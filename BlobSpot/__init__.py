from argparse import FileType
import logging

import azure.functions as func
import fitz
from difflib import SequenceMatcher
from operator import itemgetter
import unicodedata

import regex as re
import pandas as pd
import spacy
from spacy import displacy
import ntpath
import json

def similar(a, b):
    return SequenceMatcher(None, a, b).ratio()

def fonts(doc, granularity=False):
    """Extracts fonts and their usage in PDF documents.
    :param doc: PDF document to iterate through
    :type doc: <class 'fitz.fitz.Document'>
    :param granularity: also use 'font', 'flags' and 'color' to discriminate text
    :type granularity: bool
    :rtype: [(font_size, count), (font_size, count}], dict
    :return: most used fonts sorted by count, font style information
    """
    styles = {}
    font_counts = {}

    for page in doc:
        blocks = page.get_text("dict")["blocks"]
        for b in blocks:  # iterate through the text blocks
            if b['type'] == 0:  # block contains text
                for l in b["lines"]:  # iterate through the text lines
                    for s in l["spans"]:  # iterate through the text spans
                        if granularity:
                            identifier = "{0}_{1}_{2}_{3}".format(s['size'], s['flags'], s['font'], s['color'])
                            styles[identifier] = {'size': s['size'], 'flags': s['flags'], 'font': s['font'],
                                                  'color': s['color']}
                        else:
                            identifier = "{0}".format(s['size'])
                            styles[identifier] = {'size': s['size'], 'font': s['font']}

                        font_counts[identifier] = font_counts.get(identifier, 0) + 1  # count the fonts usage

    font_counts = sorted(font_counts.items(), key=itemgetter(1), reverse=True)

    if len(font_counts) < 1:
        raise ValueError("Zero discriminating fonts found!")

    return font_counts, styles


def font_tags(font_counts, styles):
    """Returns dictionary with font sizes as keys and tags as value.
    :param font_counts: (font_size, count) for all fonts occuring in document
    :type font_counts: list
    :param styles: all styles found in the document
    :type styles: dict
    :rtype: dict
    :return: all element tags based on font-sizes
    """
    p_style = styles[font_counts[0][0]]  # get style for most used font by count (paragraph)
    p_size = p_style['size']  # get the paragraph's size

    # sorting the font sizes high to low, so that we can append the right integer to each tag
    font_sizes = []
    for (font_size, count) in font_counts:
        font_sizes.append(float(font_size))
    font_sizes.sort(reverse=True)

    # aggregating the tags for each font size
    idx = 0
    size_tag = {}
    for size in font_sizes:
        idx += 1
        if size == p_size:
            idx = 0
            size_tag[size] = '<p>'
        if size > p_size:
            size_tag[size] = '<h{0}>'.format(idx)
        elif size < p_size:
            size_tag[size] = '<s{0}>'.format(idx)

    return size_tag


def headers_para(doc, size_tag):
    """Scrapes headers & paragraphs from PDF and return texts with element tags.
    :param doc: PDF document to iterate through
    :type doc: <class 'fitz.fitz.Document'>
    :param size_tag: textual element tags for each size
    :type size_tag: dict
    :rtype: list
    :return: texts with pre-prended element tags
    """
    header_para = []  # list with headers and paragraphs
    first = True  # boolean operator for first header
    previous_s = {}  # previous span

    for page in doc:
        blocks = page.get_text("dict")["blocks"]
        for b in blocks:  # iterate through the text blocks
            if b['type'] == 0:  # this block contains text

                # REMEMBER: multiple fonts and sizes are possible IN one block

                block_string = ""  # text found in block
                for l in b["lines"]:  # iterate through the text lines
                    for s in l["spans"]:  # iterate through the text spans
                        if s['text'].strip():  # removing whitespaces:
                            if first:
                                previous_s = s
                                first = False
                                block_string = size_tag[s['size']] + s['text']
                            else:
                                if s['size'] == previous_s['size']:

                                    if block_string and all((c == "|") for c in block_string):
                                        # block_string only contains pipes
                                        block_string = size_tag[s['size']] + s['text']
                                    if block_string == "":
                                        # new block has started, so append size tag
                                        block_string = size_tag[s['size']] + s['text']
                                    else:  # in the same block, so concatenate strings
                                        block_string += " " + s['text']

                                else:
                                    header_para.append(block_string)
                                    block_string = size_tag[s['size']] + s['text']

                                previous_s = s

                    # new block started, indicating with a pipe
                    block_string += "<br>"

                header_para.append(block_string)

    return header_para

def ascii(string):
    return ''.join([i if ord(i) < 128 else ' ' for i in string])

def stripper(string):
    string = ascii(string)
    string = string.strip('|')
    string = string.strip(':')
    string = string.lstrip('<h1>')
    string = string.lstrip('<h2>')
    string = string.lstrip('<h3>')
    string = string.lstrip('<h4>')
    string = string.lstrip('<h5>')
    string = string.lstrip('<p>')
    string = string.strip('<br>')
    string = string.strip()
    string = string.strip('')
    string = string.strip('☐')
    return string


def remove_accents(input_str):
    nkfd_form = unicodedata.normalize('NFKD', str(input_str))
    only_ascii = nkfd_form.encode('ASCII', 'ignore')   
    return only_ascii.decode("utf-8")

def namechecker(query):
    length = len(query.split())
    if (length < 2) or (length > 3):
        return False
    query = query.lower()
    query = remove_accents(query)
    query = query.split()
    f = open("data\\surnames.txt", 'r', encoding='utf-8')
    for x in query:
        #print(x)
        for line in f:
            line = line.strip()
            line = line.lower()
            if line in x:
                return True
    return False

def sim_sectiondict(sectiondict, query):
    for section in sectiondict:
        for word in sectiondict[section]:
            if similar(word, query) > 0.95:
                return True
    return False


def header_dict_maker(document):

    namefound = 0
    _, tail = ntpath.split(document)
    
    # create sectiondict and headerdict from the json file included
    with open('sectiondict.json') as json_file:
        sectiondict = json.load(json_file)
    header_dict = {key: [] for key in sectiondict}
    header_dict['Bestand'] = [tail]


    # open the document and load out the elements
    doc = fitz.open(document, filetype="pdf") ### !!! document 57... wordt niet uitgelezen
    raw = []
    for page in doc:
        raw.append(page.get_text("text"))

    raw = '\n'.join(raw)
    #print(raw)


    ### NER
    # english = 0
    # if english:
    #     nlp = spacy.load("en_core_web_md") # in main do this before header_dict_maker
    # else:
    #     nlp = spacy.load("nl_core_news_lg")
    
    # doc = nlp(raw)

    # entities = []
    # labels = []

    # for ent in doc.ents:
    #     entities.append(ent)
    #     labels.append(ent.label_)
    
    # df = pd.DataFrame({'Entities':entities,'Labels':labels})
    # #print(df.loc[df['Labels'] == 'PERSON'])
    # persons = [(df.loc[df['Labels'] == 'PERSON'])]
    # if persons:
    #     for _, row in df.loc[df['Labels'] == 'PERSON'].iterrows():
    #         if not namefound:
    #             if namechecker(stripper(str(row['Entities']))):
    #                 header_dict['Naam'] = [str(df.loc[df['Labels'] == 'PERSON'].iloc[0]["Entities"]).capitalize()]
    #                 namefound = 1
    ### Einde NER


    doc = fitz.open(document, filetype="pdf")
    font_counts, styles = fonts(doc, granularity=False)
    size_tag = font_tags(font_counts, styles)
    elements = headers_para(doc, size_tag)
    # print(elements)
    # loop over the elements
    for item in elements:

        if any(x in stripper(item) for x in ['page', 'Page']):
            item = ''

        
        # check if the element is in the top 3 headers
        large_headers = ['<h1>','<h2>','<h3>']
        title = stripper(item).lower()
        #print(title)
        
        if any(x in item for x in large_headers) or (sim_sectiondict(sectiondict, title) and stripper(item).isupper()): ### check if match 95% 
            #print(title)
            sim_sectiondict(sectiondict, title)
            

            
            for section in sectiondict:
                if title not in header_dict['Andere Informatie']:
                    header_dict['Andere Informatie'].append(title)
                if title in '\t'.join(sectiondict[section]):
                    #print(item)
                    header_dict[section].append('<h2>' + title + '</h2>') # temporary
                    header_dict['Andere Informatie'].remove(title)
                    break
                else:
                    pass

        elif item not in ['','|','<br>']:
            
            try:
                header_dict[section].append(ascii(item))
            except:
                header_dict['Andere Informatie'].append(item)


        # try to extract names
        name = re.search("""(name|Name|CV|Curriculum Vitae):?\s+\K\S+\s\S+""", stripper(item))
        if name:
            header_dict['Naam'] = [name.group(0).capitalize()]
            namefound = 1
        elif not namefound:
            header_dict['Naam'] = ['Could not find name']



        # use regex to extract mail
        mail = re.search("""(?:[a-z0-9!#$%&'*+/=?^_`{|}~-]+(?:\.[a-z0-9!#$%&'*+/=?^_`{|}~-]+)*|"(?:[\x01-\x08\x0b\x0c\x0e-\x1f\x21\x23-\x5b\x5d-\x7f]|\\[\x01-\x09\x0b\x0c\x0e-\x7f])*")@(?:(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)+[a-z0-9](?:[a-z0-9-]*[a-z0-9])?|\[(?:(?:(2(5[0-5]|[0-4][0-9])|1[0-9][0-9]|[1-9]?[0-9]))\.){3}(?:(2(5[0-5]|[0-4][0-9])|1[0-9][0-9]|[1-9]?[0-9])|[a-z0-9-]*[a-z0-9]:(?:[\x01-\x08\x0b\x0c\x0e-\x1f\x21-\x5a\x53-\x7f]|\\[\x01-\x09\x0b\x0c\x0e-\x7f])+)\])""", item)
        if mail:
            header_dict['E-mail'] = [mail.group(0)]

        # use regex to extract phone numbers
        tel = re.search("""((\+)?([ 0-9]){10,19})""", stripper(item))
        tel_found = 0 
        if tel and (tel_found == 0): # tel_found werkt nog niet
            tel_found = 1
            header_dict['Telefoon'] = [tel.group(0)]

        
        # use regex to extract linkedin
        li1 = re.search("""(^https:\\/\\/[a-z]{2,3}\\.linkedin\\.com\\/.*$)""", stripper(item))
        li2 = re.search("""(http(s)?:\/\/([\w]+\.)?linkedin\.com\/in\/[A-z0-9_-]+\/?)""", stripper(item))
        if li1:
            header_dict['LinkedIn'] = [li1.group(0)]
        elif li2:
            header_dict['LinkedIn'] = [li2.group(0)]

    return header_dict






def main(myblob: func.InputStream, inputBlob: bytes, outputBlob: func.Out[bytes]):
    logging.info(f"Python blob trigger function processed blob \n"
                 f"Name: {myblob.name}\n"
                 f"Blob Size: {myblob.length} bytes")

    file = open('new.pdf', 'wb')
    file.write(inputBlob)
    fitz.open('new.pdf', filetype='pdf')

    filename = 'new.pdf'
    header_dict = header_dict_maker(filename)

    output = json.dumps(header_dict).encode("ascii")
    ### PDF back to bytes?s
    outputBlob.set((output))

