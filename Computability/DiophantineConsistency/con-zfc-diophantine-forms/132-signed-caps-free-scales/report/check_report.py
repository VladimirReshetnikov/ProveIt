#!/usr/bin/env python3
"""Check report-copy equations and reported endpoint metrics without TeX execution."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent.parent
def need(x,m):
    if not x:raise ValueError(m)
def display_blocks(text):
    pattern=r'\\\[(.*?)\\\]|\\begin\{(align\*?|gather\*?|equation\*?)\}(.*?)\\end\{\2\}'
    out=[]
    for match in re.finditer(pattern,text,re.S):
        value=match.group(1) if match.group(1) is not None else match.group(3)
        value=re.sub(r'\\(?:quad|qquad)\b','',value).replace('&','')
        value=value.replace(r']\Phi_{352}',']P').replace(r']\Phi_{\rm native}',']P')
        out.append(re.sub(r'\s+','',value))
    return out
def main():
    pairs=[('alternative/section.tex','report/sections/direct.tex'),('lowdegree/section.tex','report/sections/lowdegree.tex'),('positive/section.tex','report/sections/positive.tex'),('integer/section.tex','report/sections/integer.tex'),('integer_lowops/section.tex','report/sections/integer_lowops.tex'),('report/sources/direct_full.tex','report/sections/direct_full_proof.tex')]
    receipt=[]
    for source,report in pairs:
        a=(ROOT/source).read_text();b=(ROOT/report).read_text()
        need(display_blocks(a)==display_blocks(b),'changed display mathematics: '+report)
        receipt.append({'source':source,'report':report,'display_blocks':len(display_blocks(a)),'source_sha256':hashlib.sha256(a.encode()).hexdigest(),'report_sha256':hashlib.sha256(b.encode()).hexdigest(),'display_math_identical_modulo_documented_formatting_and_output_labels':True})
    low=json.loads((ROOT/'lowdegree/equation.json').read_text());need((low['variable_count'],low['exact_degree'],low['operations'])==(15,44,111),'lowdegree metric drift')
    i=json.loads((ROOT/'integer/free_main_saturated11_sharp.json').read_text());need((i['variable_count'],i['exact_degree'],i['operations'])==(11,352,132),'integer metric drift')
    for file,degree,ops in [('native',924,109),('short',840,110)]:
        p=json.loads((ROOT/'integer_lowops'/f'product_main_guard11_{file}.json').read_text());need((p['variable_count'],p['exact_degree'],p['operations'])==(11,degree,ops),'lowops metric drift')
    for file,degree,ops in [('first',253,102),('second',252,104)]:
        p=json.loads((ROOT/'positive'/f'{file}.json').read_text());need(len(p['witnesses'])==10 and (p['exact_degree'],p['operations'])==(degree,ops),'positive metric drift')
    for folder,variables,rows,terms in [('odd_cap',352,219,9355),('signed_cap',355,220,9370)]:
        p=json.loads((ROOT/'alternative'/folder/'equation.json').read_text());x=json.loads((ROOT/'alternative'/folder/'expanded_polynomial.json').read_text())
        need((len(p['variables']),len(p['residuals']),len(x['terms']))==(variables,rows,terms),'direct counts')
        need(max(len(m) for c,m in x['terms'])==4 and max(abs(c) for c,m in x['terms'])==15020718,'direct degree/height')
    print(json.dumps({'status':'PASS','scope':'Exact displayed producer equations preserved modulo typesetting alignment/spacing and explicit final-output label disambiguation (P to Phi only in coefficient extractions); all primary report metric statements checked against literal data. Other mathematical prose has separate independent review.','equation_copies':receipt},indent=2))
if __name__=='__main__':main()
