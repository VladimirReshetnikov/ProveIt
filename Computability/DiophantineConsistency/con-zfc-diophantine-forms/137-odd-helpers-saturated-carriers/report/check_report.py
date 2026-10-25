#!/usr/bin/env python3
"""Check report metric bindings and exact presentation-copy provenance.

This validates report data and source consistency, not the semantic theorems.
"""
from pathlib import Path,PurePosixPath
import hashlib,json
ROOT=Path(__file__).resolve().parent.parent

def need(ok,msg):
    if not ok:raise ValueError(msg)
def load(rel):return json.loads((ROOT/rel).read_text())
def digest(raw):return hashlib.sha256(raw).hexdigest()
def safe(rel):
    p=PurePosixPath(rel)
    need(p.as_posix()==rel and not p.is_absolute() and '..' not in p.parts and '\\' not in rel and ':' not in rel,'unsafe report path')
def table(results):
    lines=[r'\begin{center}\small',r'\begin{tabular}{lcrrr}',r'\toprule',
      r'Construction & Domain & Variables & Degree & Gates\\',r'\midrule']
    for e in results['main_endpoints']:
        domain=r'$\mathbb Z$' if e['domain']=='Z' else r'$\mathbb Z_{>0}$'
        ops='---' if e.get('live_binary_operations') is None else str(e['live_binary_operations'])
        lines.append(f"{e['table_label']} & {domain} & {e['variables']} & {e['exact_degree']} & {ops}\\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}',''])
    return '\n'.join(lines)
def main():
    results=load('RESULTS.json');rows=[]
    for e in results['main_endpoints']:
        rel=e['literal_artifact'];safe(rel);raw=(ROOT/rel).read_bytes();d=json.loads(raw)
        need(digest(raw)==e['sha256'],'endpoint hash '+rel)
        n=len(d.get('variables',d.get('witnesses',[])))
        need(n==e['variables'],'variables '+rel)
        if e.get('metrics_artifact'):
            safe(e['metrics_artifact']);m=load(e['metrics_artifact'])
            need(m['variables']==n and m['degree']==e['exact_degree'],'direct degree '+rel)
            need(len(d['residuals'])==e['residuals']==m['rows'],'residual count '+rel)
            need(m['monomials']==e['monomials'] and m['height']==e['coefficient_height'],'expansion metrics '+rel)
        else:
            need(d['exact_degree']==e['exact_degree'],'degree binding '+rel)
            need(d['operations']==e['live_binary_operations'],'operation binding '+rel)
        safe(e['proof']);need((ROOT/e['proof']).is_file(),'missing ordinary proof')
        rows.append({'artifact':rel,'sha256':e['sha256'],'variables':n,'degree':e['exact_degree'],'status':'PASS'})
    need((ROOT/'report/summary_table.tex').read_text()==table(results),'generated summary table differs')
    prov=load('report/section_copy_provenance.json');copies=[]
    for row in prov['sections']:
        for key in ['source','destination']:safe(row[key])
        src=(ROOT/row['source']).read_bytes();dst=(ROOT/row['destination']).read_bytes()
        need(digest(src)==row['source_sha256'],'producer section changed '+row['source'])
        need(digest(dst)==row['destination_sha256'],'presentation section changed '+row['destination'])
        txt=src.decode('utf-8')
        for r in row['replacements']:
            need(txt.count(r['old'])==r['expected_count'],'replacement count')
            txt=txt.replace(r['old'],r['new'])
        need(txt.encode()==dst,'unrecorded presentation change')
        copies.append(row['destination'])
    for p in (ROOT/'report').rglob('*.tex'):
        need('Results and independently reviewed endpoints are pending' not in p.read_text(),'draft placeholder '+p.name)
        need('This working scaffold must not be released' not in p.read_text(),'draft placeholder '+p.name)
    print(json.dumps({'status':'PASS','scope':'Endpoint numeric bindings, proof presence, generated table, source hashes and recorded presentation transformations. Not a new semantic or kernel theorem.','endpoints':rows,'presentation_copies':copies},indent=2))
if __name__=='__main__':main()
