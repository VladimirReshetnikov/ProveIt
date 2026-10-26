#!/usr/bin/env python3
"""Independently parse the printed polynomial rows and pivot table."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def demand(c,m):
 if not c:raise ValueError(m)

def parse_polynomial(s):
 s=re.sub(r'\s+','',s)
 tokens=re.findall(r'([+-]?)([^+-]+)',s)
 demand(''.join(a+b for a,b in tokens)==s,'term-tokenization mismatch')
 terms={}
 pattern=re.compile(r'v_\{([0-9]+)\}(?:\^\{([0-9]+)\})?')
 for sign,body in tokens:
  m=re.match(r'[0-9]+',body)
  coefficient=int(m.group()) if m else 1
  remaining=body[m.end():] if m else body
  variables=[];offset=0
  for f in pattern.finditer(remaining):
   demand(f.start()==offset,'unparsed polynomial text')
   variables.extend([int(f.group(1))]*int(f.group(2) or 1));offset=f.end()
  demand(offset==len(remaining),'unparsed factor')
  if sign=='-':coefficient=-coefficient
  key=tuple(sorted(variables));demand(key not in terms,'uncollected printed term')
  terms[key]=coefficient
 return terms

def main():
 source=json.loads((ROOT/'principal92/sources/source191.json').read_text())
 rows={};current=None;body=''
 text=(ROOT/'report/source191_residuals.tex').read_text()
 for line in text.splitlines():
  start=re.match(r'S_\{([0-9]+)\}=\{\}&(.*)',line)
  if start:
   if current is not None:rows[current]=parse_polynomial(body)
   current=int(start.group(1));body=start.group(2).replace('\\\\','')
  elif line.startswith('&{}'):
   demand(current is not None,'continuation without residual')
   body+=line[3:].replace('\\\\','')
 if current is not None:rows[current]=parse_polynomial(body)
 demand(set(rows)==set(range(len(source['residuals']))),'printed residual index set differs')
 for i,row in enumerate(source['residuals']):
  demand(rows[i]=={tuple(m):c for c,m in row['terms']},'printed coefficient mismatch '+str(i))
 cert=json.loads((ROOT/'principal92/projection92.json').read_text())
 table=(ROOT/'report/factored92_definition.tex').read_text()
 triples=[]
 for line in table.splitlines():
  if re.match(r'^[0-9]+&[0-9]+&-?1&',line) or re.match(r'^[0-9]+&[0-9]+&-?1\\',line):
   cells=line.replace('\\\\','').split('&')
   for i in range(0,len(cells),3):
    if cells[i]:triples.append(tuple(map(int,cells[i:i+3])))
 expected={(s['row'],s['variable'],s['coefficient']) for s in cert['steps']}
 demand(len(triples)==len(expected)==99 and set(triples)==expected,'printed pivot table differs')
 alive=set(cert['free_source_variables'])
 definitions={s['variable']:s for s in cert['steps']}
 for _,v,_ in triples:
  used={j for _,m in definitions[v]['restoration_source_terms'] for j in m}
  demand(used<=alive,'printed dependency order is not acyclic');alive.add(v)
 standalone=(ROOT/'ConZFC_Exact_Contractions.tex').read_text()
 demand(text in standalone and table in standalone,'standalone source omits equation data')
 result={'status':'pass','literal_residuals_parsed':len(rows),
         'coefficients_parsed':sum(map(len,rows.values())),
         'unit_definitions_parsed':len(triples),'topological_order_checked':True,
         'standalone_contains_complete_definition':True}
 (ROOT/'verification/PRINTED_EQUATION_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))

if __name__=='__main__':main()
