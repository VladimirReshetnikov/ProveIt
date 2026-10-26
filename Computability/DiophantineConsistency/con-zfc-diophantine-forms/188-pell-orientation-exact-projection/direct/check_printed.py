#!/usr/bin/env python3
"""Parse every printed source polynomial and unit-table entry independently."""
from pathlib import Path
import json,re,copy
ROOT=Path(__file__).resolve().parent
def must(ok,msg):
 if not ok:raise ValueError(msg)
def canonical(ts):
 p={}
 for c,m in ts:
  k=tuple(sorted(m));p[k]=p.get(k,0)+c
 return {m:c for m,c in p.items() if c}
def parse_poly(body):
 body=body.replace('&','').replace('\\quad','').replace('\\\\','');body=re.sub(r'\s+','',body)
 p={};position=0
 while position<len(body):
  s=1
  if body[position] in '+-':s=-1 if body[position]=='-' else 1;position+=1
  match=re.match(r'\d+',body[position:]);c=int(match.group()) if match else 1
  if match:position+=len(match.group())
  mon=[];gotvar=False
  while position<len(body) and body[position]=='x':
   q=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',body[position:]);must(q is not None,'bad printed variable');j=int(q.group(1));e=int(q.group(2) or 1);mon.extend([j]*e);position+=len(q.group());gotvar=True
  must(match is not None or gotvar,'unparsed mathematical token')
  key=tuple(sorted(mon));p[key]=p.get(key,0)+s*c
  must(position==len(body) or body[position] in '+-','trailing mathematical token')
 return {m:c for m,c in p.items() if c}
def check(text):
 s=json.loads((ROOT/'source206.json').read_text());f=json.loads((ROOT/'factored_pool.json').read_text());g=json.loads((ROOT/'equations/integer84_degree2097808.json').read_text())
 expected={('r',i):canonical(r['terms']) for i,r in enumerate(s['residuals'][:-1])}
 for i,b in enumerate(f['blocks']):
  for name,field in [('n','base'),('T','T'),('E','E')]:expected[name,i]=canonical(b[field])
 found={}
 for match in re.finditer(r'\\begin\{align\*\}\s*([rnTE])_\{(\d+)\}&=(.*?)\\end\{align\*\}',text,re.S):
  key=(match.group(1),int(match.group(2)));must(key not in found,'duplicate displayed polynomial');found[key]=parse_poly(match.group(3))
 must(found==expected,'printed residual or pool coefficients differ')
 table=text.split('\\begin{longtable}',1)[1].split('\\end{longtable}',1)[0];triples=[]
 for line in table.splitlines():
  if re.match(r'^\d+&\d+&-?\d+',line):
   vals=list(map(int,re.findall(r'-?\d+',line)));must(len(vals)%3==0,'printed table arity');triples.extend(tuple(vals[i:i+3]) for i in range(0,len(vals),3))
 required=[]
 for b in g['blocks']:
  if b['kind']=='definition':
   r,v=b['source_row'],b['source_variable'];c=canonical(s['residuals'][r]['terms'])[(v,)];required.append((r,v,c))
 must(triples==required,'ordered unit table mismatch')
 tail=text.split('The independent coordinate indices, in the evaluator order, are',1)[1];inds=tail.split('\\end{gather*}',1)[0];must(list(map(int,re.findall(r'\d+',inds)))==g['source_input_indices'],'printed free coordinates')
 after=tail.split('Let $J$ be the following set of retained row indices:',1)[1];rs=after.split('\\end{gather*}',1)[0];must(list(map(int,re.findall(r'\d+',rs)))==g['retained_source_rows'],'printed retained rows')
 must('r_{144}=\\sum_{i=0}^{4} n_i E_i\\prod_{\\substack{0\\leq j\\leq4\\\\j\\ne i}}T_j\n-x_{205}\\prod_{j=0}^{4}T_j.' in text,'printed final pool formula')
 return {'printed_polynomials':len(found),'unit_definitions':len(required),'free_coordinates':len(g['source_input_indices']),'retained_rows':len(g['retained_source_rows'])}
def main():
 text=(ROOT/'complete_definition.tex').read_text();r=check(text)
 bad=text.replace('r_{0}&=', 'r_{0}&=1+',1)
 try:check(bad)
 except ValueError:pass
 else:raise ValueError('printed mutation accepted')
 print(json.dumps(dict(status='PASS',negative_controls=1,**r),indent=2))
if __name__=='__main__':main()
