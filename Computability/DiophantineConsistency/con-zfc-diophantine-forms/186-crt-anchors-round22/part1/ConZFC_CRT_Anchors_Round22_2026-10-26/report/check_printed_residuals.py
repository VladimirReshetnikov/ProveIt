#!/usr/bin/env python3
"""Independently parse every displayed TeX term against the literal source."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--equation',type=Path,required=True);p.add_argument('--tex',type=Path,default=Path(__file__).with_name('residuals.tex'));p.add_argument('--output',type=Path);a=p.parse_args()
s=a.tex.read_text();rows={};current=None
for line in s.splitlines():
 m=re.match(r'R_\{(\d+)\}&=(.*)\\\\$',line)
 if m:current=int(m[1]);body=m[2];rows[current]={}
 elif line.startswith(r'&\quad{}') and line.endswith(r'\\'):
  if current is None:raise ValueError('orphan continuation')
  body=line[len(r'&\quad{}'):-2]
 else:continue
 pos=0
 while pos<len(body):
  m=re.match(r'([+-]?)(\d*)((?:x_\{\d+\}(?:\^\{\d+\})?)*)',body[pos:])
  if not m or not m.group(0) or (not m[2] and not m[3]):raise ValueError('unparsed term '+body[pos:])
  sign=-1 if m[1]=='-'else 1;coeff=sign*int(m[2]or'1');indices=[]
  for v,e in re.findall(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',m[3]):indices.extend([int(v)]*int(e or'1'))
  key=tuple(sorted(indices));rows[current][key]=rows[current].get(key,0)+coeff;pos+=len(m[0])
d=json.loads(a.equation.read_text())
if set(rows)!=set(range(len(d['residuals']))):raise ValueError('row census')
for j,r in enumerate(d['residuals']):
 expected={}
 for c,ids in r['terms']:
  key=tuple(sorted(ids));expected[key]=expected.get(key,0)+c
 if rows[j]!={k:v for k,v in expected.items()if v}:raise ValueError('coefficient mismatch in row '+str(j))
n=len(d['variables'])
if f'x_0,\\ldots,x_{{{n-1}}}\\in\\Z'not in s:raise ValueError('domain/dimension header')
result={'status':'PASS','rows':len(rows),'terms':sum(len(r)for r in rows.values()),'variables':n,'domain':'Z','equation_sha256':hashlib.sha256(a.equation.read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256(a.tex.read_bytes()).hexdigest(),'method':'Independent complete coefficient parser; no producer import'}
t=json.dumps(result,indent=2)+'\n'
if a.output:a.output.write_text(t)
print(t,end='')
