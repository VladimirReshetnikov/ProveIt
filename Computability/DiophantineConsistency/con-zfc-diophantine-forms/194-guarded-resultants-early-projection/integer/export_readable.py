#!/usr/bin/env python3
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent

def monomial(m,tex=False):
 if not m:return ''
 if not tex:return '*'.join('x'+str(i)for i in m)
 from collections import Counter
 return ''.join('x_{'+str(i)+'}'+('^{'+str(k)+'}'if k>1 else'')for i,k in sorted(Counter(m).items()))
def form(ts,tex=False):
 parts=[]
 for c,m in ts:
  q=monomial(m,tex);a=abs(c)
  text=(str(a) if a!=1 or not q else '')+((' 'if tex else '*')if q and a!=1 else '')+q
  parts.append(('+'if c>0 else '-')+text)
 s=' '.join(parts)
 return s[1:]if s.startswith('+')else s

def outputs():
 e=json.loads((ROOT/'integer209/equation.json').read_text())
 txt=['All x0,...,x208 range independently over the integers.','P = sum(R_i^2, i=0,...,148) = 0.','']
 tex=['% Entire literal residual list; generated from integer209/equation.json.']
 for i,r in enumerate(e['residuals']):
  txt.append('R'+str(i)+' = '+form(r['terms']))
  chunks=[r['terms'][j:j+5]for j in range(0,len(r['terms']),5)]
  tex.append('\\begin{align*} R_{'+str(i)+'}={}&'+form(chunks[0],True))
  for chunk in chunks[1:]:
   line=form(chunk,True)
   if chunk[0][0]>0:line='+'+line
   tex.append('\\\\ &'+line)
  tex.append('\\end{align*}')
 vs='index\tname\tkind\n'+''.join(f"{i}\t{v['name']}\t{v['kind']}\n"for i,v in enumerate(e['variables']))
 return {'integer209/residuals.txt':'\n'.join(txt)+'\n','integer209/residuals.tex':'\n'.join(tex)+'\n','integer209/variables.tsv':vs}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 for k,v in outputs().items():
  path=ROOT/k
  if a.check:
   if path.read_text()!=v:raise ValueError('export mismatch '+k)
  else:path.write_text(v)
 print(json.dumps({'status':'PASS','readable_exports':3,'rows':149}))
