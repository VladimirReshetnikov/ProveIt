#!/usr/bin/env python3
"""Deterministic literal residual/coordinate export; no semantic interpretation by names."""
import argparse,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def term(c,m,tex=False,first=False):
 sign='-' if c<0 else ('' if first else '+')
 a=abs(c);co='' if a==1 and m else str(a)
 if tex:
  v=''.join('x_{'+str(i)+'}'+('^{'+str(k)+'}' if k>1 else '')for i,k in sorted(Counter(m).items()))
  return sign+co+v
 return sign+co+(''if not co or not m else '*')+'*'.join('x'+str(i)+('**'+str(k)if k>1 else'')for i,k in sorted(Counter(m).items()))

def exports(eq):
 n=len(eq['variables']);txt=[f'All x0,...,x{n-1} range independently over the integers.', 'P = sum_i R_i^2 = 0. Row and coordinate indices are zero based.','']
 tex=['% Generated literally from equation.json; symbolic labels are provenance, not assumptions.',r'\allowdisplaybreaks[4]',r'\begin{align*}']
 for i,r in enumerate(eq['residuals']):
  ts=r['terms'];txt.append('R'+str(i)+' = '+' '.join(term(c,m,first=j==0)for j,(c,m)in enumerate(ts)))
  chunks=[];current=[];size=0
  for j,(c,m)in enumerate(ts):
   t=term(c,m,True,j==0);weight=3+len(str(abs(c)))+sum(3+len(str(v))for v in m)
   if current and size+weight>58:chunks.append(current);current=[];size=0
   current.append(t);size+=weight
  if current:chunks.append(current)
  for k,chunk in enumerate(chunks):
   start='R_{'+str(i)+'}={}&'if k==0 else '&'
   end=r'\\[3pt]'if k==len(chunks)-1 else r'\\'
   tex.append(start+' '.join(chunk)+end)
 tex +=[r'\end{align*}','']
 tsv=['index\tname\tkind']+[str(i)+'\t'+v['name']+'\t'+v.get('kind','')for i,v in enumerate(eq['variables'])]
 return {'residuals.txt':'\n'.join(txt)+'\n','residuals.tex':'\n'.join(tex),'variables.tsv':'\n'.join(tsv)+'\n'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 count=0
 for p in sorted(ROOT.glob('*integer*/equation.json')):
  out=exports(json.loads(p.read_text()))
  for fn,s in out.items():
   if args.check:
    if (p.parent/fn).read_text()!=s:raise ValueError('readable export mismatch '+str(p.parent/fn))
   else:(p.parent/fn).write_text(s)
  count+=1
 print(json.dumps({'status':'pass','endpoints':count,'check_only':args.check}))
if __name__=='__main__':main()
