#!/usr/bin/env python3
"""Deterministic literal transforms of frozen circuit data; no parent code runs."""
import argparse, copy, json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROFILES={
 'xy_v2':('xy','V2',77,626),'xy_bv':('xy','bV',78,464),
 'q4_v2':('q4','V2',78,622),'q4_bv':('q4','bV',79,460),
 'partial_v2':('partial','V2',79,518),'partial_bv':('partial','bV',80,384)}
def compile_one(mode,weight,ops,degree):
 p=json.loads((ROOT/'provenance'/('equation78.json' if weight=='V2' else 'equation79.json')).read_text())
 rows=[]
 for name,op,a,b in p['source']:
  if name=='Tp':continue
  if name=='cT':b='T'
  if mode=='xy':
   if name=='Y2':name='D';a='X';b='Y'
   elif name=='V0':a='D';b='Y'
   elif a=='Y2':a='D'
   elif b=='Y2':b='D'
  else:
   if mode=='partial' and name=='Y':a='q2'
   if mode=='q4' and name=='q2':
    rows.append([name,op,a,b]);rows.append(['D','*','q2','q2']);continue
   if mode=='partial' and name=='Y2':
    rows.append([name,op,a,b]);rows.append(['D','*','q3','Y']);continue
   if a=='Y2' and name!='V0':a='D'
   if b=='Y2' and name!='V0':b='D'
   if mode=='partial':
    if name=='P1e':
     rows.extend([['Y2me','-','Y2','e'],['P1e','*','bJ','Y2me']]);continue
    if name=='brk':op='-';a,b='P1e','mu2inner'
    if name=='Znum':op='+'
  rows.append([name,op,a,b])
 p.update(name=mode+'_'+weight,source=rows,operations=len(rows),operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),exact_degree=degree,proof='PROOF.md',normalization=mode,parent='provenance/'+('equation78.json' if weight=='V2' else 'equation79.json'))
 if len(rows)!=ops:raise ValueError((mode,weight,len(rows),ops))
 return p

def encoded(x):return json.dumps(x,indent=2,ensure_ascii=False)+'\n'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
 for name,args in PROFILES.items():
  text=encoded(compile_one(*args));path=ROOT/(name+'.json')
  if a.check:
   if path.read_text()!=text:raise ValueError('Rebuild mismatch: '+name)
  else:path.write_text(text)
 print('PASS: six literal circuits '+('match' if a.check else 'written'))
if __name__=='__main__':main()
