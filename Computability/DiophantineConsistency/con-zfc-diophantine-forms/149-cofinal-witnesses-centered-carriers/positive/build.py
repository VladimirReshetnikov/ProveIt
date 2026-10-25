#!/usr/bin/env python3
"""Compile four finite polynomial DAGs; inherited source is read as JSON only."""
import argparse, copy, hashlib, json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROFILES={'q2_v2':('q2','V2',78,516),'q2_bv':('q2','bV',79,382),
          'q1_v2':('q1','V2',79,456),'q1_bv':('q1','bV',80,338)}
def compile_one(mode,weight,ops,degree):
 path=ROOT/'provenance'/'centered'/('equation_q4_'+weight+'.json')
 p=json.loads(path.read_text());rows=[]
 for name,op,a,b in p['source']:
  if name=='q3':continue
  if name=='Y':a='q2' if mode=='q2' else 'q'
  if name=='X' and mode=='q1':
   rows.append(['Wbase','*','q','w']);a,b='q','Wbase'
  if name=='K0w' and mode=='q1':b='Wbase'
  if name=='q4':
   rows.append([name,op,a,b]);rows.append(['D','*','q4','q' if mode=='q2' else 'q2']);continue
  if name=='P1e':
   rows.extend([['shift','*','s','q4'],['eclear','-','e','shift']]);b='eclear'
  if name not in ['q4','D','shift']:
   if a=='q4':a='D'
   if b=='q4':b='D'
  rows.append([name,op,a,b])
 p.update(name=mode+'_'+weight,source=rows,operations=len(rows),
          operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),exact_degree=degree,
          normalization=mode,denominator='q5' if mode=='q2' else 'q6',proof='PROOF.md',
          parent={'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},
          generation='Centered arithmetic sharing, partial quotient normalization, and projection-before-full-denominator recovery.')
 if len(rows)!=ops:raise ValueError((mode,weight,len(rows),ops))
 return p

def encoded(x):return json.dumps(x,indent=2,ensure_ascii=False)+'\n'
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
 for name,args in PROFILES.items():
  data=encoded(compile_one(*args));path=ROOT/(name+'.json')
  if a.check:
   if path.read_text()!=data:raise ValueError('Rebuild mismatch: '+name)
  else:path.write_text(data)
 print('PASS: four literal circuits '+('match' if a.check else 'written'))
if __name__=='__main__':main()
