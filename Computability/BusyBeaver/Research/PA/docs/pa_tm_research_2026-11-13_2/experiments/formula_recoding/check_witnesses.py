#!/usr/bin/env python3
"""Quick exact checks of retained emitter/grammar witnesses; no optimizer run."""
import json,hashlib
from pathlib import Path
import tag_swap as T
import disequality as D
ROOT=Path(__file__).resolve().parent

def need(p,msg):
 if not p:raise ValueError(msg)
def decode(d):
 rs=d['rules'];active=set();cache={}
 def rec(q):
  if isinstance(q,list):return tuple(q)
  if q not in rs:return q
  need(q not in active,'Cyclic grammar')
  if q in cache:return cache[q]
  active.add(q);v=tuple(rec(x)for x in rs[q]);active.remove(q)
  need(len(v)==2,'Nonbinary rule');cache[q]=v;return v
 return rec(d['root'])
def flatten(t):
 return flatten(t[0])+flatten(t[1])if T.isnode(t)else[t]

def main():
 need(hashlib.sha256((ROOT/'inputs/pa196/PA196/Program.lean').read_bytes()).hexdigest()=='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872','Source hash mismatch')
 need(T.stats(T.initial)[0]==68,'Original AX node count mismatch')
 count=0
 for file,maker,best,tokens in [('tagswap_shortlist.json',T.word,73,211),('disequality_shortlist.json',D.newword,75,210)]:
  records=json.loads((ROOT/file).read_text())
  for r in records:
   t=decode(r);w=flatten(t);expected=maker(r['meta'])
   need(w==expected,'Grammar expands to wrong exact word')
   need(T.stats(t)[0]==r['n'],'Grammar node census mismatch')
   need(len(w)==tokens==r['tokens'],'Token count mismatch');count+=1
  need(min(r['n']for r in records)==best,'Best retained bound mismatch')
 base=decode(json.loads((ROOT/'disequality_base.json').read_text()))
 need(flatten(base)==D.newword((0,0,0,0,0,tuple(range(6)))),'Baseline disequality word mismatch')
 need(T.stats(base)[0]==75,'Baseline disequality grammar count mismatch')
 print(json.dumps({'status':'EXACT_WORDS_AND_GRAMMAR_COUNTS_VERIFIED','shortlist_witnesses':count,'base4_tag_swap':{'tokens':211,'best_raw_AX_nodes':73},'disequality_parity':{'tokens':210,'best_raw_AX_nodes':75},'physical_machine':'Not established'},indent=2))
if __name__=='__main__':main()
