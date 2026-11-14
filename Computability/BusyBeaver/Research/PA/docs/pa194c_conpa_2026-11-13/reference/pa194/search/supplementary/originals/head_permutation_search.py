#!/usr/bin/env python3
"""Bounded search over order of the seven unconditional emitted heads."""
import sys,itertools,json,time,collections
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'deliverable/pa195_new_designs/construction'
sys.path.insert(0,str(BASE))
import compiler as c
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
savedrows,savedlabels=c.machine();c.machine=lambda:(savedrows,savedlabels)

def expand(t):
 if t=='node60':return inc,inc
 if t=='node61':return (inc,inc),(inc,inc)
 return tuple(map(expand,t))if c.isnode(t)else t
def word(t):return word(t[0])+word(t[1])if c.isnode(t)else[t]
def instantiate(shape,w):
 it=iter(w)
 def rec(x):return tuple(map(rec,x))if c.isnode(x)else next(it)
 t=rec(shape)
 try:next(it);raise AssertionError('leftover word')
 except StopIteration:return t
def encode(t):
 rules={};index={}
 def rec(x):
  if not c.isnode(x):return x
  if x in index:return index[x]
  children=[rec(y)for y in x];q='g'+str(len(rules));rules[q]=children;index[x]=q;return q
 root=rec(t);return{'root':root,'rules':rules}
def main():
 start=time.time();stats=[]
 for family in ['195S','195X']:
  base=expand(c.read_grammar(BASE/'source'/f'{family}.grammar.json'));w=word(base)
  assert len(w)==190
  cuts=[18,35,54,70,86,102,121,128]
  heads=[w[a:b]for a,b in zip(cuts,cuts[1:])]
  hist=collections.Counter();best=999;small=[]
  for perm in itertools.permutations(range(7)):
   ww=w[:18]+sum((heads[i]for i in perm),[])+w[128:]
   t=instantiate(base,ww);rows,index,shape=c.build(t);n=len(shape)
   if n>120:hist[f'raw{n}']+=1;continue
   ops=c.opportunities_fast(rows,shape);f=len(c.max_matching(ops));score=134+n-f;hist[f'score{score}']+=1
   if score<best:
    best=score;print(family,'best',score,'raw',n,'folds',f,'perm',perm,'seconds',time.time()-start,flush=True)
   if score<195:
    name=f'{family}_{len(small)}';(ROOT/f'head_{name}.grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
    small.append({'name':name,'permutation':perm,'raw':n,'matching':f,'score':score})
  stats.append({'family':family,'count':5040,'best_matching_bound':best,'histogram':hist,'candidates':small})
 (ROOT/'head_permutation_results.json').write_text(json.dumps({'seconds':time.time()-start,'results':stats},indent=2)+'\n')
 print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
