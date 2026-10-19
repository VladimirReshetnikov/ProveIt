#!/usr/bin/env python3
"""Reuse-biased parses for certified commuting AX variants, discovery only."""
from pathlib import Path
from functools import cache
import json,argparse,time

p=argparse.ArgumentParser();p.add_argument('--variants');p.add_argument('--output',default='commuting-parse-search.json');args=p.parse_args()
base=Path(__file__).resolve().parent
g=json.loads((base/'grammar245.json').read_text());enc=json.loads((base/'fine_encoding.json').read_text());fm=enc['atom_expansions'];ex=lambda w:''.join(fm[c]for c in w)
old={ex(w):(ex(a),ex(b))for w,a,b in g['rules']};original=max(old,key=len)
allowed={}
lines=(base/'fine-route-grammar.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split())
for row in lines[n+nr+1:]:
 if row.strip():w,b=row.split();allowed[w]=int(b)
fixedroots={ex(w)for w in g['roots']}|{ex(r['word'])for r in g['routes']};fixedroots.remove(original)
@cache
def closure(w):
 return frozenset()if w in allowed else frozenset({w})|closure(old[w][0])|closure(old[w][1])
free=set().union(*(closure(w)for w in fixedroots))
dictionary=(set(old)-{original})|set(allowed)
index={}
for w in dictionary:index.setdefault(w[0],[]).append(w)
for v in index.values():v.sort(key=lambda w:-len(w))
weights={w:len(closure(w)-free)for w in dictionary}
fi=json.loads((base/'trace_collisions.json').read_text())['token_info']
ind=lambda a,b:a!=b and not(fi[a][0]&fi[b][0])and not fi[a][1]and not fi[b][1]
variants=[dict(word=original,kind='control',position=None)]
variants += [dict(word=original[:i]+original[i+1]+original[i]+original[i+2:],kind='one_commutation',position=i)for i in range(len(original)-1)if ind(original[i],original[i+1])]
if args.variants:
 data=json.loads(Path(args.variants).read_text())
 for i,v in enumerate(data['variants']):variants.append(dict(word=v['word'],kind='canonical_rank',position=i))
def parse(word,weight):
 n=len(word);dp=[float('inf')]*(n+1);dp[n]=0;selected=[None]*n
 for i in range(n-1,-1,-1):
  for w in index.get(word[i],[]):
   j=i+len(w)
   if j>n or not word.startswith(w,i):continue
   if w in allowed and ((i==0 and not allowed[w]&1)or(j==n and not allowed[w]&2)):continue
   cost=1+weight*weights[w]+dp[j]
   if cost<dp[i]-1e-9:dp[i]=cost;selected[i]=w
 if selected[0]is None:return None
 pieces=[];i=0
 while i<n:w=selected[i];pieces.append(w);i+=len(w)
 return pieces
def compile_pieces(pieces):
 rules=dict(old);rules.pop(original)
 @cache
 def build(i,j):
  w=''.join(pieces[i:j])
  if i+1==j or w in old and w!=original:return w
  cuts=[]
  for k in range(i+1,j):
   if k==i+1 and pieces[i]in allowed and not allowed[pieces[i]]&1:continue
   if k==j-1 and pieces[k]in allowed and not allowed[pieces[k]]&2:continue
   if k>i+1 and pieces[k-1]in allowed and not allowed[pieces[k-1]]&2:continue
   if j>k+1 and pieces[k]in allowed and not allowed[pieces[k]]&1:continue
   cuts.append(k)
  assert cuts,(i,j,pieces[i:j])
  k=min(cuts,key=lambda k:abs((j-k)-(k-i)))
  a,b=build(i,k),build(k,j);rules[w]=(a,b);return w
 root=build(0,len(pieces));live=set()
 def walk(w):
  if w in allowed or w in live:return
  live.add(w);a,b=rules[w];walk(a);walk(b)
 for w in fixedroots|{root}:walk(w)
 return {w:rules[w]for w in live},root
best=None;records=[];t=time.monotonic()
for v in variants:
 for weight in [0,.025,.05,.1,.2,.4,.8,1.6,3.2]:
  pieces=parse(v['word'],weight)
  if pieces is None:continue
  rules,root=compile_pieces(pieces);count=len(rules)
  records.append(dict(kind=v['kind'],position=v['position'],weight=weight,count=count,pieces=len(pieces)))
  if best is None or count<best['rules_count']:
   best=dict(status='SOURCE_WORD_CANDIDATE_ONLY',rules_count=count,rules=[[w,a,b]for w,(a,b)in sorted(rules.items())],roots=sorted(fixedroots|{root}),routes=[dict(r,word=ex(r['word']))for r in g['routes']],root_word_overrides={'76':root},properties=[],framework_states=118,erase177=True,retarget=-2,discovery=records[-1],word=root)
   print('BEST',count,records[-1],flush=True)
   (base/args.output).write_text(json.dumps(dict(best=best,records=records,free_closure=len(free),seconds=time.monotonic()-t),indent=2)+'\n')
(base/args.output).write_text(json.dumps(dict(best=best,records=records,free_closure=len(free),seconds=time.monotonic()-t),indent=2)+'\n')
print('DONE',len(records),'best',best['rules_count'],'seconds',time.monotonic()-t,flush=True)
