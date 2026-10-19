#!/usr/bin/env python3
"""Independently check a finite grammar lower bound using exact rationals.

Uses only Python's standard library. No optimization package is imported.
"""
import argparse,gzip,hashlib,json
from collections import defaultdict,Counter
from fractions import Fraction as F
from pathlib import Path
if not __debug__:
 raise RuntimeError('Run this verifier with Python assertions enabled (no -O).')
P=argparse.ArgumentParser();P.add_argument('model',type=Path);P.add_argument('certificate',type=Path);P.add_argument('--witness',type=Path);P.add_argument('--inputs',type=Path,required=True);P.add_argument('--output',type=Path)
A=P.parse_args();D=json.load(gzip.open(A.model,'rt'));C=json.load(gzip.open(A.certificate,'rt'))
I=json.loads(A.inputs.read_text());assert I['zero_guard']is False and I['complements']is False
for kind,path in [('model',A.model),('certificate',A.certificate)]:
 blob=path.read_bytes();assert hashlib.sha256(blob).hexdigest()==I[kind+'_sha256']
 assert hashlib.sha256(gzip.decompress(blob)).hexdigest()==I[kind+'_uncompressed_sha256']
for inp in I['inputs'].values():assert hashlib.sha256(inp['content'].encode()).hexdigest()==inp['sha256']
base=json.loads(I['inputs']['baseline_grammar']['content']);witness=json.loads(A.witness.read_text())if A.witness else base;assert base==witness
bg={w:(l,r)for w,l,r in base['rules']};assert len(bg)==base['rules_count']
lines=I['inputs']['route_grammar']['content'].splitlines();ng,nroot,na=map(int,lines[0].split());allowed={c:int(m)for c,m in map(str.split,lines[ng+1+nroot:])};assert len(allowed)==na
boot=I['inputs']['bootstrap_lock']['content'].splitlines();assert int(boot[0])==len(boot)-1
constraints=[x.split()for x in boot[1:]];tokens=I['inputs']['route_constraints']['content'].split();at=1
for i in range(int(tokens[0])):
 s,b,w,nc=tokens[at:at+4];at+=4;route=base['routes'][i];assert(route['source'],route['read'])==(int(s),int(b));w=route['word']
 for j in range(int(nc)):
  pre,target=tokens[at:at+2];at+=2;constraints.append((w,pre,target))
frozen=set()
for w,pre,target in constraints:
 for b in pre:frozen.add(w);w=bg[w][int(b)]
 assert w==target
main=max(base['roots'],key=len);L=I['max_repeated_substring_length'];minimum=I['minimum_occurrences_in_AX']
frequency=Counter(main[i:i+k]for k in range(2,L+1)for i in range(len(main)-k+1))
universe=set(bg)|{w for w,c in frequency.items()if c>=minimum}|set(allowed)
legal=lambda l,r:(len(l)>1 or allowed[l]&1)and(len(r)>1 or allowed[r]&2)
splits={w:([(w,*bg[w])]if w in frozen else[(w,w[:k],w[k:])for k in range(1,len(w))if w[:k]in universe and w[k:]in universe and legal(w[:k],w[k:])])for w in universe if len(w)>1}
while True:
 bad={w for w,ps in splits.items()if not ps}
 if not bad:break
 for w in bad:del splits[w];universe.remove(w)
 for w in splits:splits[w]=[(w,l,r)for w,l,r in splits[w]if l not in bad and r not in bad]
expected_words=sorted(splits,key=lambda w:(len(w),w));expected_productions=[p for w in expected_words for p in splits[w]]
assert D['words']==expected_words and D['rules']==[list(p)for p in expected_productions]
words=D['words'];productions=[tuple(r)for r in D['rules']];n=len(words);nv=n+len(productions);wi={w:i for i,w in enumerate(words)};pi={r:i+n for i,r in enumerate(productions)}
assert len(wi)==n and len(pi)==len(productions)
assert D['c']==[1]*n+[0]*len(productions)
assert len(D['lower'])==len(D['upper'])==nv
assert all(x in (0,1)for x in D['lower']) and D['upper']==[1]*nv
assert D['lower'][n:]==[0]*len(productions)
forced=set(base['roots'])|{r['word']for r in base['routes']}|frozen
assert D['lower'][:n]==[int(w in forced)for w in words]
assert all(w==l+r and len(w)>1 and l and r and(len(l)==1 or l in wi)and(len(r)==1 or r in wi)for w,l,r in productions)
def sparse_rows(spec):
 rows=[defaultdict(int)for _ in range(spec['shape'][0])]
 assert spec['shape'][1]==nv
 for i,j,v in spec['entries']:
  assert type(i)is int and type(j)is int and 0<=i<len(rows) and 0<=j<nv and int(v)==v
  rows[i][j]+=int(v)
 return [{j:v for j,v in row.items()if v}for row in rows]
eq=sparse_rows(D['eq']);le=sparse_rows(D['le']);assert len(eq)==n
expected_eq=[{i:-1}for i in range(n)];expected_le=[]
for prod in productions:
 w,l,r=prod;j=pi[prod];expected_eq[wi[w]][j]=1
 for child in set((l,r)):
  if len(child)>1:expected_le.append({j:1,wi[child]:-1})
assert eq==expected_eq and D['eq_b']==[0]*n
# The generator appends one redundant cardinality bound. Since it is at least
# the entire symbol count, it imposes no restriction on binary grammars.
assert len(le)==len(expected_le)+1
canon=lambda row:tuple(sorted(row.items()))
assert sorted(map(canon,le[:-1]))==sorted(map(canon,expected_le))
assert le[-1]=={i:1 for i in range(n)} and D['le_b'][:-1]==[0]*len(expected_le)
assert D['le_b'][-1]>=n
# Positive control: the existing grammar has exactly128 rules and satisfies
# every presence bound and production restriction of this explicit universe.
wg={w:(l,r)for w,l,r in witness['rules']};assert len(wg)==witness['rules_count']
for w,lr in wg.items():
 assert(w,*lr)in pi
 assert all(len(child)==1 or child in wg for child in lr)
for i,low in enumerate(D['lower'][:n]):
 if low:assert words[i]in wg
assert C['status']=='EXACT_FINITE_UNIVERSE_LOWER_BOUND';target=C['working_grammar_lower_bound']-1
nodes=0;leaves=[]
def multipliers(rows,size,nonpositive=False):
 vals=[F(0)]*size;seen=set()
 for i,p,q in rows:
  assert i not in seen and 0<=i<size and type(p)is int and type(q)is int and q>0
  seen.add(i);vals[i]=F(p,q)
  if nonpositive:assert vals[i]<=0
 return vals
def verify(tree,lows,highs):
 global nodes
 nodes+=1;assert all(l<=h for l,h in zip(lows,highs))
 if tree['status']=='BRANCH':
  j=tree['variable'];assert 0<=j<n and lows[j]==0 and highs[j]==1 and len(tree['children'])==2
  hh=highs.copy();hh[j]=0;verify(tree['children'][0],lows,hh)
  ll=lows.copy();ll[j]=1;verify(tree['children'][1],ll,highs);return
 assert tree['status']=='EXACT_BOUND'
 cert=tree['certificate'];ye=multipliers(cert['eq_dual'],len(eq));yl=multipliers(cert['le_dual'],len(le),True);res=[F(int(x))for x in D['c']]
 for rows,dual in ((eq,ye),(le,yl)):
  for row,y in zip(rows,dual):
   if y:
    for j,v in row.items():res[j]-=y*v
 bound=sum(y*int(b)for y,b in zip(ye,D['eq_b']))+sum(y*int(b)for y,b in zip(yl,D['le_b']))+sum(r*(lows[j]if r>=0 else highs[j])for j,r in enumerate(res))
 assert bound==F(*cert['bound']) and bound>target
 leaves.append(str(bound))
verify(C['tree'],list(map(int,D['lower'])),list(map(int,D['upper'])))
assert nodes==C['nodes'] and len(leaves)==C['leaves'] and len(wg)==target+1
out=dict(status='PASS_EXACT_RATIONAL_BRANCH_CERTIFICATE',symbols=n,productions=len(productions),frozen_rules=len(frozen),forced_words=len(forced),universe_reconstructed=True,scanner_guard_used=False,model_sha256=I['model_sha256'],certificate_sha256=I['certificate_sha256'],tree_nodes=nodes,leaf_bounds=leaves,grammar_lower_bound=target+1,witness_rules=len(wg),optimizer_imported=False,scope='The explicit finite production universe and fixed presence/production restrictions; no unrestricted grammar or TM minimality claim')
print(json.dumps(out,indent=2))
if A.output:A.output.write_text(json.dumps(out,indent=2)+'\n')
