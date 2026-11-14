"""Rename selector parameters independently in unrestricted logical axiom rows.
This preserves the axiom sets exactly (bijective parameter permutations), not
merely their truth values. Each source candidate still needs compilation.
"""
import sys,json,itertools,random,math,time
from pathlib import Path
from paths import INPUTS,OUT
import model as e
s,sp=e.s,e.sp
old=e.old;word=json.loads((INPUTS/'axiom_tokens.json').read_text())
regions=[('G',478,887),('rho6',887,1170),('rho5',1170,1466),('rho4',1466,1765),('rho3',1765,2061),('rho2',2061,2411),('rho1',2411,2642)]
perms=list(itertools.permutations('abc'))
# Tokenized replacements are all exact closed variable macro subtrees.
regions_vars=[]
for name,lo,hi in regions:
 chunks=[(a,b,t)for a,b,t in word if lo<=a<b<=hi and t in'abc' and len(t)==1]
 regions_vars.append(chunks)
for chunks in regions_vars:
 for a,b,t in chunks:assert sp.closed_forest(old,a,b)==[e.macros[t]]
# Encode primitive trees as IDs, reusing the fast interned representation.
root_id=e.intern(old);macro_id={k:e.intern(v)for k,v in e.macros.items()}
# All seven intervals stay source-isomorphic at every parameter permutation.
# Record the exact paths to each variable macro root.
starts={p:i for i,(p,o,a)in enumerate(s.sites(old))}
byinterval={}
def intervals(n,p='',lo=0):
 hi=lo+sp.size(n);byinterval[lo,hi]=p
 if not s.leaf(n):intervals(n[0],p+'0',lo);intervals(n[1],p+'1',lo+sp.size(n[0]))
intervals(old)
choices=[]
for chunks in regions_vars:
 row=[]
 for perm in perms:
  rename=dict(zip('abc',perm));row.append({byinterval[a,b]:macro_id[rename[t]]for a,b,t in chunks})
 choices.append(row)

def make(combo):
 edits={p:v for i,pi in enumerate(combo)for p,v in choices[i][pi].items()}
 prefixes={p[:j]for p in edits for j in range(len(p))}
 def visit(k,p=''):
  if p in edits:return edits[p]
  if p not in prefixes:return k
  a,b=e.nodes[k];return e.pair(visit(a,p+'0'),visit(b,p+'1'))
 return visit(root_id)
from functools import lru_cache
@lru_cache(None)
def nodeset(k):
 n=e.nodes[k]
 return frozenset({k})if isinstance(n[0],str)else(frozenset({k})|nodeset(n[0])|nodeset(n[1]))
def score(combo):
 n=make(combo);return len(nodeset(n)),n
