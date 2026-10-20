#!/usr/bin/env python3
"""Emit/check explicit substitutions for the 28-node G,H -> rho8 proof.

The checker uses only finite homomorphic substitution and syntactic equality;
it does not run unification or trust the proof search's subsumption decisions.
"""
from pathlib import Path
import argparse,json
from restricted_lukasiewicz import C,canonical,nvars,rename
ROOT=Path(__file__).parent

def term(x):return tuple(map(term,x))if isinstance(x,list)else x

def substitute(t,subst):
 if isinstance(t,tuple):return substitute(t[0],subst),substitute(t[1],subst)
 return subst.get(t,t)if isinstance(t,int)else t

def witness(major,minor):
 offset=nvars(major);m=rename(minor,offset);bindings={}
 def deref(t):
  while isinstance(t,int)and t in bindings:t=bindings[t]
  return t
 def occurs(v,t):
  t=deref(t)
  return v==t if not isinstance(t,tuple)else occurs(v,t[0])or occurs(v,t[1])
 pairs=[(major[0],m)]
 while pairs:
  x,y=map(deref,pairs.pop())
  if x==y:continue
  if isinstance(y,int)and not isinstance(x,int):x,y=y,x
  if isinstance(x,int):
   assert not occurs(x,y);bindings[x]=y
  else:
   assert isinstance(x,tuple)and isinstance(y,tuple);pairs.extend(zip(x,y))
 def sub(t):
  t=deref(t)
  return(sub(t[0]),sub(t[1]))if isinstance(t,tuple)else t
 return {str(i):sub(i)for i in range(offset)},{str(i):sub(i+offset)for i in range(nvars(minor))}

def verify(receipt):
 a,b,c=0,1,2
 allowed={canonical(C(C(C(a,b),a),C(c,a))),canonical(C(C(a,b),C(C(b,c),C(a,c))))}
 nodes=receipt['derivations']
 for i,d in enumerate(nodes):
  t=term(d['term']);p=d['proof']
  if p=='axiom':assert t in allowed;continue
  j,k=p;assert 0<=j<i and 0<=k<i
  submajor={int(x):term(y)for x,y in d['major_substitution'].items()}
  subminor={int(x):term(y)for x,y in d['minor_substitution'].items()}
  major=substitute(term(nodes[j]['term']),submajor);minor=substitute(term(nodes[k]['term']),subminor)
  assert isinstance(major,tuple)and major[0]==minor
  assert canonical(major[1])==t
 native=canonical(C(C(C(c,3),a),C(C(a,c),C(b,c))))
 assert term(nodes[receipt['found']['L']]['term'])==native
 return dict(status='PASS',axioms=2,nodes=len(nodes),detachments=len(nodes)-2,native_rho8_node=receipt['found']['L'])

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
 if args.verify_only:
  receipt=json.loads((ROOT/'gh_to_l_explicit_certificate.json').read_text())
  print(json.dumps(verify(receipt)));raise SystemExit(0)
 receipt=json.loads((ROOT/'gh_to_l_certificate.json').read_text())
 for i,d in enumerate(receipt['derivations']):
  p=d['proof']
  if p=='axiom':continue
  d['major_substitution'],d['minor_substitution']=witness(term(receipt['derivations'][p[0]]['term']),term(receipt['derivations'][p[1]]['term']))
 result=verify(receipt)
 (ROOT/'gh_to_l_explicit_certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
 (ROOT/'gh_to_l_audit.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))
