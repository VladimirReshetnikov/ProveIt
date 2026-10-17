#!/usr/bin/env python3
"""Verify a supplied finite invariant without running abstract interpretation.
The program is parsed from the pinned literal Coq tree. The checker verifies
initial-state inclusion and every feasible outgoing transition against the
claimed masks. It also independently recalculates the removed case list.
"""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).parent

def main():
 raw=(ROOT/'sources/Prog254.v').read_bytes()
 assert hashlib.sha256(raw).hexdigest()=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
 body=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
 tok=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
 nodes=re.findall(r'\(('+tok+r'),\s*('+tok+r')\)',body)
 leaves=[]
 def visit(node,prefix):
  kind,*number=node.split();n=int(number[0]) if number else None
  if kind=='CN':
   visit(nodes[n][0],prefix+'0');visit(nodes[n][1],prefix+'1')
  else:leaves.append((prefix,kind,n))
 visit('CN 0','');assert len(leaves)==6460
 index={p:i for i,(p,_,_) in enumerate(leaves)}
 def dispatch(p):
  node='CN 0';i=0;prefix=''
  while node.startswith('CN '):
   b=int(p[i]) if i<len(p) else 0;node=nodes[int(node[3:])][b];prefix+=str(b);i+=1
  return index[prefix]
 def advance(p):
  chars=list(p)
  while chars and chars[-1]=='1':chars.pop()
  return ''.join(chars[:-1])+'1' if chars else ''
 def strip(p,bit,count):
  chars=list(p)
  while count and chars:
   if chars.pop()==bit:count-=1
  return ''.join(chars)
 cert=json.loads((ROOT/'abstract_reachability_k2.json').read_text());k=cert['k'];assert k==2
 states=cert['inputs'];assert len(states)==len(leaves)
 for v in states:assert v is None or (len(v)==9 and all(isinstance(x,int) and 0<x<16 for x in v))
 physical=[6,7,0,2,1,8,4,3,5]
 initial=[0]*9;initial[6]=2
 mask=states[dispatch('')];assert mask is not None
 assert all((m>>n)&1 for m,n in zip(mask,initial))
 def addone(m):
  # 0 -> 1; 1 -> 2; 2 or >=3 -> >=3.
  return ((m&1)<<1)|((m&2)<<1)|(8 if m&12 else 0)
 def subone(m):
  # Called after the zero alternative is removed; >=3 -> 2 or >=3.
  return ((m&2)>>1)|((m&4)>>1)|(12 if m&8 else 0)
 removed=[];allowed=[];obligations=0
 for i,(p,op,r0) in enumerate(leaves):
  v=states[i];r=physical[r0] if op in ('CI','CD') else r0
  for branch in ['z','p'] if op=='CD' else ['-']:
   if v is None or (op=='CD' and not (v[r]&(1 if branch=='z' else 14))):removed.append([i,branch]);continue
   allowed.append([i,branch])
   if op=='CH':continue
   u=v.copy()
   if op=='CI':u[r]=addone(u[r]);dest=advance(p)
   elif op=='CD' and branch=='z':u[r]=1;dest=advance(strip(p,'0',1))
   elif op=='CD':u[r]=subone(u[r]&14);dest=advance(p)
   elif op=='CB':dest=advance(strip(p,'0',r))
   elif op=='CC':dest=strip(p,'1',r)
   else:raise AssertionError(op)
   target=states[dispatch(dest)];assert target is not None
   assert all(a&~b==0 for a,b in zip(u,target)),(i,branch,dest)
   obligations+=1
 assert removed==cert['removed'];assert allowed==cert['allowed']
 result={'program_sha256':hashlib.sha256(raw).hexdigest(),'certificate_sha256':hashlib.sha256((ROOT/'abstract_reachability_k2.json').read_bytes()).hexdigest(),
         'k':k,'states':len(states),'initial_inclusion':True,'transition_obligations_passed':obligations,'allowed_cases':len(allowed),'removed_cases':len(removed),'removed':removed,
         'scope':'Independent finite invariant verifier; elementary soundness proof is provided in optimizer findings, not a proof-assistant artifact.'}
 (ROOT/'abstract_certificate_verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
