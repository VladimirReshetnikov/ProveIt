#!/usr/bin/env python3
"""Finite inductive sign/size invariant for a nine-register source program.
Domain bits1/2/4 mean {0}/{1}/{n:n>=2}. Checked transfer is sound for all naturals.
Run: abstract_source.py instructions.json output.json
"""
import sys,json,pathlib,hashlib,collections
if not __debug__:raise RuntimeError('Assertions required')
p=pathlib.Path(sys.argv[1]);program=json.loads(p.read_text());n=len(program)
INIT=(4,)+(1,)*8;START=25

def transfer(op,f):
 if op[0]=='inc':
  _,r,j=op;v=list(f);v[r]=(2 if f[r]&1 else 0)|(4 if f[r]&6 else 0);return [(j,tuple(v))]
 if op[0]=='dec':
  _,r,z,k=op;out=[]
  if f[r]&1:v=list(f);v[r]=1;out.append((z,tuple(v)))
  if f[r]&6:v=list(f);v[r]=(1 if f[r]&2 else 0)|(6 if f[r]&4 else 0);out.append((k,tuple(v)))
  return out
 if op[0]=='jump':return [(op[1],f)]
 if op[0]=='halt':return []
 raise ValueError(op)

facts=[None]*n;facts[START]=INIT;q=collections.deque([START]);visits=0
while q:
 i=q.popleft();f=facts[i]
 for j,v in transfer(program[i],f):
  assert 0<=j<n
  u=v if facts[j]is None else tuple(x|y for x,y in zip(v,facts[j]))
  if u!=facts[j]:facts[j]=u;q.append(j)
 visits+=1
# Independent closure check, so the worklist need not be trusted to terminate at a fixpoint.
assert all(x&~y==0 for x,y in zip(INIT,facts[START]))
for i,f in enumerate(facts):
 if f is None:continue
 assert len(f)==9 and all(1<=v<=7 for v in f)
 for j,v in transfer(program[i],f):
  assert facts[j] is not None and all(x&~y==0 for x,y in zip(v,facts[j]))
forced=[];outcomes=0
for i,(op,f)in enumerate(zip(program,facts)):
 if f is None:continue
 if op[0]=='dec':
  m=f[op[1]];outcomes+=int(bool(m&1))+int(bool(m&6))
  if not(m&1 and m&6):forced.append({'site':i,'op':op,'mask':m,'branch':'zero'if m==1 else'positive'})
 else:outcomes+=1
obj={'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'domain':{'1':'exactly zero','2':'exactly one','4':'at least two'},'start_site':START,'initial_logical_values':[2]+[0]*8,'facts':facts,'sites':n,'reachable_sites':sum(f is not None for f in facts),'unreachable_sites':[i for i,f in enumerate(facts)if f is None],'forced_decrements':forced,'admissible_outcomes':outcomes,'worklist_visits':visits,'inductive_closure_checked':True,'scope':'Natural-number source semantics; initial configuration must be supplied by the literal machine startup certificate.'}
pathlib.Path(sys.argv[2]).write_text(json.dumps(obj,indent=2)+'\n');print(json.dumps({k:v for k,v in obj.items()if k!='facts'},indent=2))
