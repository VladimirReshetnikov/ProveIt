#!/usr/bin/env python3
"""Owned literal macro inventory, external-entry guards and finite diagnostics."""
from pathlib import Path
import collections,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1];D=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=ROOT/'latest218_baseline/candidate-k218/sites218.json';sites=json.loads(p.read_text());t=A.P.tree(sites)
facts=json.loads((ROOT/'research218_source/invariant_facts.json').read_text());index={s[0]:i for i,s in enumerate(sites)};cfg=A.continuation_cfg(t);pred=collections.defaultdict(list)
for i,(_,_,targets)in enumerate(cfg):
 for which,j in enumerate(targets):pred[j].append((i,which))
old_pair=A.at(t,'11010010010000110');old_u8=A.at(t,'1000');old_u2=(('CD',2),old_u8[1])
def I(r):return('CI',r)
def Dec(r):return('CD',r)
def C(k):return('CC',k)
def transfer(a,b):return(Dec(a),(I(b),C(2)))
def double(a,b):return(Dec(a),(I(b),(I(b),C(3))))
new_pair=(double(1,7),(Dec(6),(double(7,1),((I(7),(Dec(1),C(2))),C(3)))))
def unpair(r):return(Dec(r),((Dec(r),(I(7),C(3))),(I(6),(transfer(7,r),C(4)))))
new_u8=unpair(8);new_u2=unpair(2)
def image(mask,delta):
 out=0
 for atom in range(10):
  if mask>>atom&1:
   for n in([atom]if atom<8 else[atom,atom+2]):
    if n+delta>=0:
     v=n+delta;out|=1<<(v if v<8 else 8+v%2)
 return out
inventory=[]
for name,old,new in[('pair',old_pair,new_pair),('unpair8',old_u8,new_u8),('unpair2',old_u2,new_u2)]:
 hits=[]
 def walk(n,path=''):
  if n==old:
   flat=A.flatten(n,path);first=index[flat[0][0]];end=first+len(flat);edges=[]
   for i,which in pred[first]:
    if first<=i<end:continue
    out=facts[i].copy();op,arg,_=cfg[i]
    if op=='CD':
     mask=out[arg]&(~1 if which else 1)
     if not mask:continue
     out[arg]=image(mask,-1)if which else 1
    elif op=='CI':out[arg]=image(out[arg],1)
    assert out[7]==1 and(name=='pair'or out[6]==1),(name,first,i,out)
    edges.append(dict(predecessor=i,guard=which,register6_mask=out[6],register7_mask=out[7]))
   hits.append(dict(first=first,end=end,path=path,external_entry_edges=edges));return
  if not A.P.leaf(n):walk(n[0],path+'0');walk(n[1],path+'1')
 walk(t)
 inventory.append(dict(name=name,old_ast=old,new_ast=new,old_leaves=len(A.flatten(old)),new_leaves=len(A.flatten(new)),occurrences=len(hits),entries=hits,old_boundary=A.boundary(old),new_boundary=A.boundary(new)))
# Owned direct semantics diagnostic. This is not the all-natural proof.
def execute(t,regs,limit):
 steps=0
 def go(n):
  nonlocal steps
  if A.P.leaf(n):
   steps+=1
   assert steps<=limit,'diagnostic fuel'
   op,a=n
   if op=='CI':regs[a]+=1;return('normal',0)
   if op=='CD':
    if regs[a]:regs[a]-=1;return('normal',0)
    return('break',1)
   if op=='CC':return('continue',a)
   if op=='CB':return('break',a)
   return('halt',0)
  while True:
   kind,k=go(n[0])
   if kind=='break':return('normal',0)if k==1 else('break',k-1)
   if kind!='normal':return(kind,k)
   kind,k=go(n[1])
   if kind=='continue':
    if k==1:continue
    return('continue',k-1)
   return(kind,k)
 return go(t),steps
checks=[]
for name,m in[('pair',new_pair),('unpair8',new_u8),('unpair2',new_u2)]:
 count=steps=0
 params=[(a,b)for a in range(9)for b in range(17)]if name=='pair'else range(2049)
 for param in params:
  regs=[11,12,13,14,15,16,17,18,19]
  if name=='pair':
   a,b=param;regs[1]=b;regs[6]=a;regs[7]=0;target=regs.copy();target[1]=target[6]=0;target[7]=(1<<a)*(2*b+1)-1
  else:
   r=8 if name=='unpair8'else 2;regs[r]=param;regs[6]=regs[7]=0;target=regs.copy();x=param+1;a=0
   while x%2==0:x//=2;a+=1
   target[r]=0;target[6]=a;target[7]=(x-1)//2
  control,n=execute(m,regs,2_000_000);assert control==('normal',0)and regs==target,(name,param,control,regs,target)
  count+=1;steps+=n
 checks.append(dict(name=name,cases=count,steps=steps))
result=dict(status='EXACT_MACRO_INVENTORY_AND_OLD_SOURCE_ENTRY_GUARDS_PASS',source_sha256=H(p),invariant_facts_sha256=H(ROOT/'research218_source/invariant_facts.json'),inventory=inventory,finite_diagnostics=checks,scope='External-entry guards are proved for the old source using its separately checked inductive invariant. They are not automatically transported through a changed codec. New macro arithmetic is proved in MACRO_CONTRACTS.md. The new-source zero-flow obligation is discharged separately by ZERO_FLOW_PROOF.json; compiler/runtime/calibration obligations remain separate.')
(D/'MACRO_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n');print([(r['name'],r['occurrences'],r['old_leaves'],r['new_leaves'])for r in inventory]);print(checks)
