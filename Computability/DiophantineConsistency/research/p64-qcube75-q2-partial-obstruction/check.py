#!/usr/bin/env python3
"""Exact first/main/transport obstruction; strong norm has symbolic witness."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def require(b, s):
    if not b: raise RuntimeError(s)
def mul(u,v,d):
    x,y=u; z,w=v
    return x*z+d*y*w,x*w+y*z
def power(base,e,d):
    out=(1,0)
    while e:
        if e&1:out=mul(out,base,d)
        e//=2
        if e:base=mul(base,base,d)
    return out
def digest(v):return hashlib.sha256(v.to_bytes(max(1,(v.bit_length()+7)//8),'big')).hexdigest()
q=4;Y=96;X=128;U=Y*Y;a=Y*(X+1);n=a+2;H=4*a+3;D=n*n-1;P=X*Y*Y
(t,k)=power((2*P+1,2),212,P*(P+1))
(g,c)=power((n,1),322,D)
require(Y*k<c<(Y+1)*k, 'eta/zeta positivity')
require(U*(g-X-a*c)%H==0, 'rank quotient')
A=U*(g-X-a*c)//H; B=k-1+A; R=B-U
ports={'beta':3,'K0':3,'MC':R-150,'MF':0}
inputs={'J':1,'F':1,'alpha':1,'z':23,'s':6,'w':32,'t':t,'eta':c-Y*k,'zeta':(Y+1)*k-c,'gamma':1}
require(all(v>=0 for v in ports.values()),'port signs')
require(all(v>0 for v in inputs.values()),'input signs')
require(Y%q**2==0 and Y%q**3!=0,'Y divisibility')
require(g*g-D*c*c==1,'main Pell')
# Execute generated graph gates through transport with only Y := q2*s.
graph_path=Path(__file__).resolve().parent.parent/'p64-qcube76-independent-y-candidate'/'graph.json'
b=graph_path.read_bytes()
require(hashlib.sha256(b).hexdigest()=='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c','graph pin')
gates=json.loads(b)['source'];require(['q3','*','q2','q'] in gates,'q3 gate')
require(['Y','*','q3','s'] in gates,'Y gate')
v=dict(ports,**inputs)
for row in gates:
 name,op,l,r=row
 if name=='q3':continue
 if name=='Y': l='q2'
 require(name not in v and op in ('+','-','*'),'unexpected gate')
 x=v[l] if isinstance(l,str) else l; y=v[r] if isinstance(r,str) else r
 v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 if name=='Lt':break
require(v['q']==q and v['Y']==Y and v['R']==R and v['c']==c,'coordinate mapping')
require(v['A0']==1 and v['M']==0 and v['Lt']==0,'residual mismatch')
require(c.bit_length()==4686 and max(abs(x).bit_length() for x in v.values())<10000,'size limit')
result={'status':'PASS_PARTIAL_ONLY','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'graph_sha256':hashlib.sha256(b).hexdigest(),'q':q,'Y':Y,'Y_mod_q_cubed':Y%q**3,
 'pell_exponents':{'first':212,'main':322},'A0':1,'M':0,'Lt':0,
 'ports':{'beta':3,'K0':3,'MF':0,'MC':'R-150 as defined in README and check.py',
          'MC_bits':ports['MC'].bit_length(),'MC_sha256_unsigned_big_endian':digest(ports['MC'])},
 'c_bits':c.bit_length(),'c_sha256_unsigned_big_endian':digest(c),'k_sha256_unsigned_big_endian':digest(k),
 'strong_norm':'symbolic Pell witness described in README, not expanded or checked by this script',
 'scope':'Partial first/main/transport constraints at specified natural ports; no auxiliary-unit zero, original-graph nonexistence, fixed-compact44, or existence-equivalence claim.'}
print(json.dumps(result,indent=2,sort_keys=True))
