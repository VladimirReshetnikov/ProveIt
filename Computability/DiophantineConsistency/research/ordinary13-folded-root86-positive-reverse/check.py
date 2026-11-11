#!/usr/bin/env python3
"""Graph fold and finite sign controls for the positive reverse map."""
import hashlib,itertools,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def load(rel,h):
 b=(D/rel).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
p=load('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
f=load('research/ordinary13-folded-root86-probe/candidate.json','e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540')
a=p['source']; b=f['source']; assert p['witnesses']==f['witnesses'] and p['fixed_numerals']==f['fixed_numerals'] and len(a)==88 and len(b)==86
x=[]
for row in a:
 if row[0] in ('folded_kBt','folded_g31'):continue
 if row[0]=='g32':assert row==['g32','*','M','folded_g31'];row=['g32','*','M','g31']
 x.append(row)
assert x==b
rows={z[0]:z for z in b}
for n,z in {'qm':['qm','*','J','beta'],'q':['q','+',1,'qm'],'M':['M','*','q3','qm'],'k':['k','+','eta','zeta'],'ell':['ell','*','E','kY'],'g31':['g31','+','g30','r'],'Z':['Z','-','g34','folded_q3Bt'],'A0':['A0','-','g38','g42'],'out':['out','+','sum01','sum23']}.items():assert rows[n]==z
checked=0
for b0,q3,ell,k,rho,Y,Bt in itertools.product(range(1,4),range(1,4),range(1,4),range(2,5),range(1,4),range(1,4),range(-3,1)):
 M=q3*b0;Z=M*(ell+k+rho)+Y*b0-q3*Bt
 assert Z>M*(ell+k)>0
 assert (M*(ell+k))**2-M*M*(1+ell*(ell+k))==M*M*(ell*k+k*k-1)>0
 assert Z*Z-M*M*(1+ell*(ell+k))>0;checked+=1
print(json.dumps({'parent_sha256':'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420','folded_sha256':'e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540','source_rows_88_86':True,'finite_sign_controls':checked,'scope':'one-way positive zero transfer for beta>0; no converse, Lean, or file binding'},sort_keys=True,indent=2))
