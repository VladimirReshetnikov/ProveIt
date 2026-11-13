#!/usr/bin/env python3
"""Independent direct-qF source, actual seed and arithmetic controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-direct-qf73-probe'
P=D/'research/ordinary14-positive-guard74'
def digest(data):return hashlib.sha256(data).hexdigest()
def pinned(path,expected):
    data=path.read_bytes()
    assert digest(data)==expected,str(path)
    return data

new=json.loads(pinned(A/'candidate.json','734b2467ac242178e5d44285a573e27430748555927b0eb7121316066e2796ce'))
old=json.loads(pinned(P/'candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'))
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary14-direct-qf73-probe-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)])=='1e44c3fa529679d5d5c590dcb016a6923198060aefb85666e24750d86d2a3be1'
assert new['witnesses']==['qF' if x=='F' else x for x in old['witnesses']]
assert new['fixed_numerals']==old['fixed_numerals']
rows=[row for row in old['source'] if row[0]!='qF']
assert rows==new['source'] and len(rows)==73
assert [row for row in old['source'] if 'F' in row[2:]]==[['qF','-','q','F']]
known=set(new['witnesses']+new['fixed_numerals'])
assert len(known)==18
for name,op,a,b in rows:
    assert name not in known and op in {'+','-','*'}
    assert all(isinstance(x,int) or x in known for x in (a,b))
    known.add(name)
live={new['output']}
for name,_,a,b in reversed(rows):
    if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses']+new['fixed_numerals'])<=live

def const(n):return {():n} if n else {}
def var(name):return {(name,):1}
def add(a,b,sign=1):
    out=dict(a)
    for key,val in b.items():out[key]=out.get(key,0)+sign*val
    return {key:val for key,val in out.items() if val}
def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb));out[key]=out.get(key,0)+va*vb
    return {key:val for key,val in out.items() if val}
b,X,K,t=map(var,('b','X','K0','t'))
q=add(b,const(1));qF=add(q,mul(b,t));C=mul(const(3),b)
h=add(add(mul(const(3),add(X,K)),t),const(1))
guard=add(add(mul(C,add(X,K)),qF),mul(b,h),-1)
assert guard==const(1)
U,a,c,H,g0,k,R=map(var,('U','a','c','H','gamma0','k','R'))
ugamma=add(add(add(mul(U,g0),k),R,-1),const(1),-1)
main=add(mul(U,add(X,mul(a,c))),mul(H,add(add(ugamma,k,-1),add(R,const(1)))))
assert main==mul(U,add(add(X,mul(a,c)),mul(H,g0)))

base=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind72=json.loads(pinned(base/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
bind115=json.loads(pinned(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for name,info in bind72['ports'].items():
    assert all(bind115['ports'][name][key]==info[key] for key in ('sha256_raw','sha256_gzip'))
    compressed=(base/info['path']).read_bytes()
    assert digest(compressed)==info['sha256_gzip']
    raw=gzip.decompress(compressed)
    assert len(raw)==info['raw_bytes'] and digest(raw)==info['sha256_raw']
    ports[name]=int.from_bytes(raw,'little')
B=590069; b0=ports['beta'];q0=b0+1
assert b0==2**B-1 and ports['K0']>=0 and 0<ports['MC']<b0 and 0<ports['MF']<2*b0
AA=q0*(q0-1)*(q0*q0-1)
G0=3*b0*q0+1-2*b0
R0=G0*(q0*q0-1)+ports['MC']+q0*ports['MF']
L=R0.bit_length()+1;S=AA.bit_length()+1
t0=2+(1<<L)+(1<<(L+S))
qF0=q0+b0*t0;alpha0=1+b0*(t0-2);C0=qF0-alpha0
G=b0*qF0+alpha0
rank=G*(q0*q0-1)+ports['MC']+q0*ports['MF']
assert C0==3*b0 and q0-qF0==-b0*t0<0 and qF0>0 and alpha0>0
assert G==b0*q0*(1+t0)+1-2*b0 and G>b0*q0-1
assert rank==R0+(AA<<L)+(AA<<(L+S))
assert 0<R0.bit_length()<L and AA.bit_length()<S
assert rank%4==3 and rank.bit_length()==7080832
pop=((rank-1)//2).bit_count()
assert pop==3540414 and pop>=3*B+1 and rank>2*B
rank_sha=digest(rank.to_bytes((rank.bit_length()+7)//8,'little'))
author=json.loads((A/'result.json').read_bytes())
assert rank_sha==author['rank_sha256_little_endian']

# Small aligned-index Pell control, independent of the enormous actual seed.
def mul_pair(left,right,delta):
    a0,b0=left;c0,d0=right
    return a0*c0+delta*b0*d0,a0*d0+b0*c0
def pow_pair(base,exponent,delta):
    out=(1,0)
    while exponent:
        if exponent%2:out=mul_pair(out,base,delta)
        base=mul_pair(base,base,delta);exponent//=2
    return out
for aa in (1,2,3):
    rr=3;dd=(aa+2)**2-1
    d0,c0=pow_pair((aa+2,1),rr,dd)
    ff,L0=pow_pair((d0,c0),c0,dd)
    assert L0%(c0*c0)==0 and ff*ff-dd*L0*L0==1
    ii=dd*L0//(c0*c0);S0=dd*L0;qq=dd*(ff*ff-1)
    assert qq==S0*S0==(ii*c0*c0)**2
    chi,yy=pow_pair((S0,1),rr,S0*S0-1)
    assert chi%S0==0
    vv=chi//S0
    numerator=vv+c0+ff*ff*rr
    assert numerator%(c0*ff*ff)==0 and numerator//(c0*ff*ff)>0
    assert yy*yy-qq*(yy*yy-vv*vv)==1 and yy>0

prime=1000000009
env={name:[15*i+1,i+2] for i,name in enumerate(new['witnesses'])}
env.update({name:[value%prime] for name,value in ports.items()})
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def plus(a,b,sign):
    return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def times(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
    return trim(out)
def value(x):return [x%prime] if isinstance(x,int) else env[x]
for name,op,a,bv in rows:
    env[name]=times(value(a),value(bv)) if op=='*' else plus(value(a),value(bv),1 if op=='+' else -1)
ray=env[new['output']]
assert len(ray)-1==107 and ray[-1]!=0

run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
assert not run.stderr and run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'scope':'external symbolic zero review; no Lean/PDF theorem',
                  'operations':len(rows),'counts':dict(Counter(row[1] for row in rows)),
                  'all_live':True,'formal_guard_and_main_identities':True,'rank_bits':rank.bit_length(),
                  'rank_sha256_little_endian':rank_sha,'N_popcount':pop,'aligned_pell_controls':3,
                  'prime':prime,'weighted_ray_degree':len(ray)-1,'weighted_ray_leader':ray[-1],
                  'author_readme_prelink_sha256':digest(readme[:-len(tail)])},sort_keys=True,indent=2))
