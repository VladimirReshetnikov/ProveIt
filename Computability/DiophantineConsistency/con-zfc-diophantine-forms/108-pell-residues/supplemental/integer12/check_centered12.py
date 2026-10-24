#!/usr/bin/env python3
"""Exact independent translation checks and weighted degree certificates.

No bounded numerical search is used to establish the polynomial identities.
"""
import json, argparse, gzip, hashlib
from pathlib import Path
from collections import Counter
class Poly:
    def __init__(self,d=0): self.d={(0,0,0,0):d} if isinstance(d,int) and d else ({} if isinstance(d,int) else d)
    def coerce(self,o): return o if isinstance(o,Poly) else Poly(o)
    def __add__(self,o):
        o=self.coerce(o);d=dict(self.d)
        for m,c in o.d.items(): d[m]=d.get(m,0)+c
        return Poly({m:c for m,c in d.items() if c})
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,o): return self+-self.coerce(o)
    def __rsub__(self,o): return self.coerce(o)+-self
    def __mul__(self,o):
        o=self.coerce(o);d={}
        for m,c in self.d.items():
            for n,v in o.d.items():
                q=tuple(a+b for a,b in zip(m,n));d[q]=d.get(q,0)+c*v
        return Poly({m:c for m,c in d.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        if n==0:return Poly(1)
        if n==1:return self
        h=self**(n//2);return h*h*(self if n%2 else 1)

from build_centered12 import build

HERE=Path(__file__).resolve().parent
BASE=HERE

def need(b,m):
    if not b: raise ValueError(m)

class Canon:
    """Exact expression interning modulo associative/commutative + and *.
    Integer IDs are assigned to full tuple keys; no cryptographic hash equality
    is used as algebraic evidence.
    """
    def __init__(self): self.keys=[]; self.intern={}
    def put(self,key):
        if key not in self.intern:
            self.intern[key]=len(self.keys); self.keys.append(key)
        return self.intern[key]
    def op(self,tag,a,b):
        if tag in ('add','mul'):
            args=[]
            for v in (a,b):
                k=self.keys[v]
                args.extend(k[1:] if k[0]==tag else [v])
            return self.put((tag,*sorted(args)))
        return self.put((tag,a,b))
    def dag(self,p,replacement=None):
        vals=[]
        for row in p['nodes']:
            tag=row[0]
            if tag in ('add','sub','mul'): val=self.op(tag,vals[row[1]],vals[row[2]])
            elif tag=='variable' and row[1]=='n' and replacement is not None: val=replacement
            else: val=self.put(tuple(row))
            vals.append(val)
        return vals

def square_weights(t):
    a,b,c,f=t
    return [max(2*a,2*b,2*c,2*f), max(a+b,c+f), max(a+c,b+f),max(a+f,b+c)]

def norm_degree(rational):
    # Component weights already include sqrt(c), sqrt(d), sqrt(cd).
    q=[146,142,148,140] if rational else [150,142,148,108]
    first=square_weights(q)
    correction=270
    need(first[0]>correction,'strict first scalar cut')
    second=square_weights(first)
    correction2=522
    need(second[0]>correction2,'strict second scalar cut')
    f=second
    g0=max(2*f[0],2*f[2],2*f[1],2*f[3])
    g1=max(f[0]+f[2],f[1]+f[3])
    need(2*f[0]>max(2*f[2],2*f[1],2*f[3]),'first final norm strict')
    need(2*g0>2*g1,'second final norm strict')
    return dict(q=q,first=first,second=second,g0=g0,g1_weighted=g1,degree=2*g0)

def mono_mul(*xs):
    z=Counter()
    for x in xs: z.update(x)
    return z

def mono_pow(x,n): return Counter({k:v*n for k,v in x.items()})

def leading_monomial(rational):
    q=Counter({'#2':1,'#3':1,'#beta':1,'j':1})
    W=Counter({'#2':2,'#3':1,'w':1})
    Y=mono_mul(Counter({'#2':1,'v':1}),mono_pow(q,3))
    a=mono_mul(q,W,Y)
    I=Counter({'s':1,'r':1,'c':2})
    Q=mono_mul(mono_pow(a,4),mono_pow(I,2))
    S=mono_mul(Counter({'#2':10}),I,mono_pow(a,5))
    V=mono_mul(Counter({'#2':2,'T':1}),mono_pow(a,2),mono_pow(I,3))
    eta=mono_mul(Counter({'h':1}),a,Y)
    if rational:
        dd=mono_mul(Counter({'#3':7,'s':2}),mono_pow(S,2),mono_pow(eta,4))
        ans=mono_mul(Counter({'#2':16}),mono_pow(Q,16),mono_pow(S,16),mono_pow(V,16),mono_pow(dd,8))
    else:
        ans=mono_mul(mono_pow(S,32),mono_pow(Q,16),mono_pow(V,32))
    return {'monomial':{k:v for k,v in ans.items() if not k.startswith('#')},'coefficient':{k[1:]:v for k,v in ans.items() if k.startswith('#')}}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,default=BASE);args=ap.parse_args()
    out={}
    for variant,degree,ops,oldfile in [
        ('rational',2368,216,'prime_separated12_degree2400.json'),
        ('integral',2400,210,'prime_separated12_degree2912.json')]:
        filename='centered12_'+variant+str(degree)+'.json'
        newpath=HERE/'equations'/filename
        new=json.loads(newpath.read_text())
        need(new==build(variant),'delivered circuit differs from deterministic rebuild')
        bp=(newpath.parent/new['coefficient_binding']).resolve()
        binding=json.loads(bp.read_text())
        need(set(binding['payloads'])=={r[1] for r in new['nodes'] if r[0]=='coefficient'},'coefficient leaf coverage')
        for port,info in binding['payloads'].items():
            raw=gzip.decompress((bp.parent/info['file']).read_bytes())
            need(hashlib.sha256(raw).hexdigest()==info['raw_sha256'],'coefficient payload hash: '+port)
            need(len(raw)==info['raw_bytes'] and int.from_bytes(raw,'little').bit_length()==info['bits'],'coefficient payload size: '+port)
        old=json.loads((args.parent/'equations'/oldfile).read_text())
        c=Canon(); nv=c.dag(new)
        ni=c.put(('variable','n'))
        vv=nv[new['named_registers']['V']]
        if variant=='integral':
            vv=c.op('mul',nv[new['named_registers']['Q']],vv)
        ov=c.dag(old,c.op('add',ni,vv))
        need(ov[old['output']]==nv[new['output']],'exact translated polynomial mismatch')
        counts=Counter(r[0] for r in new['nodes'] if r[0] in ('add','sub','mul'))
        need(sum(counts.values())==ops,'operation count')
        need(new['exact_degree']==degree,'degree metadata')
        proof=norm_degree(variant=='rational'); need(proof['degree']==degree,'weighted degree')
        # Exact cancellation identities in the four independent cut variables.
        S,Q,V,z=[Poly({tuple(int(i==j) for i in range(4)):1}) for j in range(4)]; delta=Q-1; Cy=Q*V**2-1
        if variant=='rational':
            lhs=delta*(S*V+z)**2-S**2*Cy
            rhs=delta*z*z+2*delta*S*V*z-S*S*(V*V-1)
        else:
            lhs=(S*Q*V+z)**2-S**2*delta*Cy
            rhs=z*z+2*S*Q*V*z+S*S*(Q*V*V+delta)
        need(not (lhs-rhs).d,'central cancellation identity')
        need(sum(new['degree_certificate']['monomial'].values())==degree,'monomial degree')
        lm=leading_monomial(variant=='rational')
        need(lm['monomial']==new['degree_certificate']['monomial'],'derived leading monomial')
        need(lm['coefficient']==new['degree_certificate']['coefficient'],'derived leading coefficient')
        out[variant]={'delivered_circuit_rebuilt':True,'coefficient_payloads_checked':True,'exact_translation':True,'central_identity':True,'operations':sum(counts.values()),'counts':dict(counts),'degree_certificate':proof,'leading_monomial':new['degree_certificate']}
    print(json.dumps(out,indent=2))
    (HERE/'CENTERING_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__': main()
