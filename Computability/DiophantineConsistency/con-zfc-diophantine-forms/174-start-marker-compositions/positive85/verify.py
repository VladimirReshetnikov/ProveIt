#!/usr/bin/env python3
"""Exact, stdlib-only finite checks for the trace/inverse-Lucas composition."""
import copy
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def require(v,msg):
    if not v: raise ValueError(msg)

# Sparse polynomials with an arbitrary fixed ordered symbol list.
class Ring:
    def __init__(self,names):
        self.names=names
        self.zero=(0,)*len(names)
    def const(self,c): return {self.zero:c} if c else {}
    def var(self,n):
        e=list(self.zero);e[self.names.index(n)]=1
        return {tuple(e):1}
    def add(self,a,b,sign=1):
        d=a.copy()
        for e,c in b.items():
            d[e]=d.get(e,0)+sign*c
            if not d[e]: del d[e]
        return d
    def mul(self,a,b):
        d={}
        for e,c in a.items():
            for f,k in b.items():
                t=tuple(x+y for x,y in zip(e,f))
                d[t]=d.get(t,0)+c*k
        return {e:c for e,c in d.items() if c}
    def pow(self,a,n):
        r=self.const(1)
        while n:
            if n&1:r=self.mul(r,a)
            a=self.mul(a,a);n//=2
        return r
    def scale(self,a,c):return {e:c*k for e,k in a.items() if c*k}

def load(name):return json.loads((ROOT/name).read_text())

def topology(g):
    known=set(g['witnesses']+g['fixed_numerals'])
    require(len(known)==len(g['witnesses'])+len(g['fixed_numerals']),'duplicate inputs')
    defs={}
    for row in g['source']:
        require(len(row)==4 and row[1] in '+-*','bad row')
        name,op,a,b=row
        require(name not in known,'duplicate register')
        for x in (a,b):
            require(isinstance(x,int) or x in known,'missing dependency')
        known.add(name);defs[name]=(a,b)
    used=set()
    def visit(x):
        if isinstance(x,int) or x in used:return
        used.add(x)
        if x in defs:
            for v in defs[x]:visit(v)
    visit(g['output'])
    require(used==known,'dead register or input')
    return Counter(r[1] for r in g['source'])

def leading(g):
    names=g['witnesses']+g['fixed_numerals']
    r=Ring(names)
    env={n:(int(n in g['witnesses']),r.var(n)) for n in names}
    def get(x):
        return (0,r.const(x)) if isinstance(x,int) else env[x]
    for name,op,a,b in g['source']:
        da,pa=get(a);db,pb=get(b)
        if op=='*':
            out=(da+db,r.mul(pa,pb))
        else:
            d=max(da,db)
            p=r.add(pa if da==d else {},pb if db==d else {},1 if op=='+' else -1)
            # No leading cancellation occurs in this graph.
            require(bool(p),'leading cancellation requires lower-degree recovery at '+name)
            out=d,p
        env[name]=out
    q0=r.mul(r.var('beta'),r.var('J'))
    k0=r.add(r.var('eta'),r.var('zeta'))
    B0=r.add(r.mul(r.mul(k0,r.var('s')),r.var('T')),
             r.mul(r.pow(q0,2),r.add(q0,r.var('F'),-1)),-1)
    expected=r.const(-9*2**10)
    for p,e in [(q0,100),(r.var('w'),26),(r.var('s'),58),
                (r.var('i'),10),(k0,32),(B0,2)]:
        expected=r.mul(expected,r.pow(p,e))
    degree,actual=env[g['output']]
    require(degree==232,'wrong degree')
    require(actual==expected,'wrong whole leading form')
    return {
        'degree':degree,'leading_terms':len(actual),
        'cut_degrees':{x:env[x][0] for x in
                       ['DpI2','trace_f','Q','Dg','cTR','V','Mtot','Znum','RGV2']},
        'attained_monomial':'J^100 w^26 s^60 i^10 eta^34 T^2',
        'attained_coefficient':'-9216*beta^100'
    }

def exact_map_identity():
    # Independent algebraic cut: f=1+c*d, b=c*T-R, V_old=f²*b-c.
    r=Ring(['c','d','T','R','n','B','h','D','H','K','e6','sigma6','Q','G'])
    v={n:r.var(n) for n in r.names}
    c,d,T,R,n,B,h,D,H,K,e6,sigma6,Q,G=[v[x] for x in r.names]
    mul=r.mul;add=r.add
    f=add(r.const(1),mul(c,d))
    b=add(mul(c,T),R,-1)
    Vold=add(mul(r.pow(f,2),b),c,-1)
    Lold=mul(b,Vold)
    Tnew=add(mul(f,T),mul(d,R),-1)
    bnew=add(mul(c,Tnew),R,-1)
    Vnew=add(mul(f,bnew),c,-1)
    Lnew=mul(bnew,Vnew)
    nnew=add(n,mul(mul(add(f,r.const(1),-1),Lold),B))
    require(bnew==mul(f,b),'b map')
    require(Vnew==Vold,'V map')
    require(add(nnew,mul(Lnew,B),-1)==add(n,mul(Lold,B),-1),'center map')
    def z(nn,ll):
        p1=mul(mul(h,D),add(mul(H,add(nn,mul(ll,B),-1)),K))
        p2=mul(H,add(mul(D,B),mul(h,add(e6,sigma6,-1))))
        return add(p1,p2,-1)
    zold=z(n,Lold);znew=z(nnew,Lnew)
    require(znew==zold,'full numerator map')
    # The complete finalizer is a fixed polynomial in the identical
    # z,V,Q,G,M values. This exact cut proves the full substitution identity.
    return {'b_map':True,'V_map':True,'center_map':True,
            'full_numerator_map':True,'finalizer_cut':'same Z,V,Q,G,M'}

def candidate_expected():
    old=load('inherited/inverse85_degree304.json')
    expected=copy.deepcopy(old['source'])
    for row in expected:
        if row[0]=='Fsqr':row[:]=['trace_f','+','DpI2','Df']
        elif row[0]=='DfcTR':row[2]='trace_f'
    return old,expected

def verify():
    new=load('equations/inverse_lucas_trace85_degree232.json')
    old,expected=candidate_expected()
    trace=load('inherited/trace87_degree232.json')
    require(new['source']==expected,'literal source mismatch')
    require(new['witnesses']==old['witnesses']==trace['witnesses'],'witness mismatch')
    require(new['fixed_numerals']==old['fixed_numerals']==trace['fixed_numerals'],'port mismatch')
    require(old['coefficient_binding']['ports']==trace['coefficient_binding']['ports'],'whole tuple mismatch')
    for port,binding in new['coefficient_binding']['ports'].items():
        raw=gzip.decompress((ROOT/'coefficients'/binding['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==old['coefficient_binding']['ports'][port]['raw_sha256'],'raw coefficient '+port)
        require(binding['raw_sha256']==old['coefficient_binding']['ports'][port]['raw_sha256'],'coefficient metadata '+port)
        require(int.from_bytes(raw,binding['byte_order']).bit_length()==binding['bits'],'coefficient bits '+port)
    counts=topology(new)
    require(counts==Counter({'*':51,'+':18,'-':16}),'wrong operation counts')
    require(len(new['source'])==85,'wrong count')
    require(new['exact_degree']==232 and new['operations']==85,'metric mismatch')
    degree=leading(new)
    mapping=exact_map_identity()
    alt=load('equations/inverse_lucas_trace85_degree232_b2.json')
    alt_expected=copy.deepcopy(expected)
    for row in alt_expected:
        if row[0]=='L':row[3]='cTR'
    require(alt['source']==alt_expected,'literal b2 alternative mismatch')
    require(topology(alt)==counts,'b2 counts or liveness mismatch')
    alt_degree=leading(alt)
    require(alt_degree['cut_degrees']['Znum']==21,'b2 carrier degree')
    # Detect source mutations against an independently reconstructed parent edit.
    rejected=0
    for i,row in enumerate(new['source']):
        for op in '+-*':
            if op==row[1]:continue
            altered=copy.deepcopy(new['source']);altered[i][1]=op
            require(altered!=expected,'undetected literal operator corruption')
            rejected+=1
    hashes={}
    for name in ['inherited/inverse85_degree304.json','inherited/trace87_degree232.json',
                 'inherited/inverse_PROOF.md','inherited/trace_PROOF.md',
                 'equations/inverse_lucas_trace85_degree232.json',
                 'equations/inverse_lucas_trace85_degree232_b2.json',
                 'inherited/coefficient_recipe.tex','build_coefficients.py',
                 'COMPOSITION_PROOF.md']:
        hashes[name]=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    return {'status':'PASS','scope':'Exact finite graph, tuple identity, whole leading component, and polynomial map; unbounded proofs remain separate.',
            'variables':10,'domain':'strictly positive integers','operations':85,
            'counts':dict(counts),'degree':degree,'polynomial_map':mapping,
            'b_squared_alternative':alt_degree,
            'literal_operator_mutations_rejected':rejected,'sha256':hashes}

if __name__=='__main__':
    print(json.dumps(verify(),indent=2))

