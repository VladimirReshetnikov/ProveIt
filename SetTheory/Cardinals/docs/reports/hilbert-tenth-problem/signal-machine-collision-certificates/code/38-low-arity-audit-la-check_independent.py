#!/usr/bin/env python3
"""Independent exact arithmetic. Input packets are read as data only.
No subprocess, network, import of packet code, machine interpreter, or Lean.
"""
import argparse,gzip,hashlib,itertools,json,math,time,zipfile
from collections import defaultdict
from pathlib import Path

class Poly:
    def __init__(self,n,terms=None):self.n=n;self.t={k:v for k,v in (terms or {}).items() if v}
    @classmethod
    def const(cls,n,v):return cls(n,{(0,)*n:v})
    @classmethod
    def var(cls,n,j):return cls(n,{tuple(int(i==j) for i in range(n)):1})
    def coerce(self,o):return o if isinstance(o,Poly) else Poly.const(self.n,o)
    def __add__(self,o):
        o=self.coerce(o);assert self.n==o.n
        d=self.t.copy()
        for e,c in o.t.items():d[e]=d.get(e,0)+c
        return Poly(self.n,d)
    __radd__=__add__
    def __neg__(self):return Poly(self.n,{e:-c for e,c in self.t.items()})
    def __sub__(self,o):return self+-self.coerce(o)
    def __rsub__(self,o):return self.coerce(o)+-self
    def __mul__(self,o):
        o=self.coerce(o);assert self.n==o.n;d=defaultdict(int)
        for e,c in self.t.items():
            for f,a in o.t.items():d[tuple(x+y for x,y in zip(e,f))]+=c*a
        return Poly(self.n,d)
    __rmul__=__mul__
    def __pow__(self,k):
        assert isinstance(k,int) and k>=0
        ans=Poly.const(self.n,1);a=self
        while k:
            if k&1:ans=ans*a
            k//=2
            if k:a=a*a
        return ans
    def __eq__(self,o):return self.t==self.coerce(o).t
    def degree(self):return max(map(sum,self.t),default=-1)
    def norm(self):return sum(map(abs,self.t.values()))
    def ev(self,v):return sum(c*math.prod(x**p for x,p in zip(v,e)) for e,c in self.t.items())
    def embed(self,n,mapping):
        d={}
        for e,c in self.t.items():
            f=[0]*n
            for j,p in enumerate(e):f[mapping[j]]+=p
            d[tuple(f)]=c
        return Poly(n,d)
    def serial(self):return [[list(e),str(c)] for e,c in sorted(self.t.items())]

def prod(xs,one=1):
    xs=list(xs)
    if not xs:return one
    v=xs[0]
    for x in xs[1:]:v=v*x
    return v

def sos(xs):return sum(x*x for x in xs)
def horner(coeff,x):
    z=0
    for a in reversed(coeff):z=z*x+a
    return z

def bases(K):
    # Independent construction: divide full monic node polynomial by z-i.
    r=[1]
    for i in range(1,K+1):
        q=[0]*(len(r)+1)
        for j,c in enumerate(r):q[j]-=i*c;q[j+1]+=c
        r=q
    out=[];c=math.factorial(K-1)
    for i in range(1,K+1):
        q=[0]*K;q[-1]=r[-1]
        for j in range(K-2,-1,-1):q[j]=r[j+1]+i*q[j+1]
        assert r[0]+i*q[0]==0
        den=horner(q,i);assert c%den==0
        out.append([a*(c//den) for a in q])
    return r,out

def tensor(K,S):
    A,B,r,s=[Poly.var(4,j) for j in range(4)];z=Poly.const(4,0)
    if K==1:return [A-r,B-s,z,z,Poly.const(4,int(not S))]
    R,L=bases(K);u=A-r+1;v=B-s+1
    lu=[horner(x,u) for x in L];lv=[horner(x,v) for x in L]
    f=sum((lu[i-1]*lv[j-1] for i,j in grid(K) if (i,j) not in S),z)
    return [horner(R,u),horner(R,v),(r-1)*(u-K),(s-1)*(v-K),f]

def grid(K,d=2):return list(itertools.product(range(1,K+1),repeat=d))
def pp(K,x):return prod(((x-h)**2 for h in range(1,K)),1)
def factors(K,S,d=2):
    X=[Poly.var(d+1,j) for j in range(d)];w=Poly.var(d+1,d)
    if K==1:return [(w-1)**2] if S else []
    P=[pp(K,x) for x in X]
    return [sum(((X[j]-a[j])**2 for j in range(d) if a[j]<K),Poly.const(d+1,0))+(w-prod((P[j] for j in range(d) if a[j]==K),1))**2 for a in sorted(S)]
def one(K,S,d=2):return prod(factors(K,S,d),Poly.const(d+1,1))
def one_value(K,S,X,w):
    if K==1:return (w-1)**2 if S else 1
    return prod((sum((x-a)**2 for x,a in zip(X,cell) if a<K)+(w-prod((pp(K,x) for x,a in zip(X,cell) if a==K),1))**2 for cell in S),1)
def tensor_value(K,S,A,B,r,s):
    if K==1:return (A-r)**2+(B-s)**2+int(not S)
    R,L=bases(K);u=A-r+1;v=B-s+1
    f=sum(horner(L[i-1],u)*horner(L[j-1],v) for i,j in grid(K) if (i,j) not in S)
    return horner(R,u)**2+horner(R,v)**2+((r-1)*(u-K))**2+((s-1)*(v-K))**2+f*f

def table_iter(K,d=2):
    cells=grid(K,d)
    for bits in range(1<<len(cells)):yield {c for j,c in enumerate(cells) if (bits>>j)&1}
def closure(K,S):
    return {b for a in S for b in itertools.product(*(range(1,K+1) if x==K else [x] for x in a))}
def closure_local(K,S):
    # Single-coordinate replacements, repeated over every accepted cell.
    for a in S:
        for j,x in enumerate(a):
            if x==K:
                for y in range(1,K+1):
                    b=list(a);b[j]=y
                    if tuple(b) not in S:return False
    return True

def zero_poly(K,S,d):
    X=[Poly.var(d,j) for j in range(d)]
    return prod((sum(((X[j]-a[j])**2 for j in range(d) if a[j]<K),Poly.const(d,0)) for a in sorted(S)),Poly.const(d,1))

class Count:
    add=0;mul=0
    def __init__(self,v):self.v=v
    def __add__(self,o):Count.add+=1;return Count(self.v+(o.v if isinstance(o,Count) else o))
    __radd__=__add__
    def __sub__(self,o):Count.add+=1;return Count(self.v-(o.v if isinstance(o,Count) else o))
    def __mul__(self,o):Count.mul+=1;return Count(self.v*(o.v if isinstance(o,Count) else o))
    __rmul__=__mul__
def addlist(xs,zero):
    if not xs:return zero
    x=xs[0]
    for a in xs[1:]:x=x+a
    return x

def tensor_gate(K,S,values):
    Count.add=Count.mul=0;A,B,r,s=map(Count,values);u=A-r+1;v=B-s+1
    a=[u-i for i in range(1,K+1)];b=[v-i for i in range(1,K+1)]
    L=[[prod(row[:i]+row[i+1:])*((-1)**(K-i-1)*math.comb(K-1,i)) for i in range(K)] for row in [a,b]]
    terms=[L[0][i-1]*L[1][j-1] for i,j in grid(K) if (i,j) not in S]
    ds=[prod(a),prod(b),(r-1)*a[-1],(s-1)*b[-1],addlist(terms,Count(0))]
    out=addlist([x*x for x in ds],Count(0));return out.v,Count.add,Count.mul

def one_gate(K,S,values):
    if not S:return 1,0,0
    Count.add=Count.mul=0;A,B,w=map(Count,values);T=K-1
    dif=[[x-h for h in range(1,K)] for x in [A,B]]
    sq=[[x*x for x in row] for row in dif];pa,pb=[prod(row) for row in sq]
    q0=w-1;qa=w-pa;qb=w-pb;qc=w-pa*pb;q0,qa,qb,qc=[x*x for x in [q0,qa,qb,qc]]
    fs=[]
    for i,j in sorted(S):
        if i<K and j<K:fs.append(sq[0][i-1]+sq[1][j-1]+q0)
        elif i<K:fs.append(sq[0][i-1]+qb)
        elif j<K:fs.append(sq[1][j-1]+qa)
        else:fs.append(qc)
    out=prod(fs);return out.v,Count.add,Count.mul

MODV=['C','o','g','q_b','q_v','J','q_alpha','d_wb_plus','d_wC_plus','d_yC_plus','q_sigma_plus','q_tau_plus','q_r_plus']
def power(vals):
    C,o,g,qb,qv,J,qa,dwb,dwc,dy,qs,qt,qr=vals
    dwb,dwc,dy,qs,qt,qr=[x-1 for x in [dwb,dwc,dy,qs,qt,qr]]
    w=2+dwb;y=C+dy;beta=1+4*y*qb;v=y*y*qv;t=C+4*y*qt;M=2*o+J;Z=M+5
    X=y*(Z-8)+8*o+4*M*qr;U=4*beta-Z;V=qa*X+U*qs
    return [X*X-16-(Z*Z-16)*y*y,U*U-16*qa*qa-(Z*Z-16)*qa*qa*v*v,V*V-16*qa*qa-16*qa*qa*(beta*beta-1)*t*t,w-C-dwc,Z*Z-16-16*((w+1)*(w+1)-1)*(w*g)*(w*g)]
def fixture(k):return [1,1,3,4+577*k,34,61,4*k,1,2,1,4*k+1,1,1]
def stats(P):return {'degree':P.degree(),'monomials':len(P.t),'norm':str(P.norm()),'max_coefficient_bits':max((abs(c).bit_length() for c in P.t.values()),default=0)}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def loadpoly(rows,n):return Poly(n,{tuple(e):int(c) for e,c in rows})
def main(a):
    start=time.monotonic();src=a.source.resolve();out=a.out.resolve();assert src!=out and src not in out.parents
    out.mkdir(parents=True,exist_ok=False)
    results={'method':'independent exact algebra; declared tables only; conditional Pell import; no input code executed','checks':{},'two':[],'one':[],'compositions':[]};counts=defaultdict(int);saved=[]
    assert sha(src/'MANIFEST.sha256')=='b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82'
    manifest=[]
    for line in (src/'MANIFEST.sha256').read_text().splitlines():
        h,p=line.split('  ',1);assert sha(src/p)==h;p0=(src/p).resolve();assert src in p0.parents;manifest.append(p)
    assert set(manifest)=={str(p.relative_to(src)) for p in src.rglob('*') if p.is_file() and p.name!='MANIFEST.sha256'}
    counts['source_manifest_files']=len(manifest)
    for p in json.loads((src/'SOURCE_PINS.json').read_text()):
        f=src/p['file'];assert f.stat().st_size==p['bytes'] and sha(f)==p['sha256'];counts['dependency_pins']+=1
    if a.archive:
        assert sha(a.archive)=='897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c'
        with zipfile.ZipFile(a.archive) as z:
            names=[n for n in z.namelist() if not n.endswith('/')]
            for name in names:
                parts=Path(name).parts;rel=Path(*parts[1:]) if parts[0]==src.name else Path(name)
                assert not rel.is_absolute() and '..' not in rel.parts
                assert z.read(name)==(src/rel).read_bytes();counts['archive_file_matches']+=1
            assert len(names)==len(manifest)+1
    for K in range(1,10):
        R,L=bases(K);c=math.factorial(K-1)
        for i,q in enumerate(L,1):
            for j in range(1,K+1):assert horner(q,j)==c*int(i==j);counts['basis_nodes']+=1
        assert [sum(q[j] for q in L) for j in range(K)]==[c]+[0]*(K-1)
    native_cache={};one_cache={};composition_cache={}
    for K in range(1,8):
        cells=set(grid(K));tables=[set(),cells,{(1,1)},{(K,K)},{(i,i) for i in range(1,K+1)},{c for c in cells if sum(c)%2==0}]
        if K<=2:tables=list(table_iter(K))
        for S in tables:
            ds=tensor(K,S);P=sos(ds);key=(K,tuple(sorted(S)));native_cache[key]=(ds,P)
            if K==1:assert P.degree()==2 and len(P.t)==(6 if S else 7)
            else:
                assert P.degree()==max(2*K,4,2*ds[-1].degree())<=4*(K-1)
                B=math.factorial(K+1);L=2**(K-1)*B;Q=L**4+2*B*B+8*(K+1)**2
                assert P.norm()<=Q and len(P.t)<=K*K*(2*K-1)**2+8*K+2
                for e in P.t:
                    ar=e[0]+e[2];bs=e[1]+e[3]
                    assert (ar<=2*K-2 and bs<=2*K-2) or (ar==0 and bs<=2*K) or (bs==0 and ar<=2*K)
                if S=={(1,1)}:assert P.degree()==4*(K-1)
                val,ad,mu=tensor_gate(K,S,(K+3,K+1,2,3));m=K*K-len(S)
                assert val==P.ev((K+3,K+1,2,3)) and ad==2*K+10+max(m-1,0) and mu==2*K*K+m+5
                assert ad+mu<=4*K*K+2*K+14;counts['tensor_gate_instances']+=1
            results['two'].append({'K':K,'accepted':sorted(S),**stats(P)});counts['tensor_expansions']+=1
            saved.append({'kind':'two','K':K,'accepted':sorted(S),'variables':['A','B','r','s'],'residuals':[d.serial() for d in ds],'polynomial':P.serial()})
    print('tensor expansions complete',flush=True)
    for K in [1,2,3]:
        for S in table_iter(K):
            counts['all_small_tables']+=1
            for A,B in itertools.product(range(1,K+3),repeat=2):
                rs=(A-min(A,K)+1,B-min(B,K)+1) if K>1 else (A,B)
                expected=(min(A,K),min(B,K)) in S
                assert (tensor_value(K,S,A,B,*rs)==0)==expected;counts['tensor_canonical_assignments']+=1
                w=prod((pp(K,x) for x in [A,B] if x>=K),1) if K>1 else 1
                for z in sorted({1,2,3,w,max(1,w-1),w+1}):
                    assert (one_value(K,S,(A,B),z)==0)==(expected and z==w);counts['one_candidate_assignments']+=1
                if K<=2:
                    for r,s in itertools.product(range(1,K+4),repeat=2):
                        v=tensor_value(K,S,A,B,r,s);assert (v==0)==(expected and (r,s)==rs)
                        assert v==native_cache[(K,tuple(sorted(S)))][1].ev([A,B,r,s]);counts['tensor_witness_box_assignments']+=1
            C=closure(K,S);assert closure_local(K,S)==(C==S)
            if C==S:
                R=zero_poly(K,S,2)
                for A,B in itertools.product(range(1,K+3),repeat=2):assert (R.ev([A,B])==0)==((min(A,K),min(B,K)) in S);counts['zero_polynomial_assignments']+=1
                counts['zero_witness_closed_K'+str(K)]+=1
            else:
                a0=next(a0 for a0 in S if any(b not in S for b in closure(K,{a0})))
                witness=next(b for b in closure(K,{a0}) if b not in S);assert witness in closure(K,{a0});counts['nonclosed_obstructions']+=1
            counts['closure_tables']+=1
    assert tensor_value(3,{(3,1)},2,1,0,1)==0
    assert one_value(3,{(1,3)},(1,2),0)==0
    counts['outside_domain_zero_challenges']=2
    print('finite tables and closure complete',flush=True)
    for K in range(1,5):
        cells=set(grid(K));tables=list(table_iter(K)) if K<=2 else [set(),{(1,1)},{(K,K)},{(1,K),(K,1)},cells if K==3 else {(1,1),(1,K),(K,1),(K,K)}]
        for S in tables:
            Q=one(K,S);N=len(S);ni=sum(i<K and j<K for i,j in S);nc=int((K,K) in S);ne=N-ni-nc;T=K-1
            D=(2 if S else 0) if K==1 else 2*ni+4*T*ne+8*T*nc
            assert Q.degree()==D
            if K>1:
                PK=math.factorial(K)**2;bound=(2*K*K+4)**ni*(K*K+(1+PK)**2)**ne*(1+PK*PK)**(2*nc)
                assert Q.norm()<=bound and len(Q.t)<=math.comb(D+3,3) and D<=10*T*T+8*T
                val,ad,mu=one_gate(K,S,(K+1,K+2,7));assert val==Q.ev([K+1,K+2,7])
                if N:assert ad==2*T+4+2*ni+ne and mu==4*T+3+N-1 and ad+mu<=3*T*T+10*T+7
                else:assert ad==mu==0
                counts['one_gate_instances']+=1
            if K<=2:
                A0,B0,w0=[Poly.var(3,j) for j in range(3)];choices=[]
                if K==1:choices=[[(w0-1) if S else Poly.const(3,1)]]
                else:
                    for i,j in sorted(S):
                        fixed=[x-a0 for x,a0 in [(A0,i),(B0,j)] if a0<K]
                        choices.append(fixed+[w0-prod((pp(K,x) for x,a0 in [(A0,i),(B0,j)] if a0==K),1)])
                distributed=list(itertools.product(*choices))
                rebuilt=sos([prod(cs,Poly.const(3,1)) for cs in distributed])
                assert rebuilt==Q and len(distributed)==(3**ni*2**ne if K>1 else 1)
                counts['distributed_sos_identities']+=1
            for A0,B0,z0 in [(1,1,1),(K+1,K+2,3),(-1,0,-2),(0,-3,1)]:
                assert Q.ev([A0,B0,z0])==one_value(K,S,(A0,B0),z0)>=0
                counts['one_expanded_direct_assignments']+=1
            key=(K,tuple(sorted(S)));one_cache[key]=Q
            results['one'].append({'K':K,'accepted':sorted(S),**stats(Q),'distributed_square_slots':3**ni*2**ne if K>1 else 1})
            saved.append({'kind':'one','K':K,'accepted':sorted(S),'variables':['A','B','w'],'polynomial':Q.serial()});counts['one_expansions']+=1
    print('one-variable expansions complete',flush=True)
    for d in range(1,6):
        for K in range(2,6):
            cells=grid(K,d);summ=sum(2 if all(x<K for x in a0) else 4*(K-1)*sum(x==K for x in a0) for a0 in cells)
            assert summ==2*(K-1)**d+4*d*(K-1)*K**(d-1);counts['dimension_degree_ledgers']+=1
    for d in [1,3]:
        K=2
        for S in table_iter(K,d):
            assert closure_local(K,S)==(closure(K,S)==S);counts['dimension_closure_tables']+=1
            for X in grid(3,d):
                w=prod((pp(K,x) for x in X if x>=K),1);expected=tuple(min(x,K) for x in X) in S
                for z in {w,w+1}:assert (one_value(K,S,X,z)==0)==(expected and z==w);counts['dimension_assignments']+=1
    # Symbolic (not just sampled) module family in a free parameter.
    k=Poly.var(1,0)
    assert all(h==0 for h in power(fixture(k)));counts['symbolic_power_family_identities']=5
    H=power([Poly.var(13,j) for j in range(13)]);P=sos(H)
    assert len(H)==5 and len(MODV)==13 and len(set(MODV))==13
    assert {j for e0 in P.t for j,p0 in enumerate(e0) if p0}==set(range(13))
    assert [h.degree() for h in H]==[4,10,10,1,6] and P.degree()==20
    e=[0]*13
    for name,p in [('J',4),('q_alpha',4),('d_yC_plus',8),('q_v',4)]:e[MODV.index(name)]=p
    assert P.t[tuple(e)]==1 and len(P.t)==12858
    for k in [1,2,3,7,23]:
        v=fixture(k);assert all(x>0 for x in v) and all(h.ev(v)==0 for h in H);counts['positive_power_fixtures']+=1
        for j in range(1,13):
            bad=v.copy();bad[j]+=1
            if all(h.ev(bad)==0 for h in H):counts['valid_module_perturbations']+=1
            else:counts['rejected_module_perturbations']+=1
    saved.append({'kind':'power','variables':MODV,'residuals':[h.serial() for h in H],'polynomial':P.serial()});results['power']=stats(P)
    # Paid compositions use disjoint module variables and the already counted indices.
    for typ in ['two','one']:
        n=31 if typ=='two' else 30
        # g1,g2,g3,A,B, then first and second twelve leaves, then native leaves.
        g1,g2,g3=[Poly.var(n,j) for j in range(3)];D=g1+g2+g3
        m1=[3]+list(range(5,17));m2=[4]+list(range(17,29))
        h1=[h.embed(n,m1) for h in H];h2=[h.embed(n,m2) for h in H]
        G=[(20*g1-D)*Poly.var(n,5)-2*D,(20*g3-D)*Poly.var(n,17)-2*D]
        E=sos(G+h1+h2);assert E.degree()==20 and len(G+h1+h2)==12
        assert n-3==2+2*12+(2 if typ=='two' else 1)
        cases=[(1,set()),(1,{(1,1)}),(2,set(grid(2))),(3,{(3,3)}),(3,set(grid(3)))] if typ=='one' else [(K,S) for K in [1,2,3,6,7] for S in [set(),{(1,1)}]]
        for K,S in cases:
            if typ=='two':
                ds,Q=native_cache[(K,tuple(sorted(S)))];Q0=Q.embed(n,[3,4,29,30]);F=E+Q0
                assert F.degree()==max(20,Q.degree()) and len(G+h1+h2+ds)==17
                assert {j for e0 in F.t for j,p0 in enumerate(e0) if p0}==set(range(n))
                counts['two_composition_expansions']+=1
                composition_cache[(K,tuple(sorted(S)))]=F
                polynomials=[F];degrees=[F.degree()]
            else:
                Q=one_cache[(K,tuple(sorted(S)))];Q0=Q.embed(n,[3,4,29]);F=E+Q0
                # Full self-convolution of K=3 full Q is deliberately not required: certificate and top parts prove its square degree.
                if len(Q.t)<1000:Fsq=E+(Q*Q).embed(n,[3,4,29]);assert Fsq.degree()==max(20,2*Q.degree());counts['one_squared_composition_expansions']+=1
                assert F.degree()==max(20,Q.degree());counts['one_product_composition_expansions']+=1
                polynomials=[F];degrees=[F.degree(),max(20,2*Q.degree())]
            results['compositions'].append({'kind':typ,'K':K,'accepted':sorted(S),'witnesses':n-3,'variables':n,'degree_or_degrees':degrees,'polynomial_monomials':len(F.t)})
            for k in [1,2,7]:
                v=[3,14,3,1,1]+fixture(k)[1:]+fixture(k+1)[1:]+([1,1] if typ=='two' else [1])
                assert len(v)==n and min(v)>0
                assert (F.ev(v)==0)==((1,1) in S);counts['composition_assignments']+=1
                bad=v.copy();bad[0]+=1;assert F.ev(bad)>0;counts['changed_gap_rejections']+=1
    print('module and compositions complete',flush=True)
    # Compare saved author DATA only, after the independent expansions exist.
    author=json.load(gzip.open(src/'evidence/expanded_polynomials.json.gz','rt'))
    for item in author:
        vs=item['variables'];meta=item.get('meta',{})
        if vs==['A','B','r','s']:
            K=meta['K'];S={tuple(x) for x in meta['accepted']};ds,Q=native_cache[(K,tuple(sorted(S)))]
            assert Q==loadpoly(item['polynomial'],4)
            assert ds==[loadpoly(r,4) for r in item['residuals']];counts['source_tensor_coefficient_matches']+=1
        elif vs==['A','B','w']:
            K=meta['K'];S={tuple(x) for x in meta['accepted']};Q=one(K,S)
            assert Q==loadpoly(item['polynomial'],3);counts['source_one_coefficient_matches']+=1
        elif len(vs)==13:
            assert set(vs)==set(MODV);mapping=[vs.index(x) for x in MODV]
            assert P.embed(13,mapping)==loadpoly(item['polynomial'],13)
            assert [h.embed(13,mapping) for h in H]==[loadpoly(r,13) for r in item['residuals']];counts['source_power_coefficient_matches']+=1
        elif len(vs)==31:
            K=meta['K'];assert meta['table']=='origin';F=composition_cache[(K,((1,1),))]
            ours=['g1','g2','g3','A','B']+['left_'+x for x in MODV[1:]]+['right_'+x for x in MODV[1:]]+['r','s']
            assert set(ours)==set(vs)
            assert F.embed(31,[vs.index(x) for x in ours])==loadpoly(item['polynomial'],31)
            counts['source_composed_coefficient_matches']+=1
        else:raise AssertionError('unrecognized coefficient record')
    results['checks']=dict(sorted(counts.items()));results['seconds']=round(time.monotonic()-start,3)
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    with gzip.GzipFile(filename=str(out/'expansions.json.gz'),mode='wb',mtime=0) as f:f.write(json.dumps(saved,separators=(',',':')).encode())
    print(json.dumps(results['checks'],sort_keys=True));print('PASS',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',required=True,type=Path);p.add_argument('--out',required=True,type=Path);p.add_argument('--archive',type=Path);main(p.parse_args())
