#!/usr/bin/env python3
"""Report125 finite companion. Exact standard-library algebra, never a proof of analytic limits."""
import sys
sys.dont_write_bytecode = True
from collections import defaultdict
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from math import factorial, comb
import importlib.util
import json
import re

ROOT = Path(__file__).resolve().parent
LEGACY_FILES = frozenset({'README.md','verify.py','negative_tests.py','evidence.json','provenance.json','b279571.txt','historical_gmp_n0_1000.txt','enumerate_gmp.cpp','historical_verification.json','manifest.sha256'})
FILES = frozenset({'README.md','verify.py','negative_tests.py','evidence.json','provenance.json','manifest.sha256'} | {'legacy/'+f for f in LEGACY_FILES})
ARCHIVE_MANIFEST_HASH = '79f5dfa1cb52fe41ec57b4cbc73638d502f1f9a73cec9e3af881e6fabd399295'
PROOF_HASH = 'b2c806a56c3f8b652646527d9bf1c3c62ee64046d11e36e25db243eac53e05cf'
PUBLIC_HASH = '9fa7ab4c890fd441996ad028a2bd25c9ef69904c13f1a383371023627ac37c65'

class CheckError(Exception): pass

def require(ok, message):
    if not ok: raise CheckError(message)
def same(a,b,message): require(a==b,message)
def unique(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,'JSON: duplicate key '+k); d[k]=v
    return d

def load(name):
    try:
        return json.loads((ROOT/name).read_text(encoding='utf-8'),object_pairs_hook=unique,
            parse_constant=lambda _: (_ for _ in ()).throw(CheckError('JSON: nonfinite number')))
    except (ValueError,UnicodeError) as e: raise CheckError('JSON: invalid '+name) from e

def keys(d,ks,path): require(type(d) is dict and set(d)==set(ks),'SCHEMA: '+path+' keys')
def integer(v,path):
    require(type(v) is int,'SCHEMA: '+path+' integer'); return v

def rational(v,path):
    require(type(v) is str and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?',v) is not None,'SCHEMA: '+path+' canonical rational')
    q=Q(v); same(str(q),v,'SCHEMA: '+path+' canonical rational'); return q

def array(d,shape,path):
    if not shape: return rational(d,path)
    require(type(d) is list and len(d)==shape[0],'SCHEMA: '+path+' shape')
    return [array(v,shape[1:],path+'['+str(i)+']') for i,v in enumerate(d)]

def snapshot():
    return {p.relative_to(ROOT).as_posix():sha256(p.read_bytes()).hexdigest() for p in ROOT.rglob('*') if p.is_file()}

def inventory():
    paths=list(ROOT.rglob('*'))
    require(not any(p.is_symlink() for p in paths),'INVENTORY: symlink forbidden')
    same({p.relative_to(ROOT).as_posix() for p in paths if p.is_dir()},{'legacy'},'INVENTORY: unexpected or missing directory')
    same({p.relative_to(ROOT).as_posix() for p in paths if p.is_file()},FILES,'INVENTORY: unexpected or missing member')
    require(all(p.is_file() or p.is_dir() for p in paths),'INVENTORY: nonregular member')
    entries={}
    for line in (ROOT/'manifest.sha256').read_text(encoding='ascii').splitlines():
        require(re.fullmatch(r'[0-9a-f]{64}  (?:legacy/)?[A-Za-z0-9_.-]+',line) is not None,'MANIFEST: malformed entry')
        h,n=line.split('  '); require(n not in entries,'MANIFEST: duplicate member'); entries[n]=h
    same(set(entries),FILES-{'manifest.sha256'},'MANIFEST: closed inventory mismatch')
    for n in sorted(entries): same(sha256((ROOT/n).read_bytes()).hexdigest(),entries[n],'HASH: '+n)
    same(sha256((ROOT/'legacy/manifest.sha256').read_bytes()).hexdigest(),ARCHIVE_MANIFEST_HASH,'ARCHIVE: Report123 manifest anchor')
    for line in (ROOT/'legacy/manifest.sha256').read_text(encoding='ascii').splitlines():
        digest,name=line.split('  ')
        same(sha256((ROOT/'legacy'/name).read_bytes()).hexdigest(),digest,'ARCHIVE: immutable '+name)

def evidence():
    d=load('evidence.json')
    keys(d,{'schema','ranges','forward','dual','cycles','whitening','brownian','inverse','counting'},'evidence')
    same(d['schema'],'a279571-leading-finite-v1','SCHEMA: evidence version')
    keys(d['ranges'],{'brute','tree','endpoint','reversal','historical','reflection_angles'},'ranges')
    for k,v in d['ranges'].items(): integer(v,'ranges.'+k)
    same(d['ranges'],{'brute':9,'tree':65,'endpoint':12,'reversal':5,'historical':1001,'reflection_angles':5},'RANGE: mandatory coverage changed')
    for name in ('forward','dual'):
        x=d[name]; keys(x,{'color','stationary','drift','h','Gamma','B','Sigma'},name)
        for key,shape in [('color',[2,2]),('stationary',[2]),('drift',[2,2]),('h',[2,2]),('Gamma',[2,2,2]),('B',[2,2,2]),('Sigma',[2,2])]: x[key]=array(x[key],shape,name+'.'+key)
    keys(d['cycles'],{'forward_P','forward_Q','dual_P','dual_Q'},'cycles')
    for name,x in d['cycles'].items():
        keys(x,{'mean','covariance','determinant'},'cycles.'+name)
        x['mean']=array(x['mean'],[3],'cycles.'+name+'.mean')
        x['covariance']=array(x['covariance'],[3,3],'cycles.'+name+'.covariance')
        x['determinant']=rational(x['determinant'],'cycles.'+name+'.determinant')
    x=d['whitening'];keys(x,{'A','inverse_sigma','determinant_squared','cosine_squared'},'whitening')
    x['A']=array(x['A'],[2,2,2],'whitening.A');x['inverse_sigma']=array(x['inverse_sigma'],[2,2],'whitening.inverse_sigma')
    for k in ('determinant_squared','cosine_squared'):x[k]=rational(x[k],'whitening.'+k)
    x=d['brownian'];keys(x,{'b','I1','I2','k','reflection_b_pi'},'brownian')
    for k in ('b','I1','I2','k'):
        require(type(x[k]) is list and len(x[k])==6,'SCHEMA: brownian.'+k+' shape')
        x[k]=[rational(x[k][0],'brownian.'+k+' coefficient')]+[integer(v,'brownian.'+k+' exponent') for v in x[k][1:]]
    keys(x['reflection_b_pi'],{'1','2','3','4','6'},'brownian.reflection_b_pi')
    x['reflection_b_pi']={k:rational(v,'brownian.reflection_b_pi.'+k) for k,v in x['reflection_b_pi'].items()}
    x=d['inverse'];keys(x,{'center_coefficients','defect_coefficient','envelope_factor'},'inverse')
    x['center_coefficients']=array(x['center_coefficients'],[4],'inverse.center_coefficients')
    for k in ('defect_coefficient','envelope_factor'):x[k]=rational(x[k],'inverse.'+k)
    x=d['counting'];keys(x,{'initial_factor','time_shift','growth','leading_factor','terminal_stationary'},'counting')
    integer(x['time_shift'],'counting.time_shift')
    for k in ('initial_factor','growth','leading_factor'):x[k]=rational(x[k],'counting.'+k)
    x['terminal_stationary']=array(x['terminal_stationary'],[2],'counting.terminal_stationary')
    return d

# Degree-two multivariate Taylor algebra, variables q1,q2,t. Coefficients are
# ordinary Taylor coefficients, so derivatives multiply repeated powers by 2.
J0=(0,0,0)
def jclean(a):return {m:Q(v) for m,v in a.items() if v}
def jc(c):return {J0:Q(c)} if c else {}
def ja(*args):
    d=defaultdict(Q)
    for a in args:
        for m,v in a.items():d[m]+=v
    return jclean(d)
def js(a,c):return jclean({m:c*v for m,v in a.items()})
def jm(*args):
    out=jc(1)
    for a in args:
        nxt=defaultdict(Q)
        for m,v in out.items():
            for n,w in a.items():
                z=tuple(x+y for x,y in zip(m,n))
                if sum(z)<=2:nxt[z]+=v*w
        out=jclean(nxt)
    return out

def ji(a):
    c=a.get(J0,0);require(c!=0,'JET: inverse of zero constant')
    z=js(ja(a,jc(-c)),1/c)
    return js(ja(jc(1),js(z,-1),jm(z,z)),1/c)

def je(v):
    out=jc(1)
    for i in range(3):
        m=[0]*3;m[i]=1;out[tuple(m)]=Q(v[i])
    linear=ja(out,jc(-1))
    return ja(out,js(jm(linear,linear),Q(1,2)))

def raw(jet,dim=3):
    mean=[];second=[]
    for i in range(dim):
        m=[0]*3;m[i]=1;mean.append(jet.get(tuple(m),Q(0)))
    for i in range(dim):
        row=[]
        for k in range(dim):
            m=[0]*3;m[i]+=1;m[k]+=1;row.append(jet.get(tuple(m),Q(0))*(2 if i==k else 1))
        second.append(row)
    return mean,second

def transition_jets(reverse=False):
    # These closed transforms come directly from the unbounded step families.
    # No producer corrector script, truncated jump sum, or legacy moments is used.
    a=je((1,0,0));b=je((-1,1,0));c=je((0,-1,0))
    pp=js(jm(a,ji(ja(jc(1),js(b,-Q(5,9))))),Q(1,3))
    qp=js(jm(a,c,b,ji(ja(jc(1),js(b,-Q(5,9))))),Q(2,9))
    pq=js(jm(a,c,ji(ja(jc(1),js(c,-Q(3,5))))),Q(1,10))
    qq=js(pq,2)
    L=[[pp,pq],[qp,qq]]
    if reverse:
        pi=[Q(2,3),Q(1,3)]
        L=[[js({m:v*(-1)**(m[0]+m[1]) for m,v in L[j][i].items()},pi[j]/pi[i]) for j in range(2)] for i in range(2)]
    return L

def det(M):
    if len(M)==2:return M[0][0]*M[1][1]-M[0][1]*M[1][0]
    return sum((-1)**j*M[0][j]*det([[M[i][k] for k in range(3) if k!=j] for i in (1,2)]) for j in range(3))

def derive_chain(reverse=False):
    L=transition_jets(reverse);P=[[L[i][j].get(J0,Q(0)) for j in range(2)] for i in range(2)]
    pi=[P[1][0]/(P[0][1]+P[1][0]),P[0][1]/(P[0][1]+P[1][0])]
    E=[[raw(L[i][j],2)[0] for j in range(2)] for i in range(2)]
    R=[[raw(L[i][j],2)[1] for j in range(2)] for i in range(2)]
    drift=[[sum(E[i][j][a] for j in range(2)) for a in range(2)] for i in range(2)]
    same([sum(row) for row in P],[1,1],'CHAIN: stochastic transforms')
    same([sum(pi[i]*drift[i][a] for i in range(2)) for a in range(2)],[0,0],'CHAIN: zero stationary drift')
    gap=P[0][1]+P[1][0]
    # For a two-color chain, I-P acts by gap on its pi-mean-zero subspace.
    h=[[v/gap for v in row] for row in drift]
    G=[[[sum(R[i][j][a][b]+(h[j][a]-h[i][a])*E[i][j][b]+(h[j][b]-h[i][b])*E[i][j][a]+(h[j][a]-h[i][a])*(h[j][b]-h[i][b])*P[i][j] for j in range(2)) for b in range(2)] for a in range(2)] for i in range(2)]
    S=[[sum(pi[i]*G[i][a][b] for i in range(2)) for b in range(2)] for a in range(2)]
    B=[[[ (G[i][a][b]-S[a][b])/gap for b in range(2)] for a in range(2)] for i in range(2)]
    return {'color':P,'stationary':pi,'drift':drift,'h':h,'Gamma':G,'B':B,'Sigma':S}

def chain_checks(d):
    for name in ('forward','dual'):
        actual=derive_chain(name=='dual');x=d[name]
        for k in ('color','stationary','drift','h','Gamma','Sigma','B'):same(x[k],actual[k],'CHAIN: '+name+' '+k)
        P=x['color'];pi=x['stationary'];h=x['h'];G=x['Gamma'];B=x['B'];S=x['Sigma']
        same([sum(pi[i]*h[i][a] for i in range(2)) for a in range(2)],[0,0],'POISSON: '+name+' drift centering')
        same([[h[i][a]-sum(P[i][j]*h[j][a] for j in range(2)) for a in range(2)] for i in range(2)],x['drift'],'POISSON: '+name+' drift equation')
        same([[sum(pi[i]*B[i][a][b] for i in range(2)) for b in range(2)] for a in range(2)],[[0,0],[0,0]],'POISSON: '+name+' covariance centering')
        same([[[G[i][a][b]+sum(P[i][j]*B[j][a][b] for j in range(2))-B[i][a][b] for b in range(2)] for a in range(2)] for i in range(2)],[S,S],'POISSON: '+name+' second-order cancellation')
        require(G[0]!=S and G[1]!=S,'POISSON: conditional covariance defect must be nonzero')
    same(d['forward']['Sigma'],d['dual']['Sigma'],'CHAIN: forward/dual covariance')


def derive_cycle(reverse,start):
    # e^t records ORIGINAL step duration before taking a return-cycle transform.
    z=je((0,0,1));L=[[jm(z,v) for v in row] for row in transition_jets(reverse)]
    other=1-start
    F=ja(L[start][start],jm(L[start][other],L[other][start],ji(ja(jc(1),js(L[other][other],-1)))))
    same(F.get(J0),1,'CYCLE: return probability')
    mean,second=raw(F)
    covariance=[[second[i][j]-mean[i]*mean[j] for j in range(3)] for i in range(3)]
    return {'mean':mean,'covariance':covariance,'determinant':det(covariance)}

def cycle_checks(d):
    for direction in ('forward','dual'):
        for start,color in enumerate(('P','Q')):
            name=direction+'_'+color;actual=derive_cycle(direction=='dual',start);x=d['cycles'][name]
            same(x['mean'],actual['mean'],'CYCLE: '+name+' original-clock mean')
            same(x['covariance'],actual['covariance'],'CYCLE: '+name+' joint covariance')
            same(x['determinant'],actual['determinant'],'CYCLE: '+name+' joint determinant')
            same(x['mean'][:2],[0,0],'CYCLE: zero displacement mean')
            require(x['determinant']>0,'CYCLE: positive joint determinant')
            same([[x['covariance'][i][j]/x['mean'][2] for j in range(2)] for i in range(2)],d[direction]['Sigma'],'CYCLE: '+name+' covariance per ORIGINAL time')
            require(any(x['covariance'][i][2]!=0 for i in range(2)),'CYCLE: displacement/time correlations retained')
            same(x['mean'][2]*d[direction]['stationary'][start],1,'CYCLE: stationary return duration')

# Exact arithmetic in Q(sqrt(3)), sufficient for whitening and reflection groups.
class R:
    def __init__(self,a=0,b=0):self.a=Q(a);self.b=Q(b)
    def __add__(self,v):
        if not isinstance(v,R):v=R(v)
        return R(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self):return R(-self.a,-self.b)
    def __sub__(self,v):return self+-asR(v)
    def __rsub__(self,v):return asR(v)+-self
    def __mul__(self,v):
        v=asR(v);return R(self.a*v.a+3*self.b*v.b,self.a*v.b+self.b*v.a)
    __rmul__=__mul__
    def __truediv__(self,v):
        v=asR(v);den=v.a*v.a-3*v.b*v.b;require(den!=0,'RADICAL: zero divisor');return self*R(v.a/den,-v.b/den)
    def __eq__(self,v):
        v=asR(v);return self.a==v.a and self.b==v.b
    def __bool__(self):return bool(self.a or self.b)
    def __pow__(self,n):
        require(type(n)is int and n>=0,'RADICAL: exponent');out=R(1)
        for _ in range(n):out=out*self
        return out
    def rational(self):same(self.b,0,'RADICAL: expected rational');return self.a

def asR(v):return v if isinstance(v,R) else R(v)
def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def tr(A):return list(map(list,zip(*A)))

def whitening_checks(d):
    x=d['whitening'];A=[[R(*v) for v in row] for row in x['A']];S=d['forward']['Sigma']
    same(mm(mm(A,S),tr(A)),[[1,0],[0,1]],'WHITENING: A Sigma A^T')
    same(mm(tr(A),A),x['inverse_sigma'],'WHITENING: metric inverse')
    same(mm(S,x['inverse_sigma']),[[1,0],[0,1]],'WHITENING: rational inverse')
    determinant=det(A);same(determinant,R(0,Q(1,5)),'WHITENING: positive oriented Jacobian')
    same((determinant*determinant).rational(),x['determinant_squared'],'WHITENING: determinant squared')
    same(x['determinant_squared']*det(S),1,'WHITENING: density normalization')
    u=[A[0][0],A[1][0]];v=[A[0][1],A[1][1]]
    uv=sum(a*b for a,b in zip(u,v));u2=sum(a*a for a in u);v2=sum(a*a for a in v)
    require(uv.rational()>0,'WHITENING: acute wedge')
    same(((uv*uv)/(u2*v2)).rational(),x['cosine_squared'],'WHITENING: wedge angle')
    same(x['cosine_squared'],Q(4,7),'WHITENING: model angle')

# Laurent monomials in H=2^(p/2), theta, Gamma(p+1), Gamma(p/2+1), p.
def mono(c,*e):return [Q(c)]+list(e)
def monomul(*args):return [__import__('functools').reduce(lambda a,b:a*b,(x[0] for x in args),Q(1))]+[sum(x[i] for x in args) for i in range(1,6)]
def monoinv(x):return [1/x[0]]+[-v for v in x[1:]]

def pc(p):return {m:asR(v) for m,v in p.items() if v}
def pa(*args):
    out=defaultdict(R)
    for a in args:
        for m,v in a.items():out[m]=out[m]+v
    return pc(out)
def ps(a,s):return pc({m:v*s for m,v in a.items()})
def pm(*args):
    out={(0,0,0,0):R(1)}
    for a in args:
        nxt=defaultdict(R)
        for m,v in out.items():
            for n,w in a.items():
                z=tuple(x+y for x,y in zip(m,n));nxt[z]=nxt[z]+v*w
        out=pc(nxt)
    return out

def pp(a,n):return pm(*([a]*n))
def dotpoly(c,s,reflection):
    # z dot R_phi w, or z dot R_phi(conjugate w); variable order x,y,X,Y.
    sign=-1 if reflection else 1
    return pc({(1,0,1,0):c,(0,1,1,0):-sign*s,(1,0,0,1):s,(0,1,0,1):sign*c})
def harmonic_poly(n,offset):
    out={}
    for j in range(1,n+1,2):
        m=[0]*4;m[offset]=n-j;m[offset+1]=j;out[tuple(m)]=R(comb(n,j)*(-1)**((j-1)//2))
    return out

def brownian_checks(d):
    x=d['brownian']
    # Angular integrals: int sin(p phi)=2/p, int sin^2(p phi)=theta/2.
    # Radial substitution r^2/2=s gives 2^(p/2) Gamma(p/2+1);
    # r^2=s gives Gamma(p+1)/2 for the squared profile.
    b=mono(2,-2,-1,-1,0,0)
    I1=monomul(mono(2,0,0,0,0,-1),mono(1,1,0,0,1,0))
    I2=monomul(mono(Q(1,2),0,1,0,0,0),mono(Q(1,2),0,0,1,0,0))
    same(x['b'],b,'BROWNIAN: Bessel leading coefficient')
    same(x['I1'],I1,'BROWNIAN: meander integral normalization')
    same(x['I2'],I2,'BROWNIAN: midpoint integral normalization')
    same(x['k'],monomul(b,I1),'BROWNIAN: survival coefficient')
    same(monomul(x['k'],monoinv(x['I1'])),b,'BROWNIAN: survival times endpoint density')
    same(monomul(b,b,mono(2,2,0,0,0,0),I2),b,'BROWNIAN: midpoint semigroup constant')
    rotations={1:(R(1),R(0)),2:(R(-1),R(0)),3:(R(-Q(1,2)),R(0,Q(1,2))),4:(R(0),R(1)),6:(R(Q(1,2)),R(0,Q(1,2)))}
    for m,(c,s) in rotations.items():
        want=Q(2)**(1-m)*Q(m,factorial(m))
        same(x['reflection_b_pi'][str(m)],want,'BROWNIAN: special-angle b*pi p='+str(m))
        polys=[];ck=R(1);sk=R(0)
        for k in range(m):
            polys.append((dotpoly(ck,sk,False),dotpoly(ck,sk,True)))
            ck,sk=ck*c-sk*s,sk*c+ck*s
        same((ck,sk),(R(1),R(0)),'BROWNIAN: finite reflection rotation')
        for degree in range(m+1):
            value=ps(pa(*(pa(pp(a,degree),ps(pp(b,degree),-1)) for a,b in polys)),Q(1,2*factorial(degree)))
            target={} if degree<m else ps(pm(harmonic_poly(m,0),harmonic_poly(m,2)),want)
            same(value,target,'BROWNIAN: reflection polynomial p='+str(m)+' degree='+str(degree))

def inverse_counting_checks(d):
    x=d['inverse'];a,b,c,e=x['center_coefficients']
    # Formal independent basis L,kappa*log L,kappa*log lambda,log C_A.
    same([a-1,b-1,c+1,e+1],[0,0,0,0],'INVERSE: complete constant centering cancellation')
    same(x['defect_coefficient'],-1,'INVERSE: exact log(1+b/L) defect sign')
    same(x['envelope_factor'],4,'INVERSE: stated error envelope factor')
    require(x['envelope_factor']/2>1,'INVERSE: envelope strict margin')
    x=d['counting']
    same(x['initial_factor'],2,'COUNTING: initial Perron factor')
    same(x['time_shift'],1,'COUNTING: original step shift')
    same(x['growth'],9,'COUNTING: exponential growth')
    same(x['initial_factor']/x['growth']**x['time_shift'],x['leading_factor'],'COUNTING: leading 2/9 factor')
    same(x['terminal_stationary'],d['forward']['stationary'],'COUNTING: terminal stationary normalization')


def provenance():
    d=load('provenance.json')
    keys(d,{'schema','archive','proof_source','public_fixture','scope','report'},'provenance')
    same(d['schema'],'a279571-leading-provenance-v1','SCHEMA: provenance version')
    same(d['archive'],{'role':'byte-identical Report123 finite companion; archived references retain their original context','directory':'legacy','manifest_sha256':ARCHIVE_MANIFEST_HASH,'modified':False},'PROVENANCE: immutable archive boundary')
    require(type(d['archive'].get('modified')) is bool,'SCHEMA: archive modified boolean')
    same(d['proof_source'],{'file':'proof_candidate.md','sha256':PROOF_HASH,'role':'audited analytic source; this recorded digest is not a finite proof certificate'},'PROVENANCE: analytic source boundary')
    same(d['public_fixture'],{'file':'legacy/b279571.txt','sha256':PUBLIC_HASH,'rows':1001,'role':'historical frozen public OEIS b-file; no fresh raw-byte retrieval claimed here','internal_comparison':'legacy/historical_gmp_n0_1000.txt','fresh_gmp_run':False},'PROVENANCE: public/historical distinction')
    require(type(d['public_fixture'].get('rows')) is int and type(d['public_fixture'].get('fresh_gmp_run')) is bool,'SCHEMA: fixture field types')
    same(d['scope'],'Finite identities only: no analytic uniform bounds, harmonic-limit existence, amplitude existence or numerical amplitude digits, correction fits, or effective inverse error rate are certified.','PROVENANCE: finite-check scope')
    same(d['report'],{'file':'../report125.tex','role':'analytic arguments and citations; bytes sealed by the outer package inventory'},'PROVENANCE: report boundary')


def legacy_checks():
    spec=importlib.util.spec_from_file_location('report123_frozen',ROOT/'legacy/verify.py')
    v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
    try:
        v.inventory();d=v.evidence();public=v.provenance();K=v.algebra(d);v.stochastic(d);v.paths(d)
        levels=v.tree_levels(d['ranges']['tree'])
        v.same(levels,v.prefix_levels(d['ranges']['tree']),'ENUMERATION: tree/prefix full-state mismatch')
        v.same(levels[:10],v.brute_levels(d['ranges']['brute']),'ENUMERATION: original avoidance/full-state mismatch')
        v.same([sum(x.values()) for x in levels],public[:len(levels)],'ENUMERATION: published coefficient mismatch')
        for n,level in enumerate(levels[1:],1):v.require(all(a>=1 and b>=0 and a+b<=n and (c!='Q' or a>=2) for a,b,c in level),'DOMAIN: unshifted labels or automatic sum bound')
        v.functional(levels,K);v.endpoint(d,levels);v.inventory()
        return {'tree_max_n':65,'brute_max_n':9,'endpoint_max_n':12,'reversal_max_length':5,'historical_rows':1001,'last_recomputed_coefficient':str(public[65]),'loop_templates':6}
    except v.CheckError as e:raise CheckError('ARCHIVE CHECK: '+str(e)) from e


def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: python3 verify.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:require(output!=ROOT and ROOT not in output.parents,'OUTPUT: path must be outside sealed checks directory')
    inventory();before=snapshot();d=evidence();provenance()
    chain_checks(d);cycle_checks(d);whitening_checks(d);brownian_checks(d);inverse_counting_checks(d)
    old=legacy_checks();inventory();same(snapshot(),before,'SOURCE: verification changed source bytes')
    lines=[
      'strict schema, canonical rational data, closed recursive inventory, immutable Report123 archive',
      'independent transform-derived forward/dual drift, martingale covariance and second-order Poisson correctors',
      'four full return-cycle joint moments, both colors and directions, original-clock covariance normalization',
      'exact radical whitening, wedge angle, oriented Jacobian and lattice density normalization',
      'Brownian integral/semigroup constants and complete reflection polynomials at p=1,2,3,4,6',
      'full inverse constant centering, error-envelope algebra, terminal color and 2/9 counting normalization',
      'original avoidance/full states through n=9, independent tree/prefix full states and public counts through n=65',
      'coordinate/domain, tilt, functional/kernel, six return-loop, endpoint/reversal and historical 1001-row invariants']
    for line in lines:print('PASS: '+line)
    print('LIMIT: finite checks do not certify analytic uniform estimates, existence or digits of the amplitude, or fitted corrections')
    result={'schema':'a279571-leading-finite-results-v1','status':'PASS','ranges':d['ranges'],'exact_arithmetic':'Python standard-library fractions.Fraction, integer polynomials and Q(sqrt(3))','checks':lines,'legacy':old,'cycle_cases':list(d['cycles']),'reflection_angles_p':[1,2,3,4,6],'proof_source_recorded_sha256':PROOF_HASH,'public_table_sha256':PUBLIC_HASH,'fresh_gmp_run':False,'fresh_public_raw_byte_retrieval':False,'analytic_claims_certified_by_finite_checks':False,'amplitude_digits_supplied':False,'source_unchanged':True}
    if output is not None:
        output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (CheckError,OSError,UnicodeError) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
