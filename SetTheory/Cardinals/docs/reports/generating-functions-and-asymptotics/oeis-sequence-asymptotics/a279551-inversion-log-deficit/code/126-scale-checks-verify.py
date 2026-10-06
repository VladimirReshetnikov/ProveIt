#!/usr/bin/env python3
"""Independent finite exact checks for Report126. Standard library; no asymptotic certification."""
import sys
sys.dont_write_bytecode = True
from collections import defaultdict, Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product, combinations
from math import comb, factorial
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent
FILES = frozenset({'README.md', 'verify.py', 'negative_tests.py', 'evidence.json', 'provenance.json', 'manifest.sha256'})
RANGES = {'direct_n':8, 'decorated_n':8, 'renewal_n':24, 'normalized_n':12, 'cycle_b':10, 'bulk_w':12, 'mgf_b':8, 'fill_radius':12, 'floor_start':256, 'floor_end':320, 'log_terms':80}
PROOFS = {
 'square_audit':'ecebc6a0ee4a0e434f4ab9e16fc7629455cd99224f476fc94b5d9363e291d912',
 'logarithmic_proof':'e0b6bd0e87373f78727af99f093597c7f9d46d8f72b6a04bb86fcf9e5c749167',
 'upper_proof':'0ee7385b66f3b3229d012525a9f1007334a96777c34564cedcd922717f8a1fe3',
}
class CheckError(Exception): pass
def require(ok, message):
    if not ok: raise CheckError(message)
def same(a,b,message): require(a==b,message)
def unique(pairs):
    result={}
    for k,v in pairs:
        require(k not in result,'JSON: duplicate key '+k); result[k]=v
    return result

def load(name):
    try:
        return json.loads((ROOT/name).read_text(encoding='utf-8'),object_pairs_hook=unique,
                          parse_constant=lambda _: (_ for _ in ()).throw(CheckError('JSON: nonfinite number')))
    except (ValueError, UnicodeError) as e: raise CheckError('JSON: invalid '+name) from e

def keys(obj, expected, path): require(type(obj) is dict and set(obj)==set(expected),'SCHEMA: '+path+' keys')
def integer(v,path): require(type(v) is int,'SCHEMA: '+path+' integer'); return v
def rational(v,path):
    require(type(v) is str and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?',v) is not None,'SCHEMA: '+path+' canonical rational')
    value=F(v); same(str(value),v,'SCHEMA: '+path+' canonical rational'); return value

def snapshot(root=ROOT):
    return {p.relative_to(root).as_posix():('directory' if p.is_dir() else sha256(p.read_bytes()).hexdigest()) for p in root.rglob('*')}

def inventory():
    paths=list(ROOT.rglob('*'))
    require(not any(p.is_symlink() for p in paths),'INVENTORY: symlink forbidden')
    require(not any(p.is_dir() for p in paths),'INVENTORY: unexpected directory')
    same({p.relative_to(ROOT).as_posix() for p in paths},FILES,'INVENTORY: unexpected or missing member')
    require(all(p.is_file() for p in paths),'INVENTORY: nonregular member')
    entries={}
    for line in (ROOT/'manifest.sha256').read_text(encoding='ascii').splitlines():
        require(re.fullmatch(r'[0-9a-f]{64}  [A-Za-z0-9_.-]+',line) is not None,'MANIFEST: malformed entry')
        digest,name=line.split('  ')
        require(name not in entries,'MANIFEST: duplicate member'); entries[name]=digest
    same(set(entries),FILES-{'manifest.sha256'},'MANIFEST: closed inventory mismatch')
    for name,digest in entries.items(): same(sha256((ROOT/name).read_bytes()).hexdigest(),digest,'HASH: '+name)

def schema():
    d=load('evidence.json')
    keys(d,{'schema','ranges','cutoffs','floor_extra','floor_samples','classes','barrier','inverse','scope'},'evidence')
    same(d['schema'],'commitment-scale-finite-v1','SCHEMA: evidence version')
    keys(d['ranges'],RANGES,'ranges')
    for k,v in d['ranges'].items():integer(v,'ranges.'+k)
    same(d['ranges'],RANGES,'RANGE: mandatory coverage changed')
    for name in ('cutoffs','floor_extra'):
        require(type(d[name]) is list,'SCHEMA: '+name+' array')
        for v in d[name]:integer(v,name+' entry')
    same(d['cutoffs'],[2,4,7],'RANGE: boundary cutoffs changed')
    same(d['floor_extra'],[512,1024,4096,10000,1000000,100000000],'RANGE: floor sample changed')
    require(type(d['floor_samples']) is list and len(d['floor_samples'])==2,'SCHEMA: floor_samples shape')
    for row in d['floor_samples']:
        require(type(row) is list and len(row)==4,'SCHEMA: floor_samples row')
        for value in row:integer(value,'floor_samples entry')
    keys(d['classes'],{'759','247'},'classes')
    for kind,c in d['classes'].items():
        keys(c,{'oeis','mu','x','y','alpha','terminal_cap','counts','decorated_counts','factor_prefactor','A','R','critical','endpoint_exponent'},'classes.'+kind)
        for key in ('mu','x','endpoint_exponent'):integer(c[key],kind+'.'+key)
        require(c['terminal_cap'] is None or type(c['terminal_cap']) is int,'SCHEMA: '+kind+'.terminal_cap integer or null')
        for key in ('y','alpha','factor_prefactor'): c[key]=rational(c[key],kind+'.'+key)
        for key in ('counts','decorated_counts'):
            require(type(c[key]) is list and len(c[key])==9,'SCHEMA: '+kind+'.'+key+' shape')
            for value in c[key]:integer(value,kind+'.'+key+' entry')
        for key in ('A','R'):
            keys(c[key],{'numerator','denominator'},kind+'.'+key)
            for side in ('numerator','denominator'):
                require(type(c[key][side]) is dict and bool(c[key][side]),'SCHEMA: '+kind+'.'+key+'.'+side+' polynomial')
                converted={}
                for monomial,value in c[key][side].items():
                    require(re.fullmatch(r'(?:0|[1-9][0-9]*),(?:0|[1-9][0-9]*)',monomial) is not None,'SCHEMA: polynomial monomial')
                    coeff=rational(value,kind+'.'+key+'.'+side)
                    require(coeff!=0,'SCHEMA: polynomial zero term')
                    converted[tuple(map(int,monomial.split(',')))]=coeff
                c[key][side]=converted
        keys(c['critical'],{'A0','R0','d_lambda_logR','d_lambda2_logR','d_eta_logR','boundary_mass'},kind+'.critical')
        c['critical']={k:rational(v,kind+'.critical.'+k) for k,v in c['critical'].items()}
    keys(d['barrier'],{'first_coefficients','second_coefficients'},'barrier')
    for k,size in [('first_coefficients',2),('second_coefficients',3)]:
        require(type(d['barrier'][k]) is list and len(d['barrier'][k])==size,'SCHEMA: barrier.'+k+' shape')
        d['barrier'][k]=[rational(v,'barrier.'+k) for v in d['barrier'][k]]
    keys(d['inverse'],{'lower_margin_sign','upper_margin_sign','lower_rounding','upper_rounding','correction_sign','deficit_power','log_power','conjectured_power'},'inverse')
    for k in ('lower_margin_sign','upper_margin_sign','correction_sign'):integer(d['inverse'][k],'inverse.'+k)
    for k in ('deficit_power','log_power','conjectured_power'):d['inverse'][k]=rational(d['inverse'][k],'inverse.'+k)
    keys(d['scope'],{'finite_only','all_size_bounds_certified','effective_constants','effective_onset','asymptotic_equivalent','fitted_amplitudes'},'scope')
    for value in d['scope'].values():require(type(value) is bool,'SCHEMA: scope boolean')
    same(d['scope'],{'finite_only':True,'all_size_bounds_certified':False,'effective_constants':False,'effective_onset':False,'asymptotic_equivalent':False,'fitted_amplitudes':False},'SCOPE: analytic limitations')
    return d

def provenance():
    p=load('provenance.json')
    keys(p,{'schema','primary_source','analytic_sources','sequence_fixtures','implementation','verification_scope'},'provenance')
    same(p['schema'],'commitment-scale-provenance-v1','PROVENANCE: version')
    same(p['primary_source'],{'authors':'Nathan Britt and Nicholas Beaton','title':'Completing the enumeration of inversion sequences avoiding triples of relations','version':'arXiv:2512.21943v3','url':'https://arxiv.org/html/2512.21943v3','locations':['sections 3.8-3.9','equations 3.41-3.45','Appendix A'],'source_inspection':'2026-10-02, recorded in supplied independent audits; this checker performs no network retrieval'},'PROVENANCE: primary source')
    same(p['analytic_sources'],PROOFS,'PROVENANCE: frozen analytic sources')
    keys(p['sequence_fixtures'],{'external_fixtures','origin','fresh_external_retrieval'},'sequence_fixtures')
    require(type(p['sequence_fixtures']['fresh_external_retrieval']) is bool,'SCHEMA: provenance freshness boolean')
    same(p['sequence_fixtures'],{'external_fixtures':[],'origin':'Internal exact recomputation from direct avoidance and separately implemented trees; no OEIS coefficient fixture imported','fresh_external_retrieval':False},'PROVENANCE: sequence fixture origin')
    same(p['implementation'],'Independent standard-library implementation; no producer or prior-audit program is imported, executed, or read by verify.py','PROVENANCE: implementation independence')
    same(p['verification_scope'],'Finite regression checks and exact algebra only; source hashes identify mathematical inputs, not finite certificates of their all-size theorems','PROVENANCE: analytic boundary')

# Sparse polynomial/rational-function algebra over Q[u,v], u=exp(lambda), v=exp(eta).
def pc(v):return {(0,0):F(v)} if v else {}
def padd(a,b):
    c=dict(a)
    for k,v in b.items():c[k]=c.get(k,F(0))+v
    return {k:v for k,v in c.items() if v}
def pscale(a,s):return {k:v*s for k,v in a.items() if v*s}
def pmul(a,b):
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():c[(i+k,j+l)]=c.get((i+k,j+l),F(0))+v*w
    return {k:v for k,v in c.items() if v}
def ppow(a,n):
    result=pc(1)
    for _ in range(n):result=pmul(result,a)
    return result
class RF:
    def __init__(self,n,d=None):self.n=n if type(n) is dict else pc(n);self.d=pc(1) if d is None else d
    def __add__(self,b):
        b=b if isinstance(b,RF) else RF(b)
        return RF(padd(pmul(self.n,b.d),pmul(b.n,self.d)),pmul(self.d,b.d))
    __radd__=__add__
    def __neg__(self):return RF(pscale(self.n,-1),self.d)
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        b=b if isinstance(b,RF) else RF(b)
        return RF(pmul(self.n,b.n),pmul(self.d,b.d))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=b if isinstance(b,RF) else RF(b)
        return RF(pmul(self.n,b.d),pmul(self.d,b.n))
    def __pow__(self,n):return RF(ppow(self.n,n),ppow(self.d,n))
    def equals(self,b):return pmul(self.n,b.d)==pmul(b.n,self.d)
    def at_one(self):
        require(sum(self.d.values())!=0,'ALGEBRA: denominator at critical point')
        return sum(self.n.values())/sum(self.d.values())
    def D(self,axis):
        def derivative(p):return {ij:c*ij[axis] for ij,c in p.items() if ij[axis]}
        return RF(padd(pmul(derivative(self.n),self.d),pscale(pmul(self.n,derivative(self.d)),-1)),pmul(self.d,self.d))

U=RF({(1,0):F(1)}); V=RF({(0,1):F(1)})

def catalan(n):return comb(2*n,n)//(n+1)
def choose(n,k):return comb(n,k) if 0<=k<=n else 0

def algebra(d):
    outcomes={}
    for kind,c in d['classes'].items():
        j=int(kind); mu,x=c['mu'],c['x']
        same((mu,x,c['y'],c['alpha'],c['oeis']),(9,3,F(1,2),F(3,2),'A279556') if j==759 else (8,2,F(1,3),F(4,3),'A279551'),'MODEL: '+kind+' critical parameters and identity')
        same(c['terminal_cap'],None if j==759 else 2,'MODEL: '+kind+' terminal extraction')
        same(F(x,mu)+F(x,mu)/c['y'],1,'MODEL: '+kind+' bulk row')
        z=RF(1)/(x*U); t=(x*U*V)/mu
        claimed_A=RF(c['A']['numerator'],c['A']['denominator']);claimed_R=RF(c['R']['numerator'],c['R']['denominator'])
        # Independent construction: exact l generating series and first-return w series.
        cases=0
        for b in range(d['ranges']['mgf_b']+1):
            lsum=(z**b)/(RF(1)-z)**(b+1) if j==759 else (z**b)*(RF(1)+z)**(b+1)
            wsum=RF(1) if b==0 else (t/(RF(1)-t))**b
            direct=(V/mu)*catalan(b)*lsum*wsum
            claimed=claimed_A*F(catalan(b),4**b)*(claimed_R**b)
            require(direct.equals(claimed),'MGF: '+kind+' joint identity b='+str(b));cases+=1
        # Generator identities are checked coefficientwise independently at finite orders.
        for b in range(9):
            expansion=[1]+[0]*24
            for _ in range(b+1):
                if j==759:
                    running=0;next_expansion=[]
                    for value in expansion:
                        running+=value;next_expansion.append(running)
                    expansion=next_expansion
                else:expansion=[expansion[n]+(expansion[n-1] if n else 0) for n in range(25)]
            for ell in range(25):
                coeff=choose(ell,b) if j==759 else choose(b+1,ell-b)
                expanded=expansion[ell-b] if ell>=b else 0
                same(coeff,expanded,'MGF: commitment generating coefficient')
        R0=claimed_R.at_one();dl=claimed_R.D(0).at_one()/R0
        crit={'A0':claimed_A.at_one(),'R0':R0,'d_lambda_logR':dl,'d_lambda2_logR':claimed_R.D(0).D(0).at_one()/R0-dl*dl,'d_eta_logR':claimed_R.D(1).at_one()/R0,'boundary_mass':F(x,mu)+2*claimed_A.at_one()}
        for k,v in crit.items():same(c['critical'][k],v,'CRITICAL: '+kind+' '+k)
        require(crit['boundary_mass']<1,'CRITICAL: substochastic boundary')
        pref=F(1,9) if j==759 else F(3,16)
        same(c['factor_prefactor'],pref,'CYCLE: '+kind+' factor prefactor')
        same(c['endpoint_exponent'],-1,'NORMALIZATION: '+kind+' inverse endpoint tilt')
        outcomes[kind]={'joint_mgf_polynomial_identities':cases,'includes_b0_without_bulk':True,'critical':{k:str(v) for k,v in crit.items()}}
    # Exact differentiation of t^a (log t)^b, using half-integer exponents.
    def deriv(poly):
        result={}
        for (a,b),c in poly.items():
            for key,v in [((a-1,b),a*c),((a-1,b-1),b*c)]:result[key]=result.get(key,F(0))+v
        return {k:v for k,v in result.items() if v}
    f={(F(1,2),F(1,2)):F(1)};fp=deriv(f);fpp=deriv(fp)
    fc=d['barrier']['first_coefficients'];sc=d['barrier']['second_coefficients']
    claimed_fp={(F(-1,2),F(1,2)):fc[0],(F(-1,2),F(-1,2)):fc[1]}
    claimed_fpp={(F(-3,2),F(1,2)):sc[0],(F(-3,2),F(-1,2)):sc[1],(F(-3,2),F(-3,2)):sc[2]}
    same(fp,{k:v for k,v in claimed_fp.items() if v},'BARRIER: first derivative algebra')
    same(fpp,{k:v for k,v in claimed_fpp.items() if v},'BARRIER: second derivative algebra')
    require(all(v<0 for v in fpp.values()),'BARRIER: strict concavity sign')
    # Positivity of log(t) for t>=2 makes every nonzero f'' monomial negative.
    inv=d['inverse']
    same((inv['lower_margin_sign'],inv['upper_margin_sign']),(-1,1),'INVERSE: strict margin directions')
    same((inv['lower_rounding'],inv['upper_rounding']),('ceil','ceil'),'INVERSE: ceiling directions')
    same(inv['correction_sign'],1,'INVERSE: positive correction')
    same((inv['deficit_power'],inv['log_power'],inv['conjectured_power']),(F(1,3),F(2,3),F(3,8)),'INVERSE: scale exponents')
    # Lower margin dL-c <0 and upper margin DL-C>0 are algebraic, not calibrated constants.
    margins=0
    for L in (F(3,2),F(2),F(5,2)):
        for c,C in ((F(1),F(3)),(F(2),F(5)),(F(1,7),F(11,3))):
            small=c/(2*L);large=2*C/L
            require(small*L-c<0 and large*L-C>0,'INVERSE: algebraic margins')
            for s in (F(5,2),F(13,3),F(20)):
                for delta in (F(1,4),F(2),F(11,3)):
                    b=s+delta;ceil=-((-b.numerator)//b.denominator)
                    for n in range(max(0,ceil-2),ceil+2):same(n<ceil,F(n)<b,'INVERSE: exact strict ceiling equivalence')
            margins+=1
    require(inv['conjectured_power']-inv['deficit_power']==F(1,24),'INVERSE: exponent gap')
    return {'classes':outcomes,'barrier_derivatives_and_sign':True,'inverse_margin_cases':margins,'asymptotic_implications_certified_by_finite_checks':False}

# Succession-rule counts, implemented as integer transition accumulation.
def multiplicity(kind,ell,b):return catalan(b)*(choose(ell,b) if kind==759 else choose(b+1,ell-b))
def raw_layers(kind,N,cap=None):
    layers=[{(0,0):1}]
    for n in range(N):
        nxt=defaultdict(int)
        for (p,c),count in layers[-1].items():
            edges=[(p+1,c,1)]
            if c:edges.append((p+1,c-1,1))
            else:
                edges += [(p-ell,b,multiplicity(kind,ell,b)) for ell in range(p) for b in range(ell+1)]
            for h,b,m in edges:
                if m and (cap is None or b!=0 or h<cap):nxt[(h,b)]+=count*m
        layers.append(dict(nxt))
    return layers

def normalized_layers(kind,N,mu,x,y):
    # Direct propagation of individual tilted edge masses, independently of raw counts.
    layers=[{(0,0):F(1)}]
    for _ in range(N):
        nxt=defaultdict(F)
        for (p,c),mass in layers[-1].items():
            nxt[(p+1,c)]+=mass*F(x,mu)
            if c:nxt[(p+1,c-1)]+=mass*F(x,mu)/y
            else:
                for b in range(p):
                    for ell in range(b,p):
                        m=multiplicity(kind,ell,b)
                        if m:nxt[(p-ell,b)]+=mass*F(m,mu)*F(x)**(-ell)*y**b
        layers.append(dict(nxt))
    return layers

# Renewal implementation uses repeated convolution of a finite first-return duration law.
def return_words(b,remaining):
    if b==0:return {0:1}
    # Last symbol fulfills the last commitment; enumerate by Pascal recurrence, not comb.
    live={b:1};out={}
    for w in range(1,remaining+1):
        nxt=defaultdict(int)
        for c,count in live.items():
            nxt[c]+=count
            if c==1:out[w]=out.get(w,0)+count
            else:nxt[c-1]+=count
        live=nxt
    return out

def renewal_layers(kind,N,cap=None):
    layers=[defaultdict(int) for _ in range(N+1)];layers[0][0]=1
    bulk={b:return_words(b,N) for b in range(N+1)}
    for n in range(N):
        for p,count in list(layers[n].items()):
            if cap is None or p+1<cap:layers[n+1][p+1]+=count
            # Enumerate commitment amount and time, then allowed removals.
            for b in range(p):
                for w,paths in bulk[b].items():
                    if n+1+w>N:continue
                    for ell in range(b,p):
                        m=multiplicity(kind,ell,b);h=p-ell+w
                        if m and (cap is None or h<cap):layers[n+1+w][h]+=count*m*paths
    return [dict(row) for row in layers]

def avoids(seq,kind):
    for a,b,c in combinations(seq,3):
        if a<=b and a>=c and (kind==247 or b!=c):return False
    return True

def direct_sets(N,kind):
    # Explicit product over independent inversion-sequence coordinates; no tree pruning.
    return [{s for s in product(*(range(i+1) for i in range(n))) if avoids(s,kind)} for n in range(N+1)]

def zeros(seq):return next((i for i,v in enumerate(seq) if v),len(seq))
def relabel(word):
    order={v:i for i,v in enumerate(sorted(set(word)))}
    return tuple(order[v] for v in word)
@lru_cache(None)
def pending_orders(kind,width):
    prohibited={(1,0,1),(0,0,1),(1,0,2)}|({(0,0,0)} if kind==247 else set())
    schedules=[]
    for groups in range(1,width+1):
        for word in product(range(groups),repeat=width):
            if len(set(word))!=groups:continue
            if any(relabel(t) in prohibited for t in combinations(word,3)):continue
            schedules.append(tuple(frozenset(i for i,v in enumerate(word) if v==g) for g in range(groups)))
    return tuple(schedules)

def decorated_layers(kind,N,brute,raw):
    current={((),()):1};counts=[];word_tests=0
    for n in range(N+1):
        labels=Counter();terminal=[]
        for (seq,schedule),ways in current.items():
            require(ways==1,'DECORATED: repeated decorated history')
            p=zeros(seq);labels[(p,len(schedule))]+=ways
            if not schedule and (kind==759 or p<=2):terminal.append(seq)
        same(dict(labels),raw[n],'DECORATED: full label distribution')
        same(len(terminal),len(set(terminal)),'DECORATED: repeated completed sequence')
        same(set(terminal),brute[n],'DECORATED: direct terminal set')
        counts.append(len(current))
        if n==N:break
        nxt=defaultdict(int)
        for (seq,schedule),ways in current.items():
            p=zeros(seq)
            candidates=[(frozenset(),schedule)]
            if schedule:candidates.append((schedule[0],schedule[1:]))
            else:
                for size in range(1,p+1):
                    if kind==759 or size<=2:candidates.append((frozenset(range(p-size,p)),()))
                # Single chosen pivot left of a rightmost selected suffix.
                for pivot in range(p):
                    for suffix in range(p-pivot-1):
                        if kind==247 and suffix>1:continue
                        gap=tuple(range(pivot+1,p-suffix))
                        for blocks in pending_orders(kind,len(gap)):
                            schedule2=tuple(frozenset(gap[t] for t in block) for block in blocks)
                            candidates.append((frozenset({pivot}|set(range(p-suffix,p))),schedule2))
            for selected,next_schedule in candidates:
                child=(0,)+tuple(value+1 if value else int(i in selected) for i,value in enumerate(seq))
                # Physical reverse rule recovers the unique predecessor even from unfinished states.
                same(tuple(max(v-1,0) for v in child[1:]),seq,'DECORATED: physical inverse')
                shifted=tuple(frozenset(i+1 for i in block) for block in next_schedule)
                nxt[(child,shifted)]+=ways
        current=dict(nxt)
    for width in range(1,N-1):
        hist=Counter(map(len,pending_orders(kind,width)))
        for b in range(1,width+1):
            expected=catalan(b)*(choose(width-1,b-1) if kind==759 else choose(b,width-b))
            same(hist.get(b,0),expected,'DECORATED: onto word multiplicity');word_tests+=1
    return counts,word_tests

def model_checks(d):
    result={}
    for kind,c in d['classes'].items():
        j=int(kind);raw=raw_layers(j,d['ranges']['renewal_n']);direct=direct_sets(d['ranges']['direct_n'],j)
        prefix=[]
        for n,objects in enumerate(direct):
            actual=sum(v for (p,b),v in raw[n].items() if b==0 and (j==759 or p<=2))
            same(actual,len(objects),'MODEL: '+kind+' direct avoidance count')
            prefix.append(actual)
            for seq in objects:require(avoids(seq+(n,),j),'INJECTION: append-largest preservation')
            if n:require(avoids(tuple(range(n))+(n-1,),j),'INJECTION: strictness witness')
        same(prefix,c['counts'],'MODEL: '+kind+' frozen internal counts')
        threshold_cases=0
        tilted=normalized_layers(j,d['ranges']['normalized_n'],c['mu'],c['x'],c['y']);tilt_cases=0
        for n,layer in enumerate(tilted):
            exact={(p,b):F(count*c['x']**p,c['mu']**n)*c['y']**b for (p,b),count in raw[n].items()}
            same(layer,exact,'NORMALIZATION: propagated endpoint telescoping');tilt_cases+=len(layer)
        for n,layer in enumerate(raw):
            qtotal=sum(F(count*c['x']**p,c['mu']**n)*c['y']**b for (p,b),count in layer.items())
            require(qtotal<=1,'NORMALIZATION: finite substochastic total')
            target=sum(count for (p,b),count in layer.items() if b==0 and (j==759 or p<=2))
            require(target<=c['mu']**n,'NORMALIZATION: finite target upper bound')
        for n in range(2,len(prefix)):
            for threshold in (F(prefix[n]),F(prefix[n-1]+prefix[n],2)):
                hit=next(k for k,value in enumerate(prefix) if value>=threshold)
                require((hit==0 or prefix[hit-1]<threshold) and threshold<=prefix[hit],'INVERSE: threshold bracketing')
                lower=next(k for k in range(hit+1) if c['mu']**k>=threshold)
                require(lower<=hit,'INVERSE: finite global bound direction');threshold_cases+=1
        decorated,word_tests=decorated_layers(j,d['ranges']['decorated_n'],direct,raw)
        same(decorated,c['decorated_counts'],'DECORATED: '+kind+' frozen pair counts')
        distribution_cases=0;digests={}
        for cutoff in [None]+d['cutoffs']:
            rows=raw if cutoff is None else raw_layers(j,d['ranges']['renewal_n'],cutoff)
            renew=renewal_layers(j,d['ranges']['renewal_n'],cutoff)
            for n,(layer,boundary) in enumerate(zip(rows,renew)):
                same({p:v for (p,b),v in layer.items() if b==0},boundary,'RENEWAL: '+kind+' duration-resolved distribution')
                # Terminal normalization is checked endpoint by endpoint in the original clock.
                for p,count in boundary.items():
                    qweight=F(count*c['x']**p,c['mu']**n)
                    same(qweight*F(c['x'])**(c['endpoint_exponent']*p),F(count,c['mu']**n),'NORMALIZATION: fixed terminal conversion')
                distribution_cases+=1
            serial=[sorted(row.items()) for row in renew]
            digests[str(cutoff)]=sha256(json.dumps(serial,separators=(',',':')).encode()).hexdigest()
        require(sum(raw[3].values())>prefix[3],'MODEL: auxiliary versus terminal distinction')
        # Explicit fixed access/termination pieces end at heights independent of staircase top.
        for p0 in range(2,13):
            q=F(c['x'],c['mu'])**p0;n=p0;p=p0
            if j==247:
                for _ in range(p0-2):q*=F(1,c['mu']*c['x']);n+=1;p-=1
            same(q*F(c['x'])**(-p),F(1,c['mu']**n),'NORMALIZATION: fixed access termination')
        result[kind]={'counts_n0_8':prefix,'decorated_pairs_n0_8':decorated,'onto_word_cases':word_tests,'duration_boundary_distributions':distribution_cases,'distribution_sha256':digests,'all_completed_physical_endpoints_unique':True,'finite_inverse_threshold_cases':threshold_cases,'substochastic_full_layers':len(raw),'propagated_endpoint_telescoping_cases':tilt_cases}
    return result

def cycle_checks(d):
    answer={};bulk_cases=0
    for b in range(1,7):
        got=return_words(b,d['ranges']['bulk_w'])
        for w in range(b,d['ranges']['bulk_w']+1):
            literal=sum(1 for word in product((0,1),repeat=w) if word[-1]==1 and sum(word)==b)
            same(got.get(w,0),literal,'CYCLE: independent first return enumeration')
            same(literal,comb(w-1,b-1),'CYCLE: first return binomial count');bulk_cases+=1
    for kind,c in d['classes'].items():
        j=int(kind);tested=0;zero=0
        for b in range(1,d['ranges']['cycle_b']+1):
            for ell in range(b,3*b+3):
                for w in range(b,2*b+4):
                    raw=F(multiplicity(j,ell,b)*choose(w-1,b-1),c['mu']**(w+1))*F(c['x'])**(w-ell)
                    q=F(2,3) if j==759 else F(3,4)
                    nb=choose(w-1,b-1)*q**b*(1-q)**(w-b)
                    if j==759:factor=F(catalan(b),4**b)*F(ell,b)*choose(ell-1,b-1)*q**b*(1-q)**(ell-b)*nb*c['factor_prefactor']
                    else:
                        r=ell-b
                        bn=choose(b+1,r)*F(1,3)**r*F(2,3)**(b+1-r)
                        factor=F(catalan(b),4**b)*bn*nb*c['factor_prefactor']
                    same(raw,factor,'CYCLE: '+kind+' negative-binomial factorization');tested+=1;zero+=int(raw==0)
        answer[kind]={'exact_factorizations':tested,'outside_support_zero_cases':zero}
    return {'classes':answer,'literal_first_return_cases':bulk_cases}

# Rigorous log intervals from integral of geometric series, with binary reduction.
@lru_cache(None)
def log_interval_integer(n,terms=80):
    require(type(n) is int and n>=1,'FLOOR: log domain')
    power=n.bit_length()-1; reduced=F(n,2**power)
    def atanh_bounds(v):
        z=(v-1)/(v+1); z2=z*z; term=z;total=F(0)
        for j in range(terms):total+=term/F(2*j+1);term*=z2
        low=2*total;tail=2*term/F(2*terms+1)/(1-z2)
        return low,low+tail
    lo,hi=atanh_bounds(reduced);a,b=atanh_bounds(F(2))
    return lo+power*a,hi+power*b

def floor_scaled_log(k,multiplier,terms):
    lo,hi=log_interval_integer(k+1,terms);lo*=multiplier;hi*=multiplier
    a=lo.numerator//lo.denominator;b=hi.numerator//hi.denominator
    same(a,b,'FLOOR: rational enclosure crosses integer')
    require(0<=hi-lo<F(1,10**30),'FLOOR: certificate width')
    return a

def fill(L,R,N):
    require(0<R<L and N>=F(L*L-R*R,2*R),'FILL: hypotheses')
    A,B=L-R,L+R;m=(N+B-1)//B;excess=N-m*A
    require(0<=excess<=m*2*R,'FILL: interval capacity')
    q,r=divmod(excess,2*R)
    # Run-length encoded composition supports huge exact N without allocation.
    parts=[(B,q),(A+r,int(r>0)),(A,m-q-int(r>0))]
    require(all(count>=0 and (count==0 or A<=length<=B) for length,count in parts),'FILL: legal summands')
    same(sum(length*count for length,count in parts),N,'FILL: exact sum')
    same(sum(count for length,count in parts),m,'FILL: exact summand count')
    return m

def floor_filling_checks(d):
    fill_cases=0
    for R in range(1,d['ranges']['fill_radius']+1):
        for L in range(R+1,5*R+2):
            threshold=(L*L-R*R+2*R-1)//(2*R)
            for N in range(threshold,threshold+2*(L+R)+1):fill(L,R,N);fill_cases+=1
    ks=list(range(d['ranges']['floor_start'],d['ranges']['floor_end']+1))+d['floor_extra']
    certificates=[];support=0;assemblies=0
    for k in ks:
        p=floor_scaled_log(k,k*k,d['ranges']['log_terms']);pp=floor_scaled_log(k+1,(k+1)**2,d['ranges']['log_terms']);R=floor_scaled_log(k,k,d['ranges']['log_terms']);b=p//4;delta=pp-p
        require(delta>0,'STAIRCASE: increasing heights')
        certificates.append([k,p,pp,R])
        for kind,c in d['classes'].items():
            a=c['alpha'];l=(a*b+F(1,2)).numerator//(a*b+F(1,2)).denominator
            require(b>=1 and l<=p-1,'STAIRCASE: geometric support')
            for departure,w,target in [(p,l+delta,pp),(pp,l-delta,p)]:
                require(w>=b and l>=b and (kind=='759' or l<=2*b+1),'STAIRCASE: stage support')
                same(departure-l+w,target,'STAIRCASE: exact endpoint')
                require(abs(l-a*b)<=F(1,2) and abs(w-a*b)<=F(b,12),'STAIRCASE: moderate window')
                support+=1
            same((l+delta+1)+(l-delta+1),2*l+2,'STAIRCASE: signed duration cancellation')
            for v in (l-R,l,l+R):
                require(b<=v<=p-1 and (kind=='759' or v<=2*b+1),'STAIRCASE: plateau support')
                require(abs(v-a*b)<=F(b,12),'STAIRCASE: plateau moderate window')
                same(p-v+v,p,'STAIRCASE: plateau endpoint');support+=1
            L=l+1;threshold=(L*L-R*R+2*R-1)//(2*R)
            for N in (threshold,threshold+1,threshold+2*R+1,10**30+threshold):fill(L,R,N);fill_cases+=1
    same([certificates[0],certificates[-1]],d['floor_samples'],'FLOOR: claimed exact samples')
    # Exact ascending/filling/descending lengths; no assertion of an effective all-n onset.
    start=d['ranges']['floor_start'];p0=floor_scaled_log(start,start*start,d['ranges']['log_terms'])
    for top in (257,258,260,264):
        p=floor_scaled_log(top,top*top,d['ranges']['log_terms']);R=floor_scaled_log(top,top,d['ranges']['log_terms'])
        for kind,c in d['classes'].items():
            alpha=c['alpha'];ls=[]
            for k in range(start,top):
                pk=floor_scaled_log(k,k*k,d['ranges']['log_terms']);b=pk//4
                z=alpha*b+F(1,2);ls.append(z.numerator//z.denominator)
            z=alpha*(p//4)+F(1,2);L=z.numerator//z.denominator+1;T=sum(2*l+2 for l in ls);fixed=p0 if kind=='759' else 2*p0-2
            threshold=(L*L-R*R+2*R-1)//(2*R)
            for offset in (0,1,2*R+3,1234567):
                N=threshold+offset;fill(L,R,N);n=fixed+T+N
                same(n-fixed-T,N,'ASSEMBLY: exact target length');assemblies+=1
    return {'integer_fill_cases':fill_cases,'floor_parameter_values':len(ks),'floor_certificates_sha256':sha256(json.dumps(certificates,separators=(',',':')).encode()).hexdigest(),'floor_selected_certificates':[certificates[0],certificates[-1]],'log_series_terms':d['ranges']['log_terms'],'staircase_and_plateau_cases':support,'whole_length_assemblies':assemblies,'finite_k_values_do_not_certify_uniform_onset':True}

def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: python3 verify.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:require(output!=ROOT and ROOT not in output.parents,'OUTPUT: path must be outside sealed checks directory')
    inventory();before=snapshot();d=schema();provenance()
    result={'schema':'commitment-scale-result-v1','status':'PASS','ranges':RANGES,'scope':d['scope'],'algebra':algebra(d),'cycles':cycle_checks(d),'floor_and_filling':floor_filling_checks(d),'models':model_checks(d)}
    same(snapshot(),before,'IMMUTABILITY: checker changed sealed sources')
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if output is not None:output.write_text(encoded,encoding='utf-8')
    print('PASS: Report126 independent finite exact checks')
    return result

if __name__=='__main__':
    try:main()
    except CheckError as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
