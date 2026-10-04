#!/usr/bin/env python3
"""Independent, standard-library-only checker for data-only polynomial output.

No source packet is imported or executed. No counter program, physical process,
saved schedule, or Lean program is evaluated. Acceptance sets are declared data.
Interpolation is reconstructed over Fraction using synthetic division of the
full node polynomial, rather than importing the source's interpolation routine.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import sys

PROOF_SHA = "233b0f67ce13e81a41132017214db5b34d10c965cd9a3ef56d1cbc9d280ac33c"
MANIFEST_SHA = "cc8a653802570dac6744cc00d490213f34d0d6604a1bd74588173724895a7a55"
NATIVE_NAMES = ["A", "B", "j", "r", "s"]
DIRECT = ["o", "w", "M", "g", "x", "y", "u", "v", "z", "t", "qb", "qv", "J"]
SHIFT2 = ["alpha_plus", "beta_plus"]
NATURAL = ["dwb", "dwk", "dyk", "a1", "a2", "s1", "s2", "t1", "t2", "rho1", "rho2"]
LEAVES = DIRECT + SHIFT2 + NATURAL


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Ring:
    def __init__(self, names):
        self.names = list(names)
        require(len(set(names)) == len(names), "duplicate variable names")
        self.zero = (0,) * len(names)

    def constant(self, c):
        return P(self, {self.zero: c} if c else {})

    def var(self, name):
        e = list(self.zero)
        e[self.names.index(name)] = 1
        return P(self, {tuple(e): 1})


class P:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {e: c for e, c in terms.items() if c}

    def coerce(self, other):
        if isinstance(other, P):
            require(other.ring is self.ring, "mixed polynomial rings")
            return other
        require(type(other) is int, "noninteger polynomial coefficient")
        return self.ring.constant(other)

    def __add__(self, other):
        other = self.coerce(other)
        q = self.terms.copy()
        for e, c in other.terms.items():
            q[e] = q.get(e, 0) + c
        return P(self.ring, q)

    __radd__ = __add__

    def __neg__(self):
        return P(self.ring, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        q = {}
        for a, c in self.terms.items():
            for b, d in other.terms.items():
                e = tuple(x + y for x, y in zip(a, b))
                q[e] = q.get(e, 0) + c * d
        return P(self.ring, q)

    __rmul__ = __mul__

    def __pow__(self, k):
        require(type(k) is int and k >= 0, "invalid exponent")
        ans, base = self.ring.constant(1), self
        while k:
            if k & 1:
                ans = ans * base
            base = base * base
            k //= 2
        return ans

    def at(self, values):
        if isinstance(values, dict):
            values = [values[n] for n in self.ring.names]
        require(len(values) == len(self.ring.names), "wrong assignment arity")
        powers = [{0: 1} for _ in values]
        total = 0
        for e, c in self.terms.items():
            term = c
            for i, k in enumerate(e):
                if k:
                    if k not in powers[i]:
                        powers[i][k] = values[i] ** k
                    term *= powers[i][k]
            total += term
        return total

    def degree(self):
        return max(map(sum, self.terms), default=-1)

    def norm(self):
        return sum(abs(c) for c in self.terms.values())

    def serial(self):
        return [{"exponents": list(e), "coefficient": str(c)}
                for e, c in sorted(self.terms.items())]


def dense_times_linear(v, root):
    out = [0] * (len(v) + 1)
    for i, c in enumerate(v):
        out[i] -= root * c
        out[i + 1] += c
    return out


def divide_at_root(v, root):
    out = [0] * (len(v) - 1)
    out[-1] = v[-1]
    for k in range(len(out) - 2, -1, -1):
        out[k] = v[k + 1] + root * out[k + 1]
    require(v[0] + root * out[0] == 0, "synthetic division remainder")
    return out


def dense_at(v, x):
    acc = 0
    for c in reversed(v):
        acc = acc * x + c
    return acc


def interpolate(T):
    require(type(T) is int and T >= 0, "T must be a nonnegative integer")
    K, N = T + 1, (T + 1) ** 2
    R = [1]
    for i in range(1, N + 1):
        R = dense_times_linear(R, i)
    U, V = [Fraction(0)] * N, [Fraction(0)] * N
    for i in range(1, N + 1):
        numerator = divide_at_root(R, i)
        denominator = dense_at(numerator, i)
        u, v = divmod(i - 1, K)
        for k, c in enumerate(numerator):
            basis = Fraction(c, denominator)
            U[k] += (u + 1) * basis
            V[k] += (v + 1) * basis
    d = math.factorial(N - 1)
    require(all((d*c).denominator == 1 for c in U + V), "clearing denominator failed")
    return K, N, d, [int(d*c) for c in U], [int(d*c) for c in V], R


def dense_in_ring(v, variable):
    out = variable.ring.constant(0)
    for c in reversed(v):
        out = out * variable + c
    return out


def validate_set(T, accepted):
    require(type(T) is int and T >= 0, "T must be a nonnegative integer")
    require(isinstance(accepted, (list, tuple, set)), "accepted must be a finite list")
    require(all(type(i) is int for i in accepted), "noninteger acceptance node")
    require(len(accepted) == len(set(accepted)), "duplicate acceptance node")
    N = (T + 1) ** 2
    require(all(1 <= i <= N for i in accepted), "acceptance node out of range")
    return sorted(accepted)


def native(T, accepted, ring=None, interpolation=None):
    accepted = validate_set(T, accepted)
    ring = ring or Ring(NATIVE_NAMES)
    A, B, j, r, s = [ring.var(n) for n in NATIVE_NAMES]
    K, N, d, ud, vd, rd = interpolation or interpolate(T)
    U, V, R = [dense_in_ring(v, j) for v in (ud, vd, rd)]
    hd = [1]
    for i in accepted:
        hd = dense_times_linear(hd, i)
    H = dense_in_ring(hd, j)
    residuals = [R, (d*A-U)*(U-d*K), d*(A-r+1)-U,
                 (d*B-V)*(V-d*K), d*(B-s+1)-V, H]
    return residuals, sum((p*p for p in residuals), ring.constant(0))


def power_module(ring, prefix, C):
    p = {n: ring.var(prefix+n) for n in LEAVES}
    q = {n: p[n]-1 for n in NATURAL}
    o,w,M,g,x,y,u,v,z,t,qb,qv,J = [p[n] for n in DIRECT]
    alpha,beta = p['alpha_plus']+1,p['beta_plus']+1
    a1,a2,s1,s2,t1,t2,r1,r2 = [q[n] for n in ['a1','a2','s1','s2','t1','t2','rho1','rho2']]
    return [x*x-1-(alpha*alpha-1)*y*y,
            u*u-1-(alpha*alpha-1)*v*v,
            z*z-1-(beta*beta-1)*t*t,
            beta-1-4*y*qb, beta+u*(a1-a2)-alpha,
            v-y*y*qv, z+u*(s1-s2)-x, t+4*y*(t1-t2)-C,
            y-C-q['dyk'], w-2-q['dwb'], w-C-q['dwk'], M-2*o-J,
            alpha*alpha-1-((w+1)*(w+1)-1)*w*w*g*g,
            4*alpha-M-5, x+M*(r1-r2)-y*(alpha-2)-2*o]


def gap(T, accepted):
    names = ['g1','g2','g3'] + NATIVE_NAMES + ['pa_'+n for n in LEAVES] + ['pb_'+n for n in LEAVES]
    ring = Ring(names)
    residuals, unused = native(T, accepted, ring)
    g1,g2,g3,A,B = [ring.var(n) for n in ['g1','g2','g3','A','B']]
    D = g1+g2+g3
    residuals = [(20*g1-D)*ring.var('pa_o')-2*D,
                 (20*g3-D)*ring.var('pb_o')-2*D] + power_module(ring,'pa_',A) + power_module(ring,'pb_',B) + residuals
    require(len(names) == 60 and len(residuals) == 38, 'gap ledger error')
    return residuals, sum((p*p for p in residuals), ring.constant(0))


def summary(T, accepted, kind, residuals, polynomial):
    out = dict(kind=kind,T=T,N=(T+1)**2,accepted=len(accepted),
               variables=len(polynomial.ring.names),positive_witnesses=3 if kind=='native' else 57,
               residual_slots=len(residuals),degree=polynomial.degree(),
               nonzero_monomials=len(polynomial.terms),coefficient_l1=str(polynomial.norm()),
               maximum_coefficient_magnitude_bits=max(abs(c).bit_length() for c in polynomial.terms.values()))
    if kind == 'native':
        K,N=T+1,(T+1)**2
        L=K*2**(N-1)*math.factorial(N+1)
        bound=2 if T==0 else 4*N-4
        support_bound=9 if T==0 else 16*N-5
        require(polynomial.degree() <= bound, 'degree bound exceeded')
        require(len(polynomial.terms) <= support_bound, 'support bound exceeded')
        require(polynomial.norm() <= 66*L**4, 'coefficient norm bound exceeded')
        bit_bound=7+4*(L-1).bit_length()
        require(out['maximum_coefficient_magnitude_bits'] <= bit_bound, 'coefficient bit bound exceeded')
        m=N-1
        shape_bounds={(0,0,0,0):max(2,4*m),(2,0,0,0):2*m,(0,2,0,0):2*m,
                      (1,0,0,0):3*m,(0,1,0,0):3*m,(0,0,1,0):m,(0,0,0,1):m,
                      (0,0,2,0):0,(0,0,0,2):0,(1,0,1,0):0,(0,1,0,1):0}
        for a,b,j,r,s in polynomial.terms:
            require((a,b,r,s) in shape_bounds and j<=shape_bounds[(a,b,r,s)],'forbidden monomial type')
        out.update(degree_upper_bound=bound,support_upper_bound=support_bound,coefficient_magnitude_bit_upper_bound=bit_bound)
    return out


def document(T, accepted, kind='native', include_residuals=True):
    residuals, polynomial = (native if kind=='native' else gap)(T,accepted)
    doc={'schema':'three-witness-polynomial-v1','source_proof_sha256':PROOF_SHA,
         'kind':kind,'T':T,'accepted':sorted(accepted),
         'variable_order':polynomial.ring.names,'polynomial':polynomial.serial()}
    if include_residuals:
        doc['residuals']=[r.serial() for r in residuals]
    return doc


def read_terms(rows, ring):
    require(type(rows) is list, 'term collection must be a list')
    terms={}
    for row in rows:
        require(type(row) is dict and set(row)=={'exponents','coefficient'},'invalid term record')
        e=row['exponents']; c=row['coefficient']
        require(type(e) is list and len(e)==len(ring.names),'wrong exponent vector size')
        require(all(type(k) is int and k>=0 for k in e),'invalid exponent')
        require(type(c) is str and re.fullmatch(r'-?[1-9][0-9]*',c) is not None,'coefficient must be canonical nonzero decimal string')
        require(tuple(e) not in terms,'duplicate monomial')
        terms[tuple(e)]=int(c)
    return P(ring,terms)


def check_document(doc):
    require(type(doc) is dict,'candidate must be a JSON object')
    required={'schema','source_proof_sha256','kind','T','accepted','variable_order','polynomial'}
    require(required <= set(doc) <= required|{'residuals'},'candidate field set mismatch')
    require(doc['schema']=='three-witness-polynomial-v1','unknown schema')
    require(doc['source_proof_sha256']==PROOF_SHA,'wrong proof pin')
    require(doc['kind'] in ('native','gap'),'unknown polynomial kind')
    accepted=validate_set(doc['T'],doc['accepted'])
    require(type(doc['accepted']) is list and doc['accepted']==accepted,'acceptance list must be sorted')
    rs, expected=(native if doc['kind']=='native' else gap)(doc['T'],accepted)
    require(doc['variable_order']==expected.ring.names,'variable order mismatch')
    actual=read_terms(doc['polynomial'],expected.ring)
    require(actual.terms==expected.terms,'expanded polynomial coefficients do not match')
    if 'residuals' in doc:
        require(type(doc['residuals']) is list and len(doc['residuals'])==len(rs),'wrong residual slot count')
        for i,(rows,r) in enumerate(zip(doc['residuals'],rs)):
            require(read_terms(rows,expected.ring).terms==r.terms,'residual mismatch at slot '+str(i))
    return summary(doc['T'],accepted,doc['kind'],rs,expected)


def verify_source(root):
    root=Path(root)
    digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    require(digest(root/'PROOF.md')==PROOF_SHA,'source proof pin mismatch')
    require(digest(root/'MANIFEST.json')==MANIFEST_SHA,'source manifest pin mismatch')
    manifest=json.loads((root/'MANIFEST.json').read_text())
    listed=[]
    for row in manifest['files']:
        path=Path(row['path'])
        require(not path.is_absolute() and '..' not in path.parts,'unsafe manifest path')
        require(not (root/path).is_symlink(),'manifest path is a symlink')
        data=(root/path).read_bytes()
        require(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],'manifest entry mismatch: '+str(path))
        listed.append(str(path))
    pins=json.loads((root/'SOURCE_PINS.json').read_text())
    for row in pins:
        data=(root/row['file']).read_bytes()
        require(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],'dependency pin mismatch')
    actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    require(actual==set(listed)|{'MANIFEST.json'},'unmanifested or missing source file')
    return {'status':'verified','proof_sha256':PROOF_SHA,'manifest_sha256':MANIFEST_SHA,
            'manifest_entries':len(listed),'dependency_pins':len(pins),'source_execution':False}


def exponent_zero(prefix):
    v=dict(o=1,w=2,M=63,g=3,x=17,y=1,u=577,v=34,z=17,t=1,qb=4,qv=34,J=61,
           alpha_plus=16,beta_plus=16)
    v.update({n:1 for n in NATURAL}); v['dwk']=2
    return {prefix+n:x for n,x in v.items()}


def selftest():
    out={'scope':'fresh rational interpolation and polynomial assignments only',
         'source_proof_sha256':PROOF_SHA,'native_instances':[],'gap_instances':[]}
    nodes=0; classification_checks=0; expanded_assignment_checks=0
    for T in range(7):
        inter=interpolate(T); K,N,d,U,V,R=inter
        for i in range(1,N+1):
            u,v=divmod(i-1,K)
            require(dense_at(U,i)==d*(u+1) and dense_at(V,i)==d*(v+1),'interpolation node failure')
            require(dense_at(R,i)==0,'root range failure'); nodes+=1
        require(dense_at(R,0)!=0 and dense_at(R,N+1)!=0,'outside range failure')
        tables=[[],list(range(1,N+1)),[i for i in range(1,N+1) if ((i-1)//K)==((i-1)%K)],list(range(1,K+1))]
        for S in tables:
            rs,Pn=native(T,S,interpolation=inter)
            out['native_instances'].append(summary(T,S,'native',rs,Pn))
            for A,B in itertools.product(range(1,K+6),repeat=2):
                u,v=min(A,K),min(B,K); j=(u-1)*K+v
                witness=(j,A-u+1,B-v+1)
                expected=[witness] if j in S else []
                found=[]
                for i in range(1,N+1):
                    ui,vi=divmod(i-1,K); ui+=1; vi+=1
                    r,s=A-ui+1,B-vi+1
                    # Independent scalar characterization at interpolation nodes.
                    zero=(A-ui)*(ui-K)==0 and (B-vi)*(vi-K)==0 and r>0 and s>0 and i in S
                    if zero: found.append((i,r,s))
                    classification_checks+=1
                require(found==expected,'finite class uniqueness failure')
                require((Pn.at([A,B,*witness])==0)==bool(expected),'expanded polynomial assignment failure')
                expanded_assignment_checks+=1
    brute=0
    for T in (0,1):
        K,N=T+1,(T+1)**2
        for mask in range(1<<N):
            S=[i+1 for i in range(N) if mask>>i&1]
            rs,Pn=native(T,S)
            for A,B in itertools.product(range(1,6),repeat=2):
                found=[]
                for j,r,s in itertools.product(range(1,N+3),range(1,7),range(1,7)):
                    scalar=sum(q.at([A,B,j,r,s])**2 for q in rs)
                    require(Pn.at([A,B,j,r,s])==scalar,'expansion versus residual failure')
                    if scalar==0: found.append((j,r,s))
                    brute+=1
                u,v=min(A,K),min(B,K); j=(u-1)*K+v
                require(found==([(j,A-u+1,B-v+1)] if j in S else []),'literal witness uniqueness failure')
    all_table_checks=0
    for mask in range(512):
        S=[i+1 for i in range(9) if mask>>i&1]
        rs,Pn=native(2,S)
        for A,B in itertools.product(range(1,7),repeat=2):
            u,v=min(A,3),min(B,3); j=3*(u-1)+v
            require((Pn.at([A,B,j,A-u+1,B-v+1])==0)==(j in S),'all-N9-table fixture failure')
            all_table_checks+=1
    # Closed-form, hand-declared tables only; no program is stepped here.
    declared = [
        ('initial_halt_at_zero',0,[1],31,47,True),
        ('nonhalt_at_zero',0,[],31,47,False),
        ('initial_halt_by_two',2,list(range(1,10)),31,47,True),
        ('initial_halt_exact_two',2,[],31,47,False),
        ('zero_decrement_loop_by_two',2,list(range(1,7)),1,47,True),
        ('zero_decrement_loop_exact_two',2,[4,5,6],2,47,True),
        ('zero_decrement_loop_early_excluded',2,[4,5,6],1,47,False),
        ('zero_decrement_loop_tail_excluded',2,list(range(1,7)),3,47,False),
        ('increment_loop_empty',2,[],31,47,False),
    ]
    for label,T,S,A,B,want in declared:
        rs,Pn=native(T,S);K=T+1;u,v=min(A,K),min(B,K)
        require((Pn.at([A,B,(u-1)*K+v,A-u+1,B-v+1])==0)==want,'declared fixture failure: '+label)
    out['declared_semantic_fixtures']=[row[0] for row in declared]
    for T in range(4):
        N=(T+1)**2
        for S in ([],[1],list(range(1,N+1))):
            rs,Pg=gap(T,S); _,Pn=native(T,S)
            require(Pg.degree()==max(12,Pn.degree()),'gap degree identity failure')
            for prefix in ('pa_','pb_'):
                e=[0]*60; e[Pg.ring.names.index(prefix+'w')]=8; e[Pg.ring.names.index(prefix+'g')]=4
                require(Pg.terms.get(tuple(e))==1,'missing degree-twelve monomial')
            assignment={'g1':3,'g2':14,'g3':3,'A':1,'B':1,'j':1,'r':1,'s':1}
            assignment.update(exponent_zero('pa_'));assignment.update(exponent_zero('pb_'))
            require((Pg.at(assignment)==0)==(1 in S),'gap positive fixture failure')
            if 1 in S:
                for delta in (1,17,1000):
                    changed=assignment.copy();changed['pa_a1']+=delta;changed['pa_a2']+=delta
                    require(Pg.at(changed)==0,'paired-quotient nonuniqueness failure')
                changed=assignment.copy();changed['g2']+=1
                require(Pg.at(changed)!=0,'gap mutation unexpectedly accepted')
            out['gap_instances'].append(summary(T,S,'gap',rs,Pg))
    fixture=document(1,[1,3]);check_document(fixture)
    gap_fixture=document(0,[1],'gap');check_document(gap_fixture)
    mutations=[]
    for label in ('coefficient','residual','accepted','source_pin','variable_order','duplicate_term','negative_exponent','missing_slot'):
        bad=copy.deepcopy(fixture)
        if label=='coefficient': bad['polynomial'][0]['coefficient']=str(int(bad['polynomial'][0]['coefficient'])+1)
        elif label=='residual': bad['residuals'][0][0]['coefficient']='999'
        elif label=='accepted': bad['accepted']=[1]
        elif label=='source_pin': bad['source_proof_sha256']='0'*64
        elif label=='variable_order': bad['variable_order'][0]='extra'
        elif label=='duplicate_term': bad['polynomial'].append(bad['polynomial'][0])
        elif label=='negative_exponent': bad['polynomial'][0]['exponents'][0]=-1
        elif label=='missing_slot': bad['residuals'].pop()
        try: check_document(bad)
        except ValueError: mutations.append(label)
        else: raise ValueError('mutation not rejected: '+label)
    out.update(interpolation_nodes=nodes,class_code_assignment_checks=classification_checks,
               expanded_canonical_assignment_checks=expanded_assignment_checks,
               literal_positive_witness_triples=brute,exhaustive_N9_tables=512,
               N9_table_assignment_checks=all_table_checks,external_format_mutations_rejected=mutations,
               checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),status='all checks passed')
    return out


def write_json(value,path=None):
    text=json.dumps(value,indent=2)+'\n'
    if path: Path(path).write_text(text)
    else: print(text,end='')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    s=sub.add_parser('verify-source');s.add_argument('source_directory')
    s=sub.add_parser('check');s.add_argument('candidate_json');s.add_argument('--source-directory')
    s=sub.add_parser('export');s.add_argument('--T',type=int,required=True);s.add_argument('--accepted',default='')
    s.add_argument('--kind',choices=['native','gap'],default='native');s.add_argument('--output')
    s=sub.add_parser('selftest');s.add_argument('--output')
    args=parser.parse_args()
    if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
    try:
        if args.command=='verify-source': write_json(verify_source(args.source_directory))
        elif args.command=='check':
            source=verify_source(args.source_directory) if args.source_directory else None
            result=check_document(json.loads(Path(args.candidate_json).read_text()))
            write_json({'status':'exact coefficient match','source':source,'result':result,
                        'semantic_limit':'acceptance table treated as declared data; no machine semantics or table provenance certified'})
        elif args.command=='export':
            S=[] if not args.accepted else [int(i) for i in args.accepted.split(',')]
            write_json(document(args.T,S,args.kind),args.output)
        else: write_json(selftest(),args.output)
    except (ValueError,KeyError,TypeError,OSError,json.JSONDecodeError) as e:
        print('FAIL: '+str(e),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    raise SystemExit(main())
