#!/usr/bin/env python3
"""Fresh exact polynomial checks for the three-witness bounded family.

This file constructs finite integer polynomials and evaluates declared tables
and fixtures only. It neither imports nor executes any source-packet program,
counter-machine interpreter, physical simulator, schedule search, or Lean.
"""
from itertools import product
from math import comb, factorial
from pathlib import Path
import hashlib
import json


class Poly:
    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {(): terms}
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def coerce(p):
        return p if isinstance(p, Poly) else Poly(p)

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for m, c in other.terms.items():
            terms[m] = terms.get(m, 0) + c
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        terms = {}
        for ma, ca in self.terms.items():
            for mb, cb in other.terms.items():
                powers = dict(ma)
                for name, power in mb:
                    powers[name] = powers.get(name, 0) + power
                m = tuple(sorted(powers.items()))
                terms[m] = terms.get(m, 0) + ca * cb
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        answer = Poly(1)
        for _ in range(n):
            answer = answer * self
        return answer

    def eval(self, assignment):
        return sum(c * product_int(assignment[v] ** e for v, e in m)
                   for m, c in self.terms.items())

    def degree(self):
        return max((sum(e for _, e in m) for m in self.terms), default=-1)

    def l1(self):
        return sum(abs(c) for c in self.terms.values())

    def variables(self):
        return set(v for m in self.terms for v, _ in m)

    def coefficient(self, **powers):
        return self.terms.get(tuple(sorted(powers.items())), 0)


def product_int(values):
    value = 1
    for x in values:
        value *= x
    return value


def var(name):
    return Poly({((name, 1),): 1})


def pprod(values):
    answer = Poly(1)
    for value in values:
        answer *= value
    return answer


def interpolation(T):
    assert T >= 0
    K, N = T + 1, (T + 1) ** 2
    d, j = factorial(N - 1), var('j')
    U, V = Poly(), Poly()
    for i in range(1, N + 1):
        u, v = (i - 1) // K + 1, (i - 1) % K + 1
        factor = (-1) ** (N - i) * comb(N - 1, i - 1)
        basis = factor * pprod(j - h for h in range(1, N + 1) if h != i)
        U, V = U + u * basis, V + v * basis
    F = pprod(j - i for i in range(1, N + 1))
    return K, N, d, U, V, F


def clipped_formula(T, accepted):
    K, N, d, U, V, F = interpolation(T)
    accepted = set(accepted)
    assert accepted <= set(range(1, N + 1))
    A, B, j, r, s = (var(x) for x in ('A', 'B', 'j', 'r', 's'))
    H = pprod(j - i for i in sorted(accepted))
    residuals = [F, (d*A-U)*(U-d*K), d*A-U-d*(r-1),
                 (d*B-V)*(V-d*K), d*B-V-d*(s-1), H]
    return residuals, sum(p*p for p in residuals)


MODULE_DIRECT = ['o', 'w', 'M', 'g', 'xp', 'yp', 'up', 'vp', 'sp', 'tp',
                 'qb', 'qv', 'Jp']
MODULE_SHIFT2 = ['alpha_plus', 'beta_plus']
MODULE_NAT = ['dwb', 'dwk', 'dyk', 'a1', 'a2', 's1', 's2', 't1', 't2',
              'r1', 'r2']


def power_residuals(prefix, C):
    names = [prefix+x for x in MODULE_DIRECT+MODULE_SHIFT2+MODULE_NAT]
    positive = {x: var(prefix+x) for x in MODULE_DIRECT+MODULE_SHIFT2+MODULE_NAT}
    q = {x: positive[x] for x in MODULE_DIRECT}
    q.update({x: positive[x]-1 for x in MODULE_NAT})
    alpha, beta = positive['alpha_plus']+1, positive['beta_plus']+1
    o,w,M,g,xp,yp,up,vp,sp,tp,qb,qv,Jp = [q[x] for x in MODULE_DIRECT]
    dwb,dwk,dyk,a1,a2,s1,s2,t1,t2,r1,r2 = [q[x] for x in MODULE_NAT]
    residuals = [
        xp**2-1-(alpha**2-1)*yp**2,
        up**2-1-(alpha**2-1)*vp**2,
        sp**2-1-(beta**2-1)*tp**2,
        beta-1-4*yp*qb,
        beta+up*a1-alpha-up*a2,
        vp-yp**2*qv,
        sp+up*s1-xp-up*s2,
        tp+4*yp*t1-C-4*yp*t2,
        yp-C-dyk,
        w-2-dwb,
        w-C-dwk,
        M-2*o-Jp,
        alpha**2-1-((w+1)**2-1)*(w*g)**2,
        4*alpha-M-5,
        xp+M*r1-yp*(alpha-2)-2*o-M*r2,
    ]
    assert len(names) == len(set(names)) == 26
    return names, residuals


def gap_formula(T, accepted):
    native_residuals, native = clipped_formula(T, accepted)
    namesA, residualsA = power_residuals('pa_', var('A'))
    namesB, residualsB = power_residuals('pb_', var('B'))
    g1,g2,g3 = (var(x) for x in ('g1','g2','g3'))
    D = g1+g2+g3
    gaps = [(20*g1-D)*var('pa_o')-2*D,
            (20*g3-D)*var('pb_o')-2*D]
    base = gaps+residualsA+residualsB
    residuals = base+native_residuals
    witnesses = ['A','B']+namesA+namesB+['j','r','s']
    return witnesses, residuals, sum(p*p for p in residuals), sum(p*p for p in base)


def exponent_zero(prefix):
    values = dict(o=1,w=2,M=63,g=3,xp=17,yp=1,up=577,vp=34,
                  sp=17,tp=1,qb=4,qv=34,Jp=61,alpha_plus=16,beta_plus=16)
    values.update({x: 1 for x in MODULE_NAT})
    values['dwk'] = 2
    return {prefix+x: value for x,value in values.items()}


def run():
    report = {'scope': 'exact polynomial enumeration and declared tables only',
              'interpolation': [], 'arbitrary_table_ledgers': [],
              'brute_force': [], 'native_gap_ledgers': [], 'declared_fixtures': []}

    # Every interpolation node is checked, together with integer coefficient
    # norm bounds. No program transitions are generated or followed.
    for T in range(7):
        K,N,d,U,V,F = interpolation(T)
        L = K*2**(N-1)*factorial(N+1)
        for i in range(1,N+1):
            u,v = (i-1)//K+1,(i-1)%K+1
            assert U.eval({'j':i}) == d*u
            assert V.eval({'j':i}) == d*v
            assert F.eval({'j':i}) == 0
        assert U.l1() <= L and V.l1() <= L and F.l1() <= L
        assert d*K <= L
        assert F.eval({'j':N+1}) == factorial(N)
        report['interpolation'].append(dict(T=T,N=N,U_degree=U.degree(),
                                             V_degree=V.degree(),nodes_checked=N))
        declared_tables = [set(),set(range(1,N+1)),
                           {i for i in range(1,N+1) if i%2},
                           {i for i in range(1,N+1) if (i-1)//K+1 <= max(1,K//2)}]
        for accepted in declared_tables:
            residuals,P = clipped_formula(T,accepted)
            degree_bound = 2 if T == 0 else 4*N-4
            assert len(residuals) == 6
            assert P.degree() <= degree_bound
            assert P.l1() <= 66*L**4
            assert P.variables() == {'A','B','j','r','s'}
            m=N-1
            support = {
                (): 4*m if T else 2,
                (('A',2),):2*m, (('B',2),):2*m,
                (('A',1),):3*m, (('B',1),):3*m,
                (('r',1),):m, (('s',1),):m,
                (('r',2),):0, (('s',2),):0,
                (('A',1),('r',1)):0, (('B',1),('s',1)):0,
            }
            monomial_bound=16*N-5 if T else 9
            assert len(P.terms) <= monomial_bound
            for monomial in P.terms:
                nonselector=tuple((v,e) for v,e in monomial if v!='j')
                j_power=dict(monomial).get('j',0)
                assert nonselector in support
                assert j_power <= support[nonselector]
            input_checks = 0
            for A,B in product(range(1,K+5),repeat=2):
                u,v = min(A,K),min(B,K)
                j = (u-1)*K+v
                assignment = dict(A=A,B=B,j=j,r=A-u+1,s=B-v+1)
                assert (P.eval(assignment)==0) == (j in accepted)
                # Exhaust all finite class choices; their slacks are forced.
                solutions = []
                for candidate in range(1,N+1):
                    ui,vi = (candidate-1)//K+1,(candidate-1)%K+1
                    ri,si = A-ui+1,B-vi+1
                    if ri > 0 and si > 0:
                        test = dict(A=A,B=B,j=candidate,r=ri,s=si)
                        if all(p.eval(test)==0 for p in residuals):
                            solutions.append((candidate,ri,si))
                expected = [(j,assignment['r'],assignment['s'])] if j in accepted else []
                assert solutions == expected
                input_checks += 1
            report['arbitrary_table_ledgers'].append(dict(T=T,accepted=len(accepted),
                degree=P.degree(),degree_bound=degree_bound,
                coefficient_max_bits=max(abs(c).bit_length() for c in P.terms.values()),
                monomials=len(P.terms),monomial_bound=monomial_bound,
                input_checks=input_checks))

    # Independent literal brute force over all positive witness triples in
    # finite boxes and every table for N=1 and N=4. Satisfying slacks outside
    # the box are already excluded by the symbolic equations and input bound.
    for T in (0,1):
        K,N=T+1,(T+1)**2
        checks=0
        for mask in range(1<<N):
            accepted={i+1 for i in range(N) if mask & (1<<i)}
            residuals,P=clipped_formula(T,accepted)
            for A,B in product(range(1,K+4),repeat=2):
                found=[]
                for j,r,s in product(range(1,N+2),range(1,K+5),range(1,K+5)):
                    assignment=dict(A=A,B=B,j=j,r=r,s=s)
                    zero=all(p.eval(assignment)==0 for p in residuals)
                    checks+=1
                    if zero:
                        assert P.eval(assignment)==0
                        found.append((j,r,s))
                u,v=min(A,K),min(B,K)
                j=(u-1)*K+v
                expected=[(j,A-u+1,B-v+1)] if j in accepted else []
                assert found==expected
        report['brute_force'].append(dict(T=T,tables=1<<N,tuples_checked=checks))

    # These acceptance sets are declared mathematical fixtures, not obtained
    # by executing a program. The proof explains each graph and trace.
    declared = [
        ('initial_halt_by_0',0,{1},1,1,True),
        ('not_initial_halt_by_0',0,set(),1,1,False),
        ('initial_halt_by_3',3,set(range(1,17)),7,9,True),
        ('initial_halt_exact_3',3,set(),7,9,False),
        ('decrement_loop_by_3',3,set(range(1,13)),3,9,True),
        ('decrement_loop_tail_by_3',3,set(range(1,13)),4,9,False),
        ('decrement_loop_exact_3',3,set(range(9,13)),3,9,True),
        ('decrement_loop_early_exact_3',3,set(range(9,13)),2,9,False),
        ('increment_loop_by_3',3,set(),9,9,False),
    ]
    for name,T,accepted,A,B,want in declared:
        residuals,P=clipped_formula(T,accepted)
        K=T+1; u,v=min(A,K),min(B,K)
        assignment=dict(A=A,B=B,j=(u-1)*K+v,r=A-u+1,s=B-v+1)
        assert (P.eval(assignment)==0)==want
        report['declared_fixtures'].append(dict(name=name,accepted=want,witness=assignment))

    for T in range(6):
        N=(T+1)**2
        for accepted in (set(),set(range(1,N+1)),{1}):
            witnesses,residuals,F,base=gap_formula(T,accepted)
            _,native=clipped_formula(T,accepted)
            assert len(witnesses)==len(set(witnesses))==57
            assert len(residuals)==38
            assert F.variables()==set(witnesses)|{'g1','g2','g3'}
            assert F.degree()==max(12,native.degree())
            assert F.coefficient(pa_w=8,pa_g=4)==1
            assert F.coefficient(pb_w=8,pb_g=4)==1
            assignment=dict(g1=3,g2=14,g3=3,A=1,B=1,j=1,r=1,s=1)
            assignment.update(exponent_zero('pa_'))
            assignment.update(exponent_zero('pb_'))
            assert (F.eval(assignment)==0)==(1 in accepted)
            if 1 in accepted:
                shifted=dict(assignment)
                shifted['pa_a1']+=11; shifted['pa_a2']+=11
                assert F.eval(shifted)==0
                wrong=dict(assignment); wrong['g2']+=1
                assert F.eval(wrong)!=0
            report['native_gap_ledgers'].append(dict(T=T,accepted=len(accepted),
                witnesses=len(witnesses),residuals=len(residuals),degree=F.degree(),
                fixed_base_l1=base.l1()))

    root=Path(__file__).resolve().parent
    report['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (root/'evidence'/'static_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({
        'interpolation_nodes':sum(x['nodes_checked'] for x in report['interpolation']),
        'arbitrary_table_ledgers':len(report['arbitrary_table_ledgers']),
        'class_uniqueness_input_checks':sum(x['input_checks'] for x in report['arbitrary_table_ledgers']),
        'literal_witness_tuples':sum(x['tuples_checked'] for x in report['brute_force']),
        'declared_fixtures':len(report['declared_fixtures']),
        'native_gap_ledgers':len(report['native_gap_ledgers']),
        'status':'all assertions passed'
    },indent=2))


if __name__=='__main__':
    run()
