#!/usr/bin/env python3
"""Self-contained exact audit of the 33-variable quadratic lift.

Only Python's standard library is required. Coefficients beta,K0,MC,MF
are indeterminates for this algebra check and fixed integers for the theorem.
This checks algebra, counts, and degree; it does not verify the inherited
computation-to-equation or Pell theorems.
"""
from __future__ import annotations
from collections import Counter
import argparse
import json
from pathlib import Path

ORIGINAL = 'J F alpha z f h i T s w tau eta zeta y gamma'.split()
REGISTERS = 'N E P c a X D C2 G L R F2 V0 V g I Baux Delta'.split()
POSITIVE_ORIGINAL = [n for n in ORIGINAL if n not in ('tau', 'y')]
CONSTANTS = 'beta K0 MC MF'.split()

def require(condition, message):
    if not condition:
        raise ValueError(message)

class Poly:
    """Sparse integer polynomial; monomials are sorted variable tuples."""
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = value.terms
        elif isinstance(value, dict):
            self.terms = {m:c for m,c in value.items() if c}
        else:
            self.terms = {():int(value)} if value else {}
    @staticmethod
    def var(name):
        return Poly({(name,):1})
    def __add__(self, other):
        other=Poly(other)
        out=dict(self.terms)
        for m,c in other.terms.items():
            out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__
    def __neg__(self):
        return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self, other):
        return self+-Poly(other)
    def __rsub__(self, other):
        return Poly(other)+-self
    def __mul__(self, other):
        other=Poly(other)
        out={}
        for m,c in self.terms.items():
            for n,d in other.terms.items():
                k=tuple(sorted(m+n))
                out[k]=out.get(k,0)+c*d
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self, n):
        require(isinstance(n,int) and n>=0, 'nonnegative integer exponent required')
        ans=Poly(1)
        base=self
        while n:
            if n&1:
                ans=ans*base
            base=base*base if n>1 else base
            n//=2
        return ans
    def __eq__(self, other):
        return self.terms==Poly(other).terms
    def degree(self):
        return max((sum(v not in CONSTANTS for v in m) for m in self.terms),default=-1)
    def has(self, name):
        return any(name in m for m in self.terms)
    def coefficient(self, monomial):
        return self.terms.get(tuple(sorted(monomial)),0)
    def __str__(self):
        if not self.terms:
            return '0'
        parts=[]
        for m,c in sorted(self.terms.items(),key=lambda x:(-len(x[0]),x[0])):
            powers=Counter(m)
            body='*'.join(v if e==1 else f'{v}**{e}' for v,e in sorted(powers.items()))
            if not body:
                term=str(abs(c))
            elif abs(c)==1:
                term=body
            else:
                term=f'{abs(c)}*{body}'
            if not parts:
                parts.append(('-' if c<0 else '')+term)
            else:
                parts.append((' - ' if c<0 else ' + ')+term)
        return ''.join(parts)


def equations(v):
    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma = [v[n] for n in ORIGINAL]
    N,E,P,c,a,X,D,C2,G,L,R,F2,V0,V,g,I,Baux,Delta = [v[n] for n in REGISTERS]
    beta,K0,MC,MF = [v[n] for n in CONSTANTS]
    q=beta*J+1
    k=eta+zeta
    H=4*a+3
    C=q-F-alpha
    return [
        L-(q*q-1),
        N-q*(L+1),
        X-w*q,
        a-E-s*N,
        E-X*(a-E),
        c-k*(a-E)-eta,
        P-E*(c-eta)-k,
        tau*tau-P*(P-k)-1,
        D-X-a*c-gamma*H,
        Delta-a*a-H,
        C2-c*c,
        D*D-Delta*C2-1,
        k-R-1-h*E,
        G-(q-1)*(q-F)-alpha,
        R-L*G-(MC+q*MF)*J,
        (K0+w)*C+(q-F)-z*(q-1)-1,
        F2-f*f,
        V0-T*f+1,
        V-c*V0+R*F2,
        g-y*y+V*V,
        I-i*C2,
        Baux-I*I,
        Baux-Delta*(F2-1),
        y*y-Baux*g-1,
    ]


def definitions(symbols):
    v=dict(symbols)
    q=v['beta']*v['J']+1
    k=v['eta']+v['zeta']
    Y=v['s']*q**3
    v['L']=q*q-1
    v['N']=q**3
    v['X']=v['w']*q
    v['E']=v['X']*Y
    v['a']=v['E']+Y
    v['c']=k*Y+v['eta']
    v['P']=v['E']*(v['c']-v['eta'])+k
    v['D']=v['X']+v['a']*v['c']+v['gamma']*(4*v['a']+3)
    v['Delta']=v['a']*v['a']+4*v['a']+3
    v['C2']=v['c']*v['c']
    v['G']=(q-1)*(q-v['F'])+v['alpha']
    v['R']=v['L']*v['G']+(v['MC']+q*v['MF'])*v['J']
    v['F2']=v['f']*v['f']
    v['V0']=v['T']*v['f']-1
    v['V']=v['c']*v['V0']-v['R']*v['F2']
    v['g']=v['y']*v['y']-v['V']*v['V']
    v['I']=v['i']*v['C2']
    v['Baux']=v['Delta']*(v['F2']-1)
    return v


def verify():
    names=ORIGINAL+REGISTERS
    symbols={n:Poly.var(n) for n in names+CONSTANTS}
    eqs=equations(symbols)
    degrees=[e.degree() for e in eqs]
    require(len(names)==33 and len(eqs)==24 and max(degrees)==2, 'positive quadratic dimensions or degree')
    expanded=definitions(symbols)
    source_eqs=equations(expanded)
    comparisons={7,11,12,15,21,23}
    for j,e in enumerate(source_eqs):
        if j not in comparisons:
            require(e==0, 'register definition '+str(j+1))

    v=symbols
    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma=[v[n] for n in ORIGINAL]
    beta,K0,MC,MF=[v[n] for n in CONSTANTS]
    q=beta*J+1
    k=eta+zeta
    X=w*q
    Y=s*q**3
    E=X*Y
    a=E+Y
    c=k*Y+eta
    Delta=a*a+4*a+3
    D=X+a*c+gamma*(4*a+3)
    G=(q-1)*(q-F)+alpha
    R=(q*q-1)*G+(MC+q*MF)*J
    V=c*(T*f-1)-R*f*f
    I=i*c*c
    direct={
        7:tau*tau-(X*Y*Y)*(X*Y*Y+1)*k*k-1,
        11:D*D-Delta*c*c-1,
        12:k-R-1-h*E,
        15:(K0+w)*(q-F-alpha)+(q-F)-z*(q-1)-1,
        21:Delta*(f*f-1)-I*I,
        23:Delta*(f*f-1)*(V*V-y*y)+y*y-1,
    }
    for j,target in direct.items():
        require(source_eqs[j]==target, 'source residual '+str(j+1))
    require([j+1 for j,e in enumerate(eqs) if e.has('tau')]==[8], 'tau occurrence ledger')
    require(eqs[7].coefficient(('tau','tau'))==1, 'tau squared coefficient')
    # All other residuals are independent of tau; hence [tau^4] SOS = 1.

    cert_names=[]
    integer_eqs=list(eqs)
    substitutions=dict(symbols)
    for n in POSITIVE_ORIGINAL:
        extra=[n+'_pos_'+suffix for suffix in ('u','v','t')]
        cert_names.extend(extra)
        u,v,t=[Poly.var(x) for x in extra]
        positive_form=1+u*u+v*v+t*(t+1)
        integer_eqs.append(symbols[n]-positive_form)
        substitutions[n]=positive_form
    integer_names=names+cert_names
    require(len(integer_names)==72 and len(integer_eqs)==37, 'integer quartic dimensions')
    require(max(e.degree() for e in integer_eqs)==2, 'integer quadratic degrees')
    direct_integer_names=['tau','y']+REGISTERS+cert_names
    direct_eqs=equations(substitutions)
    require(len(direct_integer_names)==59, 'integer degree-eight variable count')
    require(max(e.degree() for e in direct_eqs)==4, 'integer degree-four residuals')
    require(direct_eqs[0].coefficient(('beta','beta')+('J_pos_u',)*4)==-1, 'integer degree-eight witness')

    return {
        'fixed_coefficients':CONSTANTS,
        'positive_variables':names,
        'variable_count':33,
        'quadratic_equation_count':24,
        'residuals':[str(e) for e in eqs],
        'degrees':degrees,
        'sum_of_squares_exact_degree':4,
        'degree_witness':'coefficient of tau^4 in the SOS is 1',
        'definition_residuals_verified':[j+1 for j in range(24) if j not in comparisons],
        'source_residuals_verified':[j+1 for j in direct],
        'source_residual_degrees':{str(j+1):e.degree() for j,e in direct.items()},
        'integer_quartic':{
            'variables':integer_names,
            'variable_count':72,
            'quadratic_equation_count':37,
            'residuals':[str(e) for e in integer_eqs],
            'sos_exact_degree':4,
        },
        'integer_degree8':{
            'variables':direct_integer_names,
            'variable_count':59,
            'equation_count':24,
            'residuals':[str(e) for e in direct_eqs],
            'sos_exact_degree':8,
            'degree_witness':'first residual contains -beta^2 J_pos_u^4; SOS therefore has nonzero degree 8',
        },
        'scope':'Exact algebraic audit. Positivity and inherited compiler equivalence are mathematical proof obligations, not finite tests.'
    }

if __name__=='__main__':
    result=verify()
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='regenerate the adjacent data artifact')
    args=parser.parse_args()
    base=Path(__file__).resolve().parent.parent
    out=base/'data'/'quartic33_verified.json'
    if args.write:
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(result,indent=2)+'\n')
    else:
        require(json.loads(out.read_text())==result, 'stored artifact differs from exact regeneration')
    print(json.dumps({
        'positive_variables':result['variable_count'],
        'quadratic_equations':result['quadratic_equation_count'],
        'exact_sos_degree':result['sum_of_squares_exact_degree'],
        'integer_quartic_variables':result['integer_quartic']['variable_count'],
        'integer_degree8_variables':result['integer_degree8']['variable_count'],
        'source_degrees':result['source_residual_degrees'],
        'verified':True,
    },indent=2))
