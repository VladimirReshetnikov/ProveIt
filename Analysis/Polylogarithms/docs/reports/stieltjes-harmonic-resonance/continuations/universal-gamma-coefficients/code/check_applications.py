"""Exact harmonic endpoints, arithmetic-step sums, and support counts."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
v=s.symbols('v'); L=s.log(2)

def G_endpoint(a,q,sign):
    a=s.Integer(a)
    if sign==1:
        return sum((-1)**(q-j)*s.zeta(j)/a**(q-j+1) for j in range(2,q+1))+(-1)**(q+1)*s.harmonic(a)/a**q
    Li=lambda j: -L if j==1 else -(1-2**(1-s.Integer(j)))*s.zeta(j)
    alt=sum(s.Rational((-1)**r,r) for r in range(1,int(a)+1))
    return sum((-1)**(q-j)*Li(j)/a**(q-j+1) for j in range(1,q+1))+(-1)**q*(-1)**a/a**q*(-L-alt)

def main():
    P=s.expand((1-v*v)**3*(1+3*v*v)/192)
    values={}
    expected={1:s.Rational(299,70560)-L/252,
              2:-s.Rational(66161,11113200)+s.Rational(275,774144)*s.pi**2+s.Rational(67,13230)*L}
    for q in [1,2]:
        result=0
        for sign in [1,-1]:
            W=s.Poly(s.cancel(P/(1-sign*v))/2,v)
            for (n,),c in W.terms():result+=c*G_endpoint(n+1,q,sign)
        assert s.expand(result-expected[q])==0
        values[f'harmonic_order_{q}']=str(expected[q])
    weights={1:s.Rational(1,192),5:-s.Rational(1,32),7:s.Rational(1,24),9:-s.Rational(1,64)}
    for j in range(3):assert sum(d*a**j for a,d in weights.items())==0
    expected_steps={2:s.Rational(1,252),3:-s.Rational(11,384)+s.log(3)/128+5*s.sqrt(3)*s.pi/1152,
                    4:s.Rational(13,360)-s.pi/96}
    for h in [2,3,4]:
        val=-sum(d*s.polygamma(0,s.Rational(a,h)) for a,d in weights.items())/h
        assert s.simplify(s.expand_func(val)-expected_steps[h])==0
        values[f'arithmetic_step_{h}']=str(expected_steps[h])
    # Independent elementary parity count, no normalizer or beta coefficients.
    data=json.loads((ROOT/'data'/'normal_forms_through_18.json').read_text())
    def count(m):
        total=1 # pure u0^m
        for d in range(1,m//2):
            budget=m-2*(d+1)
            if budget<0:continue
            dp={(0,0):1}
            for r in range(1,d+1):
                nxt={}
                for (weight,parity),ways in dp.items():
                    for a in range((budget-weight)//(r+1)+1):
                        key=(weight+a*(r+1),(parity+r*a)%2)
                        nxt[key]=nxt.get(key,0)+ways
                dp=nxt
            total+=sum(n for (weight,parity),n in dp.items() if parity==0)
        return total
    counts=[count(m) for m in range(19)]
    assert counts==[len(data[str(m)]['N']) for m in range(19)]
    report={'result':'PASS','harmonic_endpoints':2,'arithmetic_step_evaluations':3,
            'moment_cancellations':3,'support_count_checks':19,'support_counts_0_to_18':counts,'values':values}
    (ROOT/'data'/'application_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
