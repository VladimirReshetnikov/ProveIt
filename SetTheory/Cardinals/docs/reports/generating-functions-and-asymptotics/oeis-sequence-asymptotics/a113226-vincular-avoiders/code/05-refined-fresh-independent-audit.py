#!/usr/bin/env python3
"""Independent audit: direct posets, cycle inverse, direct saddle expansion.
Does not import any release computation module. Writes only its own JSON report.
"""
from collections import Counter
import hashlib,json,math
from pathlib import Path
import sympy as S
import mpmath as mp
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

def posets(n):
    # Append the actual strict downset of each successive natural label.
    # Parents must themselves have empty downset (excludes 3-chains).
    # Strict downsets must be comparable (excludes induced 2+2).
    def extend(ds,minima):
        if len(ds)==n:
            yield ds;return
        sub=minima
        while True:
            if all((sub & old) in (sub,old) for old in ds):
                yield from extend(ds+(sub,),minima | ((1<<len(ds)) if sub==0 else 0))
            if not sub:break
            sub=(sub-1)&minima
    yield from extend((),0)

def labels(mask):return tuple(i for i in range(mask.bit_length()) if mask>>i&1)

def to_cycles(ds):
    levels=sorted(set(ds)-{0},key=int.bit_count);previous=0;pairs=[]
    for level in levels:
        E=labels(level^previous);M=tuple(i for i,d in enumerate(ds) if d==level)
        pairs.append((E,M));previous=level
    occupied=previous
    for i,d in enumerate(ds):
        if d:occupied|=1<<i
    isolated=labels(((1<<len(ds))-1)^occupied)
    cycles=[];record=-1
    for E,M in pairs:
        if max(E)>record:cycles.append([]);record=max(E)
        cycles[-1].append((E,M))
    for cycle in cycles:
        assert max(i for E,M in cycle for i in E)<min(i for E,M in cycle for i in M)
    return cycles,isolated

def from_cycles(cycles,isolated,n):
    canonical=[]
    # Change representations before canonicalizing, to test unrooted cycles/SET.
    for cycle in reversed(cycles):
        cycle=cycle[1:]+cycle[:1]
        maximum=max(i for E,M in cycle for i in E)
        r=next(j for j,(E,M) in enumerate(cycle) if maximum in E)
        canonical.append((maximum,cycle[r:]+cycle[:r]))
    ds=[0]*n;down=0
    for maximum,cycle in sorted(canonical):
        for E,M in cycle:
            for i in E:down|=1<<i
            for i in M:ds[i]=down
    return tuple(ds)

def stirling(n,k):
    return sum((-1)**(k-j)*math.comb(k,j)*j**n for j in range(k+1))//math.factorial(k)

def partitions(total,lower=1):
    if not total:yield ();return
    for j in range(lower,total+1):
        for tail in partitions(total-j,j):yield (j,)+tail

def exp_coeff(q,k):
    ans=0
    for p in partitions(k):
        term=1
        for j,count in Counter(p).items():term*=q[j]**count/S.factorial(count)
        ans+=term
    return S.expand(ans)

def gauss(poly,x,var):
    return S.factor(sum(co*S.factorial2(power-1)*var**(power//2)
                        for (power,),co in S.Poly(poly,x).terms() if power%2==0))

def main():
    out={'source_sha256':{p:sha(p) for p in ['refined-proof.md','a113226-refined-addendum.tex','refined_coefficients.json','exact_rows.json']}}
    raw=json.loads((ROOT/'exact_rows.json').read_text());checks=[]
    for n in range(9):
        joint=Counter();component=Counter();roundtrips=0
        for ds in posets(n):
            cycles,isolated=to_cycles(ds);assert from_cycles(cycles,isolated,n)==ds
            k=len(set(ds)-{0});j=len(isolated);joint[k,j]+=1;roundtrips+=1
            if len(cycles)==1 and not isolated:component[k]+=1
        row=[sum(count for (k,j),count in joint.items() if k==m) for m in range(n//2+1)]
        assert row==raw[n]
        for m in range(1,n//2+1):
            expect=math.factorial(m)*math.factorial(m-1)*sum(stirling(a,m)*stirling(n-a,m) for a in range(m,n-m+1))
            assert component[m]==expect
        for k in range(n//2+1):
            for j in range(n+1):
                r=n-j
                noiso=sum((-1)**h*math.comb(r,h)*(raw[r-h][k] if k<len(raw[r-h]) else 0) for h in range(r+1))
                assert joint[k,j]==math.comb(n,j)*noiso
        checks.append({'n':n,'posets_and_cycle_roundtrips':roundtrips,'row':row,'joint_entries':len(joint),'component_counts':dict(component)})
    out['direct_poset_checks']=checks
    # Direct joint-singularity Taylor check using an algebraic expression for coth.
    w,aa,rr=S.symbols('w a rho',positive=True)
    qq=S.cosh(w/2)-aa*S.sinh(w/2);hh=aa*S.cosh(w/2)-S.sinh(w/2)
    ss=S.series((hh/aa)*S.sqrt(aa*w/(1-qq*qq)),w,0,3).removeO().expand()
    TT=((1+aa)*S.exp(-w/2)+1)/((1+aa)*S.exp(-w/2)-1)
    R=(rr-w)/2-2*hh/(1+qq)*(TT-TT**3/3*((1-qq)/(1+qq)))
    rs=S.series(R,w,0,2).removeO().expand()
    assert S.simplify(ss.coeff(w,1)-(aa*aa-3)/(8*aa))==0
    assert S.simplify(ss.coeff(w,2)-(9*aa**4+10*aa**2-15)/(384*aa**2))==0
    assert S.simplify(rs.coeff(w,0)-(rr/2-2-aa))==0
    assert S.simplify(rs.coeff(w,1)-(4-aa**3)/(6*aa))==0
    out['joint_singularity_coefficients_verified']=['S0=1','s1','s2','R0=K','r1']
    # Independent first saddle: expand the exact local exponent directly in h=n^-1/6.
    h,x,c=S.symbols('h x c',positive=True);g1,g2,g3=S.symbols('g1 g2 g3')
    t=c*h**4*(1+S.I*h*x)
    exponent=(2*c/h**2*((1+S.I*h*x)**(-S.Rational(1,2))-1)
              -(h**-6+1)*S.log(1-t)-c/h**2
              +g1*S.sqrt(c)*h**2*(1+S.I*h*x)**S.Rational(1,2)
              +g2*t+g3*c**S.Rational(3,2)*h**6*(1+S.I*h*x)**S.Rational(3,2))
    expanded=S.expand(S.series(exponent,h,0,7).removeO()+3*c*x*x/4)
    assert expanded.coeff(h,0)==0
    q={k:expanded.coeff(h,k) for k in range(1,7)}
    first=[gauss(exp_coeff(q,2*j),x,2/(3*c)) for j in range(4)]
    reference=json.loads((ROOT/'refined_coefficients.json').read_text())
    for have,want in zip(first,reference['first_saddle']):
        assert S.simplify(have-S.sympify(want,locals={'c':c,'g1':g1,'g2':g2,'g3':g3}))==0
    out['independent_first_saddle_matches_through_a3']=True
    out['first_saddle_direct_result']=[str(a) for a in first]
    # Independent second saddle in h: direct Taylor terms and integer-partition
    # exponential expansion, instead of the release's exponential recurrence.
    V0=S.symbols('V',positive=True)
    C1,C2,D1,D2,F3,F4=S.symbols('C1 C2 D1 D2 F3 F4')
    A1,A1p,A2,A3=S.symbols('A1_0 A1_1 A2_0 A3_0')
    second_q={1:3*S.I*C1*x,2:0,3:S.I*D1*x-S.I*F3*x**3/6,
              4:-3*C2*x*x/2,5:0,6:F4*x**4/24-D2*x*x/2}
    amplitude={0:S.Integer(1),2:A1,4:A2,5:S.I*A1p*x,6:A3}
    second=[gauss(S.expand(sum(a*exp_coeff(second_q,2*j-k)
                               for k,a in amplitude.items() if k<=2*j)),x,1/V0)
            for j in range(4)]
    local_symbols={str(s):s for s in [V0,C1,C2,D1,D2,F3,F4,A1,A1p,A2,A3]}
    for have,want in zip(second,reference['second_saddle']):
        assert S.simplify(have-S.sympify(want,locals=local_symbols))==0
    out['independent_second_saddle_matches_through_b3']=True
    out['second_saddle_direct_result']=[str(b) for b in second]
    # Conditional Poisson correction: independently use n A_(n-1,k)/A_(n,k)
    # and the leading log asymptotic along fixed k, rather than second-saddle expansion.
    v=S.symbols('v',real=True);a=S.exp(-v/2);rho=2*S.log(1+a)
    cv=(S.pi**2*a/(4*rho))**S.Rational(1,3);f=-S.log(rho);alpha=S.diff(f,v);V=S.diff(f,v,2)
    assert S.simplify(3*S.diff(cv,v)-cv*(alpha-S.Rational(1,2)))==0
    assert S.simplify(-S.diff(rho,v)/rho-alpha)==0
    # Removing a single isolated label changes alpha by alpha/n and hence v by alpha/(nV).
    # The stretched term changes by (-c+3 alpha c'/V)n^-2/3.
    ratio_correction=rho*(-cv+3*alpha*S.diff(cv,v)/V)
    claimed_correction=-(rho*cv+3*S.diff(cv,v)*S.diff(rho,v)/V)
    assert S.simplify(ratio_correction-claimed_correction)==0
    assert S.diff(rho,v).subs(v,0)==-S.Rational(1,2)
    out['independent_conditional_mean_correction_identity']=True
    out['covariance_leading_constant']='-1/2'
    # Exact moment spot checks at three sizes, with no saddle coefficient code imported.
    mp.mp.dps=50
    def pars(z):
        ap=mp.exp(-z/2);r=2*mp.log(1+ap);cc=(mp.pi**2*ap/(4*r))**(mp.mpf(1)/3);return r,cc
    alpha1=1/(2*mp.log(4));r0,c0=pars(0);cov_checks=[]
    for n in (100,200,400):
        total=sum(raw[n]);prev=sum(raw[n-1]);mean=sum(k*b for k,b in enumerate(raw[n]))
        mixed=n*sum(k*b for k,b in enumerate(raw[n-1]));cov=mp.mpf(mixed)/total-(mp.mpf(mean)/total)*(mp.mpf(n)*prev/total)
        cov_checks.append({'n':n,'exact_covariance':str(cov),'scaled_error':str((cov+mp.mpf('.5'))*n**(mp.mpf(2)/3))})
    out['exact_covariance_checks']=cov_checks
    (ROOT/'fresh-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
