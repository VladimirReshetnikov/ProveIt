#!/usr/bin/env python3
"""Exact deep-disk fewnomial checks; integer arithmetic and SymPy HNF.

The lattice computations are certificates for finite examples, not the proof
of the general transport theorem. No floating-point linear algebra is used.
"""
from math import comb, factorial
from fractions import Fraction
from itertools import product
from collections import Counter
import json
import sympy as s
from sympy.matrices.normalforms import hermite_normal_form

def vp(n, p):
    n = abs(int(n))
    if not n:
        return None
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a

def digits(n,p):
    ans=0
    while n:
        ans += n%p
        n //= p
    return ans

def precision(t,p):
    D=max(digits(j,p) for j in range(t))
    return max(0, (D-1+p-2)//(p-1))

def compositions(n,k):
    if k==1:
        yield (n,)
    else:
        for a in range(n+1):
            for rest in compositions(n-a,k-1):
                yield (a,)+rest

def canonical(nu):
    P=len(nu)
    return tuple(sorted(c+P*j for c,m in enumerate(nu) for j in range(m)))

def rank_mod(rows,p):
    pivots={}
    for vector in rows:
        v=[int(x)%p for x in vector]
        for j,w in sorted(pivots.items()):
            a=v[j]
            if a:v=[(x-a*y)%p for x,y in zip(v,w)]
        if any(v):
            j=next(j for j,x in enumerate(v) if x)
            inv=pow(v[j],-1,p)
            pivots[j]=[(x*inv)%p for x in v]
    return len(pivots)

def taylor_lattice(E,p,r,open_disk=False,certificate=False):
    """Work in K=Q_p(pi), pi^e=p, where r=a/e.

    HNF gives a Z-lattice basis for the O_K-span of Taylor rows. Its index
    away from p is immaterial. Rational coordinates are reduced p-adically.
    """
    E=tuple(E);n=max(E);t=len(E);a=r.numerator;e=r.denominator
    cols=[]
    for k in range(n+1):
        for j in range(e):
            q,z=divmod(a*k+j,e)
            col=[0]*(e*t)
            for i,ni in enumerate(E):
                col[z*t+i]=(comb(ni,k) if ni>=k else 0)*p**q
            cols.append(s.Matrix(col))
    H=hermite_normal_form(s.Matrix.hstack(*cols))
    assert H.rows==H.cols==e*t
    Hi=H.inv()
    # To represent L/pi L, enlarge pi L to a Zp lattice and test reductions
    # through the quotient using columns in H coordinates. The pi operator
    # has a fixed integral block-shift matrix in the standard basis.
    J=s.zeros(e*t)
    for z in range(e):
        for i in range(t):
            J[((z+1)%e)*t+i,z*t+i]=p if z==e-1 else 1
    JH=J*H
    # L/pi L can be read via the F_p image of adjugate-coordinate residues;
    # simpler: exact lattice indices of pi L plus successive Taylor columns.
    # Include pL in piL (true), so all successive indices divide p^t.
    Q=JH
    det0=abs(int(Q.det()))
    base_v=vp(det0,p)
    good=[];increments=[]
    for k in range(n+1):
        v=cols[k*e]
        if open_disk:
            new=hermite_normal_form(Q.row_join(v))
            loss=vp(abs(int(Q.det())),p)-vp(abs(int(new.det())),p)
            if loss:good.append(k)
            increments.append(loss)
            Q=new
        else:
            coords=JH.inv()*v
            primitive=any(vp(x.p,p)<vp(x.q,p) for x in coords if x)
            if primitive:good.append(k)
    answer=max(good)
    if not certificate:return answer
    return {'support':list(E),'p':p,'depth':str(r),'open_disk':open_disk,
            'maximum':answer,'degree':n,'hnf_determinant_valuation':vp(abs(int(H.det())),p),
            'pi_lattice_determinant_valuation':base_v,'rank_increase_indices':good,
            'quotient_rank_increments':increments if open_disk else None,
            'hnf_basis':[[str(x) for x in row] for row in H.tolist()]}

def polynomial_witness():
    X,Y=s.symbols('X Y')
    Q=s.Poly((X-1)**7*(X+3)+2**11,X)
    expansion=s.Poly(Q.as_expr().subs(X,1+Y),Y)
    assert expansion.as_expr()==Y**8+4*Y**7+2048
    assert Q.degree()==8 and len(Q.terms())==8
    assert s.gcd(Q,Q.diff()).degree()==0
    # At slope -11/8 the endpoint valuations are equal, all others larger.
    weights={k:Fraction(vp(int(c),2))+Fraction(11,8)*k for (k,),c in expansion.terms()}
    assert weights[0]==weights[8]==11 and weights[7]>11
    return {'coefficients_low_to_high':[int(Q.nth(k)) for k in range(9)],
            'translated_coefficients':{str(k):int(c) for (k,),c in expansion.terms()},
            'root_count':8,'all_root_valuations':'11/8','squarefree':True}

def main():
    E=tuple(range(8));F=(0,1,2,3,4,5,7,8)
    assert Counter(n%2 for n in E)==Counter(n%2 for n in F)
    result={'witness':polynomial_witness(),'examples':[]}
    X,Y=s.symbols('X Y')
    W=183*X**10-235*X**8+54*X**6-6*X**4-128*X**3+3*X**2+128*X+2049
    WT=s.Poly(W.subs(X,1+Y),Y)
    assert len(s.Poly(W,X).terms())==8
    assert s.gcd(s.Poly(W,X),s.Poly(s.diff(W,X),X)).degree()==0
    A=3*X**8-X**6-X**5-3*X**4+3*X**3-X**2+3*X-1
    B=-X**9+3*X**7-2*X**6-3*X**5+2*X**4-3*X**3-3*X**2+2*X+3
    assert s.Poly(A*W+B*s.diff(W,X),X,modulus=7).as_expr()==1
    assert [vp(WT.nth(k),2) for k in (0,9,10)]==[11,1,0]
    for (k,),c in WT.terms():
        assert Fraction(vp(c,2)) >= (Fraction(11)-Fraction(10*k,9) if k<=9 else Fraction(10-k))
    result['nine_root_witness']={'coefficients_low_to_high':[int(s.Poly(W,X).nth(k)) for k in range(11)], 'translated_coefficients_low_to_high':[int(WT.nth(k)) for k in range(11)],'newton_vertices':[[0,11],[9,1],[10,0]],'deep_root_valuations':['10/9']*9,'boundary_root_valuation':'1','squarefree':True,'mod7_bezout_identity_verified':True}
    for support,expected in [(E,7),(F,8)]:
        for r,op in [(Fraction(5,4),False),(Fraction(1),True)]:
            c=taylor_lattice(support,2,r,op,True)
            assert c['maximum']==expected
            result['examples'].append(c)
    # Complete finite search for all eight-term residue multisets mod 4.
    counts=Counter();best=[];profile_certificates=[]
    for nu in compositions(8,4):
        E0=canonical(nu)
        cert=taylor_lattice(E0,2,Fraction(1),True,True)
        val=cert['maximum']
        evens=nu[0]+nu[2]
        predicted=9 if evens%4==2 else (7 if evens%4==0 and len({x%2 for x in nu})==1 else 8)
        assert val==predicted
        cert['residue_multiplicities']=list(nu)
        profile_certificates.append(cert)
        counts[val]+=1
        best.append((val,nu,E0))
    result['eight_term_open_global']={'precision':precision(8,2),'profiles':sum(counts.values()),
        'distribution':dict(sorted(counts.items())),'maximum':max(counts),
        'maximizers':[{'residue_multiplicities':list(nu),'support':list(E0)} for val,nu,E0 in best if val==max(counts)],
        'profile_certificates':profile_certificates}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
