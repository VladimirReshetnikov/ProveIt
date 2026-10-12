#!/usr/bin/env python3
"""Exact checks for polarized Bernoulli cancellation and mixed even-tail moments.
Only the Python standard library is required. MZV words are formal labels;
products of singleton zetas are expanded by ordered equality partitions.
The independent route uses finite summation by parts, not the new recurrence.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations_with_replacement
from math import comb, factorial
import json
from pathlib import Path

# Linear combinations of strict descending multiple-zeta words.
# () denotes 1; ('gamma',) denotes Euler's constant in intermediate cutoffs.

def add(*xs):
    out={}
    for x in xs:
        for w,c in x.items(): out[w]=out.get(w,F(0))+c
    return {w:c for w,c in out.items() if c}

def scale(x,c):
    c=F(c)
    return {w:c*v for w,v in x.items() if c*v}

def atom(w,c=1): return {tuple(w):F(c)} if c else {}

@lru_cache(None)
def bern(n):
    if n==0:return F(1)
    return -sum((F(comb(n+1,j))*bern(j) for j in range(n)),F())/F(n+1)

def halfbern(n): return (F(2)**(1-n)-1)*bern(n)

@lru_cache(None)
def faulhaber(q):
    return tuple((a,F(comb(q+1,a),q+1)*(F(1,2) if q+1-a==1 else bern(q+1-a))) for a in range(1,q+2))

def masks(P, proper=False, even=False):
    for m in range(1,(1<<len(P))-(1 if proper else 0)):
        S=tuple(P[i] for i in range(len(P)) if m>>i&1)
        if even and len(S)%2:continue
        R=tuple(P[i] for i in range(len(P)) if not(m>>i&1))
        yield S,R

@lru_cache(None)
def words(P):
    if not P:return {():F(1)}
    out={}
    for S,R in masks(P):
        for w,c in words(R).items():
            q=(sum(S),)+w;out[q]=out.get(q,F())+c
    return out

@lru_cache(None)
def tail_anchor(P,r):
    assert r>=1 and (P or r>=2)
    return {w+(r,):c for w,c in words(P).items()}

@lru_cache(None)
def symmetric_anchor(P,r):
    return add(scale(tail_anchor(P,r),2),*(tail_anchor(R,r+sum(S)) for S,R in masks(P)))

@lru_cache(None)
def difference_anchor(P,h):
    assert P and h<=0
    return {w[:-1]+(w[-1]-h,):c for w,c in words(P).items()}

@lru_cache(None)
def asymptotic_single(p,k):
    if k==p-1:return F(1,p-1)
    if k==p:return F(-1,2)
    ell=k-p+1
    if ell<2 or ell%2:return F()
    return bern(ell)*F(factorial(p+ell-2),factorial(p-1)*factorial(ell))

@lru_cache(None)
def boundary(P,k):
    if not P:return F(k==0)
    if k<sum(p-1 for p in P):return F()
    return sum((asymptotic_single(P[0],j)*boundary(P[1:],k-j) for j in range(k+1)),F())

@lru_cache(None)
def cutoff(P,q):
    # CT_N sum_{n=1}^N n^q prod_{p in P} zeta(p,n+1).
    if not P:
        if q>=0:return {}
        if q==-1:return atom(('gamma',))
        return atom((-q,))
    if q<0:return tail_anchor(P,-q)
    out=atom((),sum((f*boundary(P,a) for a,f in faulhaber(q)),F()))
    for S,R in masks(P):
        out=add(out,*(scale(cutoff(R,a-sum(S)),f) for a,f in faulhaber(q)),scale(cutoff(R,q-sum(S)),-1))
    return out

@lru_cache(None)
def direct_C(P,k):
    return add(atom((),boundary(P,k)),*(cutoff(R,k-sum(S)) for S,R in masks(P)))

@lru_cache(None)
def direct_M(P,m):
    return add(*(scale(direct_C(P,k),F(comb(m+1,k),m+1)*halfbern(m+1-k)) for k in range(1,m+2)))

@lru_cache(None)
def new_C(P,k):
    if k<=0:return difference_anchor(P,k)
    d=len(P)
    assert (k-d-1)%2==0
    out={}
    for i,p in enumerate(P):
        J=P[:i]+P[i+1:]
        m=k-p
        if m<0:
            out=add(out,scale(symmetric_anchor(J,-m),F(1,2)))
        else:
            if J:
                for r in range(m%2,m+1,2):
                    out=add(out,scale(new_M(J,r),F(comb(m,r))*F(2)**(r-m)))
            if m==0:out=add(out,scale(words(J),F(-1,2)))
    for S,J in masks(P,proper=True,even=True):
        out=add(out,scale(new_C(J,k-sum(S)),-bern(len(S))))
    return out

@lru_cache(None)
def new_M(P,m):
    assert P and (m-len(P))%2==0
    return add(*(scale(new_C(P,k),F(comb(m+1,k),m+1)*halfbern(m+1-k)) for k in range(1,m+2) if (k-len(P)-1)%2==0))

def text_expr(x):
    if not x:return '0'
    def sk(w):return (0,()) if not w else (1,tuple(str(v) for v in w))
    ts=[]
    for w,c in sorted(x.items(),key=lambda kv:sk(kv[0])):
        z='1' if not w else ('gamma' if w==('gamma',) else 'zeta('+','.join(map(str,w))+')')
        ts.append(str(c)+'*'+z)
    return ' + '.join(ts)

def serial(x):return [{'word':list(w),'coefficient':str(c)} for w,c in sorted(x.items(),key=lambda kv:str(kv[0]))]

def determinant(A):
    A=[[F(x) for x in row] for row in A]
    result=F(1)
    for j in range(len(A)):
        pivot=next((i for i in range(j,len(A)) if A[i][j]),None)
        if pivot is None:return F()
        if pivot!=j:A[pivot],A[j]=A[j],A[pivot];result=-result
        v=A[j][j];result*=v
        for i in range(j+1,len(A)):
            r=A[i][j]/v
            for k in range(j+1,len(A)):A[i][k]-=r*A[j][k]
            A[i][j]=F()
    return result

def reduce_examples(x):
    """Exact reduction in basis (1,z2,z3,z4,z6,E5,B7,A9).
    A9 is its displayed ordinary MZV tail anchor. B7 is initially its
    explicit seven-term MZV combination, before Hoffman's weight-7 reduction.
    The remaining replacements are classical low-weight identities.
    """
    A9=new_M((2,2,2,4),0)
    B7={(2,2,2,1):F(1),(4,2,1):F(1,2),(2,4,1):F(1,2),
        (6,1):F(1,6),(2,2,3):F(1,2),(4,3):F(1,6),(7,):F(-1,12)}
    a=x.get((2,2,2,3),F())/6;x=add(x,scale(A9,-a))
    b=x.get((2,2,2,1),F());x=add(x,scale(B7,-b))
    z23=x.pop((2,3),F());z41=x.pop((4,1),F());z5=x.pop((5,),F())
    c5=F(9,2)*z23+2*z41+z5;c23=-2*z23-z41
    assert c5==F(-5,2)*c23,(c5,c23)
    e=-c23/3
    row=[x.pop((),F()),x.pop((2,),F()),x.pop((3,),F())+x.pop((2,1),F()),
         x.pop((4,),F())+F(3,4)*x.pop((2,2),F()),
         x.pop((6,),F())+F(3,16)*x.pop((2,2,2),F()),e,b,a]
    assert not x,x
    return row

def linear_rows(*terms):
    return [sum((F(c)*row[i] for c,row in terms),F()) for i in range(8)]

def cosh_moment(P,m):
    if m<0:return [F()]*8
    return linear_rows(*[(F(comb(m,r))*F(2)**(r-m),reduce_examples(new_M(P,r)))
                         for r in range(m%2,m+1,2)])

def coordinate_checks():
    results={}
    rows3=[[row[i] for i in (0,1,2,3,5,4)]
           for row in (reduce_examples(new_M((2,2,4),m)) for m in range(1,12,2))]
    rows4=[reduce_examples(new_M((2,2,2,4),m)) for m in range(0,16,2)]
    det3=determinant(rows3);det4=determinant(rows4)
    assert det3==F(-309971,13243436236800)
    assert det4==F(-806331520717,2249069145523200000)
    results['triple']={'orders':[2,2,4],'basis':['1','zeta(2)','zeta(3)','zeta(4)','E5','zeta(6)'],
                       'moment_orders':list(range(1,12,2)),
                       'rows':[[str(x) for x in row] for row in rows3],'determinant':str(det3)}
    results['quartic']={'orders':[2,2,2,4],'basis':['1','zeta(2)','zeta(3)','zeta(4)','zeta(6)','E5','B7','A9'],
                        'moment_orders':list(range(0,16,2)),
                        'rows':[[str(x) for x in row] for row in rows4],'determinant':str(det4)}
    # Check the two simplified anchored generating identities coefficientwise.
    unit=lambda i,c: [F(c) if j==i else F() for j in range(8)]
    for k in range(2,30,2):
        rhs=linear_rows((2,cosh_moment((2,4),k-2)),(1,cosh_moment((2,2),k-4)))
        corrections={2:unit(4,F(-5,8)),4:unit(3,F(-7,4)),6:unit(1,F(-1,2)),8:unit(0,F(1,4))}
        rhs=linear_rows((1,rhs),(1,corrections.get(k,unit(0,0))))
        assert rhs==reduce_examples(new_C((2,2,4),k)),k
    for k in range(1,30,2):
        rhs=linear_rows((3,cosh_moment((2,2,4),k-2)),(1,cosh_moment((2,2,2),k-4)))
        if k>=5:rhs=linear_rows((1,rhs),(F(-1,2),reduce_examples(new_C((2,4),k-4))))
        if k>=7:rhs=linear_rows((1,rhs),(F(-1,2),reduce_examples(new_C((2,2),k-6))))
        corrections={1:unit(7,1),3:unit(6,6),5:unit(5,F(-2,3))}
        rhs=linear_rows((1,rhs),(1,corrections.get(k,unit(0,0))))
        assert rhs==reduce_examples(new_C((2,2,2,4),k)),k
    # A rational ordinary-sum row is verified without numerical constants.
    coeffs=[2526903,80590275,474388272,753887520,353617920,42197760]
    row=[sum((F(c)*r[j] for c,r in zip(coeffs,rows3)),F()) for j in range(6)]
    assert row==[F(-6199420),F(),F(),F(),F(),F()]
    results['rational_sum']={'odd_weight_coefficients':coeffs,'value':'-6199420',
        'subtraction_coefficients_by_even_degree':{'0':'338793712/7','2':'180958272','4':'108495360','6':'14065920'}}
    results['simplified_generator_checks']=29
    return results

def check_cubic_telescoper():
    """A separate exact Laurent-polynomial certificate; no MZVs are used."""
    zero=(0,0,0,0)
    one=atom(zero)
    def mon(i,p=1):
        w=[0,0,0,0];w[i]=p
        return atom(w)
    def mul(*xs):
        out=one
        for x in xs:
            nxt={}
            for u,c in out.items():
                for v,e in x.items():
                    w=tuple(a+b for a,b in zip(u,v))
                    nxt[w]=nxt.get(w,F())+c*e
            out={w:c for w,c in nxt.items() if c}
        return out
    n,a,b,c=(mon(i) for i in range(4))
    def J(n,a,b,c):
        return add(scale(mul(n,n,a,a,b),F(-1,2)),
                   scale(mul(a,a,a),F(1,6)),
                   scale(mul(a,b),F(-1,2)),scale(c,F(-1,6)))
    prev=[add(a,mon(0,-2)),add(b,mon(0,-4)),add(c,mon(0,-6))]
    increment=mul(prev[0],prev[1],add(one,scale(mul(add(n,scale(one,F(-1,2))),prev[0]),-1)))
    residual=add(J(n,a,b,c),scale(J(add(n,scale(one,-1)),*prev),-1),scale(increment,-1))
    assert residual=={}
    endpoint=F(35,8)/6-F(7,4)/2-F(1,6)
    assert endpoint==F(-5,16)
    return {'laurent_polynomial_residual':{},'J_zero_as_multiple_of_zeta_6':str(endpoint),'status':'pass'}

def main():
    results={'description':'Exact formal-MZV comparisons against an independent finite-cutoff summation-by-parts algorithm. No numerical identity recognition is used.','checks':[],'examples':{}}
    total=0
    for d in range(1,5):
        for P in combinations_with_replacement((2,4,6),d):
            for m in range(d%2,18,2):
                left=direct_M(P,m);right=new_M(P,m)
                assert left==right,(P,m,text_expr(add(left,scale(right,-1))))
                assert ('gamma',) not in right
                assert all(not w or (w[0]>=2 and all(isinstance(a,int) and a>=1 for a in w)) for w in right)
                assert all(sum(w)<=sum(P)-1-(d%2) for w in right)
                total+=1
            results['checks'].append({'orders':P,'moment_orders':list(range(d%2,18,2)),'status':'pass'})
    for P,ms in [((2,2,4),(1,3,5,7)),((2,2,2,4),(0,2,4,6))]:
        key=','.join(map(str,P));results['examples'][key]={}
        for m in ms:
            x=new_M(P,m);results['examples'][key][str(m)]=serial(x)
            print('M',P,m,'=',text_expr(x))
    # Boundary polarization at all attainable coefficients, using independent
    # polynomial asymptotic products rather than the moment recurrence.
    boundary_checks=0
    for d in range(1,6):
        for P in combinations_with_replacement((2,4,6),d):
            for k in range((d+1)%2,30,2):
                lhs=boundary(P,k)
                for i,p in enumerate(P):lhs+=F(1,2)*boundary(P[:i]+P[i+1:],k-p)
                for S,J in masks(P,even=True):lhs+=bern(len(S))*boundary(J,k-sum(S))
                assert lhs==0,(P,k,lhs)
                boundary_checks+=1
    results['moment_checks']=total;results['boundary_checks']=boundary_checks
    results['coordinate_certificates']=coordinate_checks()
    results['cubic_telescoper']=check_cubic_telescoper()
    results['status']='all exact checks passed'
    out=Path(__file__).resolve().parents[1]/'results'/'mixed_tail_verification.json';out.write_text(json.dumps(results,indent=2)+'\n')
    print('PASS',total,'moment checks and',boundary_checks,'boundary parity checks')
    print('Output:',out)

if __name__=='__main__':main()
