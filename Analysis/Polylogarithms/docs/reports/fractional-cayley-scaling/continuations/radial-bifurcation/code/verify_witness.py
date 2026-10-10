"""Certify two radial turning points for an explicit rational order pair.

Finite Chebyshev sums are augmented with analytic, outward-enclosed tails.
The three signs below concern the exact infinite polylogarithm, not a
truncated model. The standard library is sufficient.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
from exact import I,SCALE,neg_power
ROOT=Path(__file__).resolve().parents[1]
N=16

def coefficients(a:I,b:I):
    H=I.point(0);p={}
    for n in range(2,2*N+4):
        H+=neg_power(n-1,b)
        p[n]=neg_power(n,a)*H
    return p

def P_and_derivative(k:int,y:I,p):
    value=p[k+2];derivative=I.point(0)
    for j in range(1,k+2):
        derivative=derivative*(2*y)+2*value
        value=value*(2*y)+((-1)**j*comb(k+1,j))*p[k+2+j]
    return value,derivative

def tail_bounds(t:I):
    # For |eta|<=1 and a,b>=0: |P_k(eta)|<=(2k+3)*3**(k+1).
    tau=I(0,max(abs(t.lo),abs(t.hi)));q=3*tau;n=N+1
    if q.hi>=SCALE:raise ValueError('tail series does not converge')
    r=3*q**n*((2*n+3)/(1-q)+2*q/(1-q)**2)
    rt=9*q**(n-1)*((2*n*n+3*n)/(1-q)+(4*n+3)*q/(1-q)**2+2*q*(1+q)/(1-q)**3)
    # Cauchy radius 1/4 is permitted for real eta in [1/4,3/4].
    return r,rt,4*r

def evaluate(t:I,y:I,p):
    if y.lo<SCALE//4 or y.hi>3*SCALE//4:
        raise ValueError('eta must be in [1/4,3/4] for derivative tail')
    val=I.point(0);dt=I.point(0);dy=I.point(0)
    for k in range(N+1):
        pk,dpk=P_and_derivative(k,y,p)
        val+=pk*t**k;dy+=dpk*t**k
        if k:dt+=k*pk*t**(k-1)
    bounds=tail_bounds(t)
    return tuple(z+I(-r.hi,r.hi) for z,r in zip((val,dt,dy),bounds))

def main():
    if not __debug__:raise RuntimeError('Do not run verifiers with python -O')
    proposal=json.loads((ROOT/'certificates/witness_proposal.json').read_text())
    af,bf=F(proposal['a']),F(proposal['b']);assert af>0 and bf>0
    p=coefficients(I.point(af),I.point(bf));mu=p[3]/(2*p[2])
    center=F(mu.lo+mu.hi,2*SCALE);width=F(1,10**8)
    left,right=center-width,center+width
    T=I.bounds(0,F(1,4000));Y=I.bounds(left,right)
    psi_left=evaluate(T,I.point(left),p)[0];psi_right=evaluate(T,I.point(right),p)[0]
    dY=evaluate(T,Y,p)[2]
    assert psi_left.hi<0<psi_right.lo
    assert F(dY.lo,SCALE)>F('0.99900') and F(dY.hi,SCALE)<F('0.99906')
    # Thus a unique analytic root eta(t) exists throughout this explicit strip.
    rows=[]
    for j,row in enumerate(proposal['samples']):
        t=F(row['t']);c=F(row['eta_approx']);rad=F(1,10**42)
        lo,hi=c-rad,c+rad;y=I.bounds(lo,hi);ti=I.point(t)
        assert left<lo<hi<right
        assert evaluate(ti,I.point(lo),p)[0].hi<0
        assert evaluate(ti,I.point(hi),p)[0].lo>0
        _,dt,dy=evaluate(ti,y,p);assert dy.lo>0
        slope=-dt/dy
        if j==1:assert slope.lo>0
        else:assert slope.hi<0
        rows.append({'t':str(t),'eta_interval':[str(lo),str(hi)],'eta_t':slope.dump(),
                     'diagnostic':slope.diagnostic(), 'tail_bounds':[x.dump() for x in tail_bounds(ti)]})
    # Simple decimal inequalities for the article's table.
    coarse=[('-7.59e-19','-7.56e-19'),('2.52e-19','2.54e-19'),('-7.59e-19','-7.56e-19')]
    for row,(lo,hi) in zip(rows,coarse):
        x=row['eta_t'];assert F(x['lo'])/SCALE>F(lo) and F(x['hi'])/SCALE<F(hi)
        row['coarse_bounds']=[lo,hi]
    doc={'status':'PASS','a':str(af),'b':str(bf),'decimal_a':proposal['a'],'decimal_b':proposal['b'],
         'N':N,'max_n':2*N+3,'strip':{'t':['0','1/4000'],'eta':[str(left),str(right)],
            'psi_left':psi_left.dump(),'psi_right':psi_right.dump(),'psi_eta':dY.dump()},
         'samples':rows,'conclusion':'At least one strict local minimum followed by at least one strict local maximum on 0<rho<1/sqrt(4000).'}
    (ROOT/'certificates/witness_verified.json').write_text(json.dumps(doc,indent=2)+'\n')
    print(json.dumps({'status':'PASS','a':proposal['a'],'b':proposal['b'],
        'psi_eta_strip':dY.diagnostic(),'samples':[{k:v for k,v in x.items() if k in ('t','diagnostic','coarse_bounds')} for x in rows]},indent=2))
if __name__=='__main__':main()
