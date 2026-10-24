#!/usr/bin/env python3
"""Compact polynomial norms; all operations are binary integer arithmetic."""
from pathlib import Path
import importlib.util
import json
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'new_integer_compression'
sys.path.insert(0,str(SOURCE))
spec=importlib.util.spec_from_file_location('reference_build',SOURCE/'build.py')
reference=importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)

def norm4(d,Z,A,B,D,Cnum,delta):
    """delta^8 times the sixteen-factor four-root norm."""
    s,p,m=d.add,d.sub,d.mul
    sq=lambda x:m(x,x)
    k=lambda n,x:m(d.lit(n),x)
    sigma=s(s(A,B),D)
    AB=m(A,B)
    pairs=s(AB,m(s(A,B),D))
    prod=m(AB,D)
    Z2=sq(Z); delta2=sq(delta); delta3=m(delta2,delta)
    dz=m(delta,Z2)
    ahat=s(m(delta,p(Z2,sigma)),Cnum)
    ahat2=sq(ahat)
    tz=m(m(delta,Cnum),Z2)
    khat=s(ahat2,k(4,p(tz,m(delta2,pairs))))
    rhat=k(16,m(delta3,prod))
    bhat=p(m(ahat,khat),rhat)
    ehat=p(s(sq(khat),k(16,m(tz,ahat2))),k(4,m(rhat,s(dz,Cnum))))
    return p(sq(ehat),k(64,m(tz,sq(bhat))))

def norm3(d,Z,A,D,Cnum,delta):
    """delta^4 times the eight-factor three-root norm."""
    s,p,m=d.add,d.sub,d.mul
    sq=lambda x:m(x,x)
    k=lambda n,x:m(d.lit(n),x)
    z2=sq(Z); ad=s(A,D); delta2=sq(delta)
    core=p(z2,ad)
    even=s(m(delta2,p(sq(core),k(4,m(A,D)))),
           s(m(k(2,delta),m(Cnum,p(k(3,z2),ad))),sq(Cnum)))
    odd_cut=k(-4,m(Z,s(m(delta,core),Cnum)))
    return p(sq(even),m(m(delta,Cnum),sq(odd_cut)))

class QuadraticAlgebra:
    """Pairs e+o*w with w^2=radicand; no divisions are used."""
    def __init__(self, base, radicand):
        self.base=base; self.radicand=radicand; self.zero=base.lit(0)
    def scalar(self,x): return (x,self.zero)
    def lit(self,n): return self.scalar(self.base.lit(n))
    def add(self,x,y):
        return (self.base.add(x[0],y[0]),self.base.add(x[1],y[1]))
    def sub(self,x,y):
        return (self.base.sub(x[0],y[0]),self.base.sub(x[1],y[1]))
    def mul(self,x,y):
        b=self.base
        if x==y:
            return (b.add(b.mul(x[0],x[0]),b.mul(self.radicand,b.mul(x[1],x[1]))),
                    b.mul(b.lit(2),b.mul(x[0],x[1])))
        return (b.add(b.mul(x[0],y[0]),b.mul(self.radicand,b.mul(x[1],y[1]))),
                b.add(b.mul(x[0],y[1]),b.mul(x[1],y[0])))
    def norm(self,x):
        b=self.base
        return b.sub(b.mul(x[0],x[0]),b.mul(self.radicand,b.mul(x[1],x[1])))

def build(n):
    normalized=n<=14
    variables=['J6' if normalized else 'J3','C','z','h','r','v_scale','w3','c','T',
               'pair_root','pair_pos1','pair_pos2','pair_pos3','xi']
    if n==13:
        variables.remove('pair_pos1')
        variables[variables.index('c')]='c1'
    if n>=15:variables.insert(3,'f')
    if n==16:variables.insert(9,'gamma')
    defs=reference.definitions(normalized)
    if n==13:
        defs['c']='2*c1+1'
        defs['Bguard']='det*eta_zeta-(pair_root**2-det-eta_zeta+1)**2-1-pair_pos2**2-pair_pos3*(pair_pos3+1)'
    g=reference.DAG(variables,reference.PORTS,defs)
    a=reference.Algebra(g); r=g.parse
    if n==13:
        Z=r('H*(xi+18*f_center+3*t+2*V)+2*D0')
        radical=r('2916*H**2*Bguard')
        qa=QuadraticAlgebra(a,radical)
        pair=norm4(qa,(Z,a.lit(-1)),qa.scalar(r('324*H**2*F2')),
            qa.scalar(r('36*H**2*A')),qa.scalar(r('4*Dm')),
            qa.scalar(r('4*H**2*(Q*V**2-1)')),qa.scalar(r('delta')))
        N=qa.norm(pair); out=N; rows=[N]
        finalizer='single five-root norm; no additional finalizer'
    elif n==14:
        Z=r('H*(xi+18*f_center+3*t+2*V)+2*D0')
        N=norm4(a,Z,r('324*H**2*F2'),r('36*H**2*A'),r('4*Dm'),
                  r('4*H**2*(Q*V**2-1)'),r('delta'))
        G=r('G'); G2=a.pow(G,2)
        out=a.add(a.add(N,G2),a.mul(N,G2)); rows=[G,N]
        finalizer='N + G^2 + N*G^2'
    elif n==15:
        Z=r('H*(xi+3*t+2*V)+2*D0')
        N=norm3(a,Z,r('36*H**2*A'),r('4*Dm'),r('4*H**2*(Q*V**2-1)'),r('delta'))
        rows=[r('Strong'),r('G'),N]
        S=g.sumsq(rows[:2]); out=a.add(a.add(N,S),a.mul(N,S))
        finalizer='N + S + N*S, S=Strong^2+G^2'
    else:
        L=r('delta*(xi**2+(6*t+4*V)*xi+9*ell)-4*(V**2-1)')
        ht=r('12*delta*t*V')
        N=a.add(a.add(a.pow(L,2),a.mul(a.lit(2),a.mul(L,ht))),r('tail'))
        rows=[r('Main'),r('Strong'),r('G'),N]
        out=g.sumsq(rows); finalizer='sum of squares of four residuals'
    name={13:'five_root_integer13_compact',14:'four_root_integer14_compact',15:'three_root_integer15_compact',16:'fixed3_crt_integer16_compact'}[n]
    packet=reference.live_packet(g,out,rows,name,dict(finalizer=finalizer,norm_output=N,
        coefficient_binding='../new_integer_compression/coefficients/BINDING.json',
        proof_status='Ordinary arithmetic proof with identified inherited calibration; no new proof-assistant certificate.',
        construction='Distinct divisibility orders at prime 3 separate the weighted Pell radicals.'))
    packet['polynomial_definitions']={key:defs[key] for key in defs if key in g.regs}
    packet['exact_total_degree']={13:1392,14:696,15:244,16:108}[n]
    packet['exact_degree_evidence']='Identity with the cancellation-aware reference circuit, symbolic upper bounds, and the finite-field leading coefficient certificate.'
    (ROOT/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
    return {k:packet[k] for k in ['name','variable_count','operation_count','operation_histogram','propagated_degree_upper_bound']}

if __name__=='__main__':
    summary=[build(n) for n in (16,15,14,13)]
    (ROOT/'BUILD_METRICS.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
