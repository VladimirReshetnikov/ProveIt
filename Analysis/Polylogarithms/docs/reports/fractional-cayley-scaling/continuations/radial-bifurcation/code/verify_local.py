"""Exact contraction certificate for K=Q=0 and its nondegeneracy."""
from pathlib import Path
from fractions import Fraction as F
import json
from exact import I,SCALE,normalized_coefficients,threshold_value,threshold_derivatives
ROOT=Path(__file__).resolve().parents[1]

RECT=(('1.0014301809614951381293517293887015374543',
       '1.0014301809614951381293517293887015374544'),
      ('0.9974937898734204210746055930669544902305',
       '0.9974937898734204210746055930669544902306'))

def mid(x:I):return F(x.lo+x.hi,2*SCALE)
def matvec(A,x):return [sum((a*b for a,b in zip(row,x)),I.point(0)) for row in A]
def inside(x:I,lo,hi):return F(x.lo,SCALE)>F(lo) and F(x.hi,SCALE)<F(hi)
def coarse(x:I,lo:str,hi:str):
    assert inside(x,lo,hi),(x.dump(),lo,hi)
    return [lo,hi]

def main():
    if not __debug__:raise RuntimeError('Do not run verifiers with python -O')
    X=[I.bounds(*r) for r in RECT];c=[(F(lo)+F(hi))/2 for lo,hi in RECT]
    cp=[I.point(v) for v in c]
    mu,K,Q,R=normalized_coefficients(*X)
    mu0,K0,Q0,R0=normalized_coefficients(*cp)
    a,b,d,e=map(mid,(K0.a,K0.b,Q0.a,Q0.b));det=a*e-b*d
    C=[[e/det,-b/det],[-d/det,a/det]]
    J=[[K.a,K.b],[Q.a,Q.b]]
    H=[[I.point(int(i==j))-sum((C[i][k]*J[k][j] for k in range(2)),I.point(0)) for j in range(2)] for i in range(2)]
    norm=max(sum(max(abs(h.lo),abs(h.hi)) for h in row) for row in H)
    assert F(norm,SCALE)<F(3,10**32)
    shift=matvec(C,[K0.v,Q0.v]);rem=matvec(H,[x-y for x,y in zip(X,cp)])
    image=[cp[i]-shift[i]+rem[i] for i in range(2)]
    for i in range(2):assert inside(image[i],*RECT[i]),('not self mapping',i,image[i].dump())
    D=K.a*Q.b-K.b*Q.a
    qp=threshold_derivatives(K,Q)[2]
    coarse_bounds={
        'R':coarse(R,'-0.00000000003368744536','-0.00000000003368744535'),
        'det_D_KQ':coarse(D,'-0.0000000008315139844','-0.0000000008315139843'),
        'q_prime_at_transition':coarse(qp,'0.00000004870284716','0.00000004870284717'),
        'K_a':coarse(K.a,'-0.017073210967','-0.017073210965'),
        'mu':coarse(mu.v,'0.4999997521943034412547442623','0.4999997521943034412547442625')}
    # Endpoint signs used in the global concavity proof.
    mesh=json.loads((ROOT/'certificates/global_mesh.json').read_text())
    ra=mesh['roots']['9/10'];A=I.bounds(ra['lo'],ra['hi']);B=I.point(F(9,10))
    assert threshold_value(I.point(F(ra['lo'])),B).lo>0
    assert threshold_value(I.point(F(ra['hi'])),B).hi<0
    q09=normalized_coefficients(A,B)[2].v;assert q09.hi<0
    A=I.bounds('1.00057049936559087278','1.00057049936559087279');B=I.point(F(999,1000))
    assert threshold_value(I(A.lo,A.lo),B).lo>0
    assert threshold_value(I(A.hi,A.hi),B).hi<0
    q0999=normalized_coefficients(A,B)[2].v
    coarse(q0999,'2.92779196e-11','2.92779197e-11')
    # Exact rational check of K(1,1)=Q(1,1)=0.
    p={n:sum((F(1,j) for j in range(1,n)),F(0))/n for n in range(2,8)}
    m=p[3]/(2*p[2]);k=-(4*p[3]*m*m-4*p[4]*m+p[5])/(2*p[2])
    q=-((8*p[3]*m-4*p[4])*k+8*p[4]*m**3-12*p[5]*m*m+6*p[6]*m-p[7])/(2*p[2])
    assert k==q==0
    doc={'status':'PASS','rectangle':RECT,'arithmetic':'outward dyadic, 256 bits',
         'contraction_norm_upper':{'numerator':str(norm),'denominator':str(SCALE)},
         'image':[x.dump() for x in image], 'inverse_preconditioner':[[str(x) for x in row] for row in C],
         'R':R.dump(),'mu':mu.v.dump(),'determinant':D.dump(),'q_prime':qp.dump(),'K_a':K.a.dump(),
         'coarse_bounds':coarse_bounds,'q_at_0_9':q09.dump(),'q_at_0_999':q0999.dump(),'q_at_1':'0 exactly'}
    (ROOT/'certificates/local_verified.json').write_text(json.dumps(doc,indent=2)+'\n')
    print(json.dumps({'status':'PASS','rectangle':RECT,'coarse_bounds':coarse_bounds,
                      'contraction_norm_diagnostic':float(F(norm,SCALE)),
                      'q_0_9':q09.diagnostic(),'q_0_999':q0999.diagnostic()},indent=2))
if __name__=='__main__':main()
