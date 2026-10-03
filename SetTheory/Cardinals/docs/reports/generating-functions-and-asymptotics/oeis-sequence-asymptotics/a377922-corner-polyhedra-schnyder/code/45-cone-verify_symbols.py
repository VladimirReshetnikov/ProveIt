"""Exact kernel, corrector, covariance and regeneration checks for both models."""
from pathlib import Path
import json
import sympy as s
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)
x, y, u = s.symbols('x y u')
variables = [x, y]
def ev(f):
    return s.simplify(f.subs({x: 1, y: 1, u: 1}))
def dg(f, v):
    return v * s.diff(f, v)
def matrix_strings(A):
    return [[str(v) for v in row] for row in A.tolist()]
D0 = (1-x**-2)*(1-y**2)
MP = s.Matrix([[y**2/D0, x/y+x**-1*y/D0],
               [x/y+x**-1*y/D0, x**-2/D0]])
H = 1-x**-2-y**2-2*x**-2*y**2
B = x/y+x**-1*y/H
MS = s.Matrix([[x**-2/H, B], [B, y**2/H]])
W = s.Matrix([[x**-2*y**2, x**-1*y**3],
              [x**-3*y, x**-2*y**2]])/(1-x**-2-y**2)
E = s.Matrix([[0, x/y], [x/y, 0]])
assert s.simplify(MS-E*(s.eye(2)-W).inv()) == s.zeros(2)
models = {
    'P': (s.simplify(MP.subs({x:s.sqrt(3)*x,y:y/s.sqrt(3)}, simultaneous=True)*s.Rational(2,9)),
          s.Rational(1,6), s.Rational(1,10),
          s.Matrix([[s.Rational(16,5),-s.Rational(9,5)],[-s.Rational(9,5),s.Rational(16,5)]]),
          [s.Matrix([[s.Rational(12,5),-s.Rational(9,5)],[-s.Rational(9,5),4]]),
           s.Matrix([[4,-s.Rational(9,5)],[-s.Rational(9,5),s.Rational(12,5)]])], s.Rational(2,5), s.Rational(9,16)),
    'S': (s.simplify(MS.subs({x:2*x,y:y/2}, simultaneous=True)*s.Rational(3,16)),
          -s.Rational(1,8), -s.Rational(1,14),
          s.Matrix([[s.Rational(36,7),-s.Rational(88,21)],[-s.Rational(88,21),s.Rational(36,7)]]),
          [s.Matrix([[6,-s.Rational(88,21)],[-s.Rational(88,21),s.Rational(30,7)]]),
           s.Matrix([[s.Rational(30,7),-s.Rational(88,21)],[-s.Rational(88,21),6]])], s.Rational(2,7), s.Rational(22,27))
}
report = {'arithmetic': 'exact rational and symbolic', 'S_face_resolvent': 'PASS', 'models': {}}
for name, (K,d,h,Sigma,expected_C,var_l,rho) in models.items():
    internal = K.subs({x:1,y:1})
    assert K == K.T
    assert internal*s.ones(2,1) == s.ones(2,1)
    assert internal.T*s.ones(2,1) == s.ones(2,1)
    assert Sigma.det() > 0
    assert -Sigma[0,1]/s.sqrt(Sigma[0,0]*Sigma[1,1]) == rho
    all_C = []
    for reverse in [False, True]:
        mat = K.T.subs({x:1/x,y:1/y}, simultaneous=True) if reverse else K
        hh = [-h,h] if reverse else [h,-h]
        cs=[]
        for i in range(2):
            for v in variables:
                drift=ev(dg(sum(mat[i,j] for j in range(2)),v))
                assert drift == (-1 if reverse else 1)*(d if i==0 else -d)
                assert s.simplify(drift+sum(internal[i,j]*(hh[j]-hh[i]) for j in range(2))) == 0
            C=s.Matrix([[s.simplify(sum(ev(dg(dg(mat[i,j],v),w))+
                (hh[j]-hh[i])*(ev(dg(mat[i,j],v))+ev(dg(mat[i,j],w)))+
                (hh[j]-hh[i])**2*internal[i,j] for j in range(2))) for w in variables] for v in variables])
            assert C == expected_C[i]
            cs.append(C)
        assert (cs[0]+cs[1])/2 == Sigma
        all_C.append([matrix_strings(C) for C in cs])
    cycles={}
    for i in range(2):
        j=1-i
        R=u*K[i,i]+u**2*K[i,j]*K[j,i]/(1-u*K[j,j])
        mean_l=ev(s.diff(R,u))
        mean_y=[ev(dg(R,v)) for v in variables]
        cov=s.Matrix([[ev(dg(dg(R,v),w)) for w in variables] for v in variables])
        variance=ev(s.diff(R,u,2)+s.diff(R,u))-mean_l**2
        assert ev(R)==1 and mean_l==2 and mean_y==[0,0]
        assert cov==2*Sigma and variance==var_l
        cycles['even' if i==0 else 'odd']={
            'return_symbol':str(s.factor(R)), 'mean_duration':str(mean_l),
            'mean_displacement':[str(v) for v in mean_y],
            'displacement_covariance':matrix_strings(cov),
            'duration_variance':str(variance),
            'duration_displacement_covariance':[str(ev(dg(s.diff(R,u),v))) for v in variables]
        }
    report['models'][name]={
        'kernel':str(K), 'internal_transition_matrix':matrix_strings(internal),
        'even_drift':[str(d),str(d)], 'even_corrector':[str(h),str(h)],
        'conditional_covariances_forward_and_reverse':all_C,
        'covariance_per_counted_step':matrix_strings(Sigma),
        'cosine_whitened_angle':str(rho), 'alpha_exact':str(1+s.pi/s.acos(rho)),
        'alpha_decimal_60_digits':str(s.N(1+s.pi/s.acos(rho),60)),
        'cycles':cycles, 'assertions':'PASS'
    }
(OUT/'symbolic-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: both exact kernels, forward/reverse correctors, conditional covariances, both parity return laws, and cone angles')
