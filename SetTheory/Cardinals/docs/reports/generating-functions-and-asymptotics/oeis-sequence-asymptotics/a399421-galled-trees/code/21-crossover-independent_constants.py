"""Independent nested-radical constants; no exact-row data used to compute them.
Depth/precision stability is not interval certification.
"""
import json
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]

def compute(depth, dps):
    with mp.workdps(dps):
        def U(x, level=depth):
            if level==0:
                return mp.mpf(0)
            q=2*x+U(x*x,level-1)
            return q/(1+mp.sqrt(1-q))
        R=mp.findroot(lambda r:1-2*r-U(r*r),(mp.mpf('.4'),mp.mpf('.405')))
        A=1+R*mp.diff(U,R*R)
        K=mp.diff(U,R*R)+2*R*R*mp.diff(U,R*R,2)
        gamma=mp.sqrt(2*R*A);c=1/(mp.sqrt(R)*A)
        f4=-1/(8*A)+1/(4*A*R)+K/(2*A**3)
        B=A*(1-5*R)+2*R*K/A
        return dict(R=R,A=A,K=K,gamma0=gamma,c=c,f4=f4,B=B)

mp.mp.dps=90
reference=compute(12,90)
variants={'depth_10_dps_90':compute(10,90),'depth_12_dps_65':compute(12,65)}
diffs={name:{key:mp.nstr(abs(v[key]-reference[key]),15) for key in reference} for name,v in variants.items()}
assert all(abs(v[key]-reference[key])<mp.mpf('1e-60') for v in variants.values() for key in reference)
finite=json.loads((ROOT/'results/crossover-checks.json').read_text())['constants']
for key in ('R','A','gamma0','c'):
    assert abs(mp.mpf(finite[key])-reference[key])<mp.mpf('1e-55')
output={'method':'nested-radical recursion without row inputs','certified':False,
        'depth':12,'precision_digits':90,
        'constants':{key:mp.nstr(v,65) for key,v in reference.items()},
        'absolute_stability_differences':diffs,'finite_series_overlap_passed':True}
(ROOT/'results/independent-constants.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
