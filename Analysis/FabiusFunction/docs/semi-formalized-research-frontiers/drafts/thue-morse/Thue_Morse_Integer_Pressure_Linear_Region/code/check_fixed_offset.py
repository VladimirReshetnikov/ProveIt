"""Exact checks of the deleted-full-insertion/true-response identity."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# data/rerun/ in the package, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parents[1] / 'data' / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from pathlib import Path
import sys,json
import sympy as s
from matrix_math import matrix_jets
ROOT=Path(__file__).resolve().parents[1]/'data'
rows=[]
for m in range(2,9):
 d=2*m;ix=list(range(1-m,m));n=len(ix);N=4*m-2
 L=s.Matrix(n,n,lambda k,r:s.Rational(s.binomial(d,m+2*ix[k]-ix[r]),2**(d-1))if abs(2*ix[k]-ix[r])<=m else 0)
 A=s.eye(n)-L;C=A.copy();C[0,:]=s.ones(1,n);inv=C.inv();rhs=s.zeros(n,1);rhs[0]=1;h0=inv*rhs
 J=[L]
 for j in range(1,d+1):
  J.append(s.Matrix(n,n,lambda k,r:L[k,r]*sum((-1)**q*s.binomial(m+2*ix[k]-ix[r],q)*s.binomial(m-2*ix[k]+ix[r],j-q)for q in range(j+1))if L[k,r] else 0))
 def solve(b):
  target=b-sum(b)*h0;rhs=target.copy();rhs[0]=0;v=inv*rhs
  assert A*v==target and sum(v)==0
  return v
 f=[h0]
 for k in range(1,N+1):f.append(solve(sum((J[j]*f[k-j]for j in range(1,min(k,d-1)+1)),s.zeros(n,1))))
 single=[]
 for k in range(d-1):single.append(solve(J[d]*f[k]+sum((J[j]*single[k-j]for j in range(1,min(k,d-1)+1)),s.zeros(n,1))))
 ev=lambda v:sum((-1)**abs(k)*v[j]for j,k in enumerate(ix))
 data=json.loads((ROOT/f'schur_m{m:03}.json').read_text());F=list(map(s.Rational,data['F']));G=list(map(s.Rational,data['G']))
 _,actual,_=matrix_jets(m,N,True)
 for off in range(m):
  q=d+2*off;Z=(-1)**(m+off)*ev(f[q]);P=(-1)**(m+off)*ev(single[2*off]);feedback=sum(F[j]*G[off-j]for j in range(off+1));H=(-1)**(m+off)*ev(actual[q])
  assert F[m+off]==Z+P
  assert H==Z+P-feedback
  rows.append({'m':m,'offset':off,'capped_orbit_coefficient':str(Z),'restored_full_insertion':str(P),'feedback':str(feedback),'true_response':str(H),'exact_checks_passed':True})
 print('m',m,'all',m,'offset identities pass',flush=True)
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('fixed_offset_identity_checks.json', json.dumps({'all_checks_passed':True,'cases':len(rows),'rows':rows},indent=2)+'\n')
