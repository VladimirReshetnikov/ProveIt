"""Compare exact finite-matrix second coefficients to finite inverse-tree sums."""
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
import json
import sympy as s
import mpmath as mp
mp.mp.dps=70
rows=[]
for m in range(2,7):
 I=list(range(1-m,m));d=len(I)
 def a(j):return s.Rational(s.binomial(2*m,m+j),4**m) if -m<=j<=m else s.S.Zero
 V=s.Matrix(d,d,lambda k,r:2*a(2*I[k]-I[r]))
 B1=s.Matrix(d,d,lambda k,r:-2*(2*I[k]-I[r])*V[k,r])
 B2=s.Matrix(d,d,lambda k,r:(m-2*(2*I[k]-I[r])**2)*V[k,r])
 f=s.zeros(d,1);f[m-1]=1;u=s.zeros(d,1);v=s.zeros(d,1)
 ev=s.Matrix(1,d,[(-1)**abs(r) for r in I])
 for N in range(1,13):
  f,u,v=V*f,V*u+B1*f,V*v-B1*u+B2*f
  assert sum(u)==0 and sum(v)==0
  if N not in [1,2,4,7,12]:continue
  exact=(ev*v)[0]
  if N<=7:
   total=mp.mpf(0)
   for q in range(-2**(N-1),2**(N-1)):
    w=mp.mpf(q)+mp.mpf('.5')
    tans=[mp.tan(mp.pi*w/2**j)for j in range(1,N+1)]
    S=sum(tans);T=sum(t*t for t in tans)
    total+=(2**N*mp.sin(mp.pi*w/2**N))**(-2*m)*(2*m*m*S*S-m*T)
   err=abs(total-mp.mpf(str(exact.p))/int(exact.q))
   assert err<mp.mpf('1e-60')
  else:err=None
  rows.append(dict(m=m,N=N,exact=str(exact),decimal=str(s.N(exact,16)),finite_orbit_error=None if err is None else str(err)))
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('finite_orbit_checks.json', json.dumps({'rows':rows,'all_finite_orbit_checks_below_1e_minus_60':True},indent=2)+'\n')
print('Verified 20 finite inverse-tree identities at 70-digit precision against exact rational matrices; recorded five N=12 convergence checks.')
