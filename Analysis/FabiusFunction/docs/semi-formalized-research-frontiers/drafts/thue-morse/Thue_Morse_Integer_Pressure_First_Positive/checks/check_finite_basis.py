"""Independent finite Bernoulli formula checked against Fourier response data."""
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
root=Path(__file__).resolve().parent.parent
c=lambda j:(-1)**(j+1)*2**(2*j)*s.bernoulli(2*j)/s.factorial(2*j)
R=lambda j:(2**(2*j)-1)*c(j)
f=lambda l,u:(4-l*(3-u))/(2*(1-l)*(1-u))
rows=[]
for old in json.loads((root/'data'/'second_response_checks.json').read_text())['rows']:
 m=old['m'];bb=[]
 for j in range(1,m):
  q=4*m*m*sum(c(k)*c(j+1-k)*f(s.Rational(1,4**j),s.Rational(1,2**(2*k-1))) for k in range(1,j+1))
  if j<=m-2:q-=2*m*(2*j+1)*c(j+1)*f(s.Rational(1,4**j),s.Rational(1,2**(2*j+1)))
  assert q>0
  lower=2*m*f(s.Rational(1,4**j),s.Rational(1,2**(2*j+1)))*(2*m*(2*j+3)-(2*j+1))*c(j+1)
  assert q>=lower>0
  assert sum(c(k)*c(j+1-k)for k in range(1,j+1))==(2*j+3)*c(j+1)
  bb.append(q)
 B=sum(bb[j-1]*R(m-j)for j in range(1,m))
 assert B==s.Rational(old['B'])
 rows.append({'m':m,'positive_basis_coefficients':[str(x)for x in bb],'B':str(B),'matches_fourier':True})
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('finite_basis_checks.json', json.dumps({'rows':rows,'all_checks_passed':True},indent=2)+'\n')
print('Finite Bernoulli formula, coefficient positivity and bounds agree with independent Fourier values for m=2,...,10.')
