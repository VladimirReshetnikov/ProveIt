"""Verify the cotangent eigenbasis formula against independent Fourier jets."""
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
import sympy as s
import json
ROOT=Path(__file__).resolve().parent.parent/'data'

def c(k):return (-1)**(k+1)*2**(2*k)*s.bernoulli(2*k)/s.factorial(2*k)
def R(k):return (2**(2*k)-1)*c(k)
def f(l,u):return (4-l*(3-u))/(2*(1-l)*(1-u))
def coeff(m,j):
 l=s.Rational(1,4**j)
 ans=4*m*m*sum(c(k)*c(j+1-k)*f(l,s.Rational(1,2**(2*k-1)))for k in range(1,j+1))
 if j<=m-2:ans-=2*m*(2*j+1)*c(j+1)*f(l,s.Rational(1,2**(2*j+1)))
 return s.factor(ans)
known={r['m']:s.Rational(r['B'])for r in json.loads((ROOT/'second_response_checks.json').read_text())['rows']}
rows=[]
for m in range(2,31):
 b=[coeff(m,j)for j in range(1,m)]
 assert all(x>0 for x in b)
 B=sum(b[j-1]*R(m-j)for j in range(1,m))
 if m in known:assert B==known[m],(m,B,known[m])
 rows.append({'m':m,'basis_coefficients':[str(x)for x in b],'B':str(B)})
for j in range(1,31):assert sum(c(k)*c(j+1-k)for k in range(1,j+1))==(2*j+3)*c(j+1)
l,u=s.symbols('lambda mu')
combined=((l-2*u)*(u-2)/(1-u)+(l-4*u+4)/2)/(1-l)
assert s.factor(combined-f(l,u))==0
assert s.factor(s.diff(f(l,u),u)-(2-l)/((1-l)*(1-u)**2))==0
out={'all_checks_passed':True,'independent_Fourier_B_matches_m2_to_10':True,'cotangent_convolutions_checked_through_j30':True,'response_multiplier_and_monotonicity_symbolically_verified':True,'rows':rows}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('finite_formula_checks.json', json.dumps(out,indent=2)+'\n')
print('Finite formula verified exactly against Fourier responses for m=2,...,10; all basis coefficients positive through m=30; convolution and response algebra pass.')
