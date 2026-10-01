"""Exact rational checks used by the C1 frozen Green bound; no floating decisions."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from pathlib import Path
import json
from exact_intervals import F,I,S,iv,PI,sinp,cosp
r=F(2,5);K=16

def H(x):
 p=iv(1)
 for j in range(1,K+1):p=p*(cosp(x/F(2**j))+r*sinp(x/F(2**j)))
 eta=r*PI*iv(x/F(2**K));up=p/(1-eta)
 # For omitted angles theta<=r, cos(theta)+r*sin(theta)>=1.
 assert (PI*iv(x/F(2**(K+1)))).hi < iv(r/2).lo
 return I(p.lo,up.hi)
def hp(x):
 v=iv(0)
 for j in range(1,K+1):
  ang=x/F(2**j);ss=sinp(ang);cc=cosp(ang)
  v=v+(PI/F(2**j))*((-ss+r*cc)/(cc+r*ss))
 # Omitted logarithmic derivatives are positive and at most r*pi/2^j.
 return I(v.lo,(v+r*PI/F(2**K)).hi)
quarter=hp(F(1,4));three_eighths=hp(F(3,8));half=hp(F(1,2));Hq=H(F(1,4));L=H(F(1,2))
assert 0<quarter.lo and quarter.hi<iv(F(2,5)).lo
assert three_eighths.hi<0
assert half.lo>iv(F(-1,2)).hi
assert Hq.hi<iv(F(5,4)).lo
assert iv(1).hi<L.lo and L.hi<iv(F(49,40)).lo
x=F(2,5);ss=sinp(x/2);cc=cosp(x/2)
bminus=(ss+r*cc)*H((1-x)/2)/H(x)
pm=(cc-r*ss)/(cc+r*ss)
assert bminus.hi<iv(F(91,100)).lo
assert pm.hi<iv(F(14,25)).lo
d0=128;gamma=F(4,5);tau=F(91,100);eta_base=F(9,10)
alpha=F(3,4)+(5*d0+8)*gamma**d0+F(9,2)*tau**d0
beta=F(1,2)+F(1,2)*tau**d0
row0=alpha+5*eta_base**d0
row1=beta+F(d0,2)*F(8,9)**d0
assert row0<F(4,5) and row1<F(4,5)
assert gamma*F(5*(d0+1)+8,5*d0+8)<1
assert F(8,9)*F(d0+1,d0)<1
out={'r':'2/5','hprime_quarter':list(map(str,[F(quarter.lo,S),F(quarter.hi,S)])),'hprime_three_eighths_upper':str(F(three_eighths.hi,S)),'hprime_half_lower':str(F(half.lo,S)),'H_quarter_upper':str(F(Hq.hi,S)),'L_interval':list(map(str,[F(L.lo,S),F(L.hi,S)])),'bminus_two_fifths_upper':str(F(bminus.hi,S)),'pminus_two_fifths_upper':str(F(pm.hi,S)),'cutoff_d':d0,'row0_less_than_four_fifths':row0<F(4,5),'row1_less_than_four_fifths':row1<F(4,5),'tail_geometric_cutoff':K,'all_comparisons_exact':True}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('green_constants_certificate.json', json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
