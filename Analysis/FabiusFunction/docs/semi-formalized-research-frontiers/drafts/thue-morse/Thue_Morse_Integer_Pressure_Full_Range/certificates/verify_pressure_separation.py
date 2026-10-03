"""Exact scalar side checks for the Green-bound pressure reduction."""
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

from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json
from exact_intervals import plo,phi
assert F(157,50)<plo<phi<F(22,7)

def sqrt_bounds(x,scale=10**22):
 k=isqrt(x.numerator*scale**2//x.denominator);return F(k,scale),F(k+1,scale)
lo=hi=F(1);bs=[]
for j in range(24):
 bs.append((lo,hi));_,a=sqrt_bounds(1+lo*lo);b,_=sqrt_bounds(1+hi*hi);lo,hi=lo/(1+a),hi/(1+b)
 scale=10**22;lo=F((lo.numerator*scale)//lo.denominator,scale);hi=F(-((-hi.numerator*scale)//hi.denominator),scale)
tail=F(2)**(1-len(bs))
a0=F(822,1000);a1=F(823,1000)
mean_up=sum(a0*u/(1+a0*u)for l,u in bs)+a0*tail
mean_low=sum(a1*l/(1+a1*l)for l,u in bs)
assert mean_up<1<mean_low
Clow=1/a1
for l,u in bs:Clow*=1+a0*l
assert Clow>F(101,25)
R=F(2,5);Bup=F(1)
for l,u in bs:Bup*=1+R*u
Bup/=1-R*tail
# pi>157/50 follows from the Machin certificate in exact_intervals.py.
Lup=F(100,157)*Bup
assert Lup<F(49,40)
atlo=sum((-1)**k*R**(2*k+1)/F(2*k+1)for k in range(20))
assert atlo>F(19,50)
# tan(t)>=t+t^3/3+2t^5/15 on (0,pi/2). Prove the resulting lower bound tan^2(t)>2t^3.
# Ascending coefficients of (15+5x²+2x⁴)²−450x.
pol=list(map(F,[225,-450,150,0,85,0,20,0,4]))
def trim(a):
 while a and not a[-1]:a.pop()
 return a
def remainder(a,b):
 a=a[:]
 while len(a)>=len(b):
  k=len(a)-len(b);c=a[-1]/b[-1]
  for j in range(len(b)):a[k+j]-=c*b[j]
  trim(a)
 return a
seq=[pol,[j*pol[j]for j in range(1,len(pol))]]
while seq[-1]:
 r=remainder(seq[-2],seq[-1])
 if not r:break
 seq.append([-z for z in r])
def variations(a):
 a=[(v>0)-(v<0)for v in a if v];return sum(a[i]!=a[i-1]for i in range(1,len(a)))
v0=variations([z[0]for z in seq]);vinf=variations([z[-1]for z in seq]);assert v0==vinf
assert pol[0]>0
alpha=F(707,275);rho2=F(7,25)/(F(19,50)**2*alpha);rho3=F(7,25)/(F(19,50)**3*2*alpha)
assert rho2<1 and rho3<1
out=dict(all_checks_passed=True,saddle_interval=[str(a0),str(a1)],C_lower=str(Clow),C_lower_exceeds='101/25',L_upper=str(Lup),L_upper_below='49/40',atan_lower=str(atlo),atan_lower_exceeds='19/50',tan_square_polynomial_ascending_coefficients=list(map(str,pol)),sturm_sequence_ascending_coefficients=[list(map(str,z))for z in seq],positive_root_count=v0-vinf,endpoint_ratio_2=str(rho2),endpoint_ratio_3=str(rho3),green_bound_proved_in_article=True)
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('pressure_separation_certificate.json', json.dumps(out,indent=2)+'\n');print('All exact pressure-separation side checks pass. The Green bound is proved in the article.');print('endpoint ratios',float(rho2),float(rho3))
