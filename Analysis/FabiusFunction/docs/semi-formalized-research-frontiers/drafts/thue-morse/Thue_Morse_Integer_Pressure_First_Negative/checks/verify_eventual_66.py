"""Exact rational side conditions for an eventual degree<6.6m theorem."""
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
from pathlib import Path
import sys,json,math
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_intervals import I,iv,PI,S,sinp,cosp

def require(condition,message):
 if not condition:raise ArithmeticError(message)

def trig_rad(x,sine):
 x=iv(x);xx=x.square();term=x if sine else iv(1);v=term
 for k in range(1,40):
  term=-(term*xx)/((2*k)*(2*k+1)if sine else (2*k-1)*(2*k));v=v+term
 power=iv(1);ab=I(0,max(abs(x.lo),abs(x.hi)));order=81 if sine else 80
 for _ in range(order):power=power*ab
 rad=(power/math.factorial(order)).hi
 return I(v.lo-rad,v.hi+rad)

bs=[sinp(F(1,2**(j+1)))/cosp(F(1,2**(j+1)))for j in range(1,33)]
def values(t):
 a=trig_rad(t,True)/trig_rad(t,False);prod=iv(1);mean=iv(0)
 for b in bs:
  prod=prod*(1+a*b);mean=mean+(a*b)/(1+a*b)
 mean=I(mean.lo,mean.hi+(a*F(1,2**31)).hi)
 mu=iv(t)*(1+a.square())/a*(1+mean)
 g=iv(2)/PI*a*prod
 return mu,g

def lo(x):return F(x.lo,S)
def hi(x):return F(x.hi,S)
R=F(2,5);w=F(49,100);beta=F(11907,20000)
tR=sum((-1)**j*R**(2*j+1)/F(2*j+1)for j in range(20))
rows=[]
for sigma,l,u,power,target in [(F(3),F(7252640,10**7),F(7252641,10**7),1,F(6,5)),(F(33,10),F(7752157,10**7),F(7752158,10**7),10,F(103,100))]:
 ml,gl=values(l);mu,gu=values(u)
 require(hi(ml)<sigma<lo(mu),"saddle bracket")
 exponent=int(sigma*power)
 balance=(lo(gl)/(R*beta))**power*(tR/u)**exponent
 require(balance>target,"endpoint rate margin")
 rows.append(dict(sigma=str(sigma),saddle_lower=str(l),saddle_upper=str(u),mean_lower_endpoint_upper=str(hi(ml)),mean_upper_endpoint_lower=str(lo(mu)),balance_power=power,balance_lower=str(balance),balance_exceeds=str(target)))
d=128
checks={
 'weighted_derivative_error':60000*d*d*F(49,90)**d<1,
 'weighted_derivative_error_decreases':F(49,90)*F(d+1,d)**2<1,
 'weighted_value_error':60000*d*d*w**d<1,
 'weighted_value_error_decreases':w*F(d+1,d)**2<1,
 'Hermite_value_error':610*d*F(1,2)**d<1,
 'Hermite_value_error_decreases':F(1,2)*F(d+1,d)<1,
 'F_disk_bound':31000*d*d*w**d<1,
 'g_squared_below_Rbeta':R*F(243,200)<w,
 'gap_from_endpoint_33':F(3,1030)>F(1,400),
 'gap_from_endpoint_3':F(1,6)>F(1,400),
 'exp_bound_for_third_cluster':1+F(63,250)+F(63,250)**2/(2*(1-F(63,750)))<F(13,10),
 'third_model_at_one_eighth':F(273,2500)<F(1,9),
 'third_rate_below_two':2**21<(2*9**3)**2,
}
require(all(checks.values()),"norm or third-cluster side condition")
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('eventual_66_certificate.json', json.dumps(dict(all_checks_passed=True,rows=rows,checks=checks,uniform_rate_gap='1/400',finite_cutoff_not_claimed=True),indent=2)+'\n')
print('All eventual6.6m side conditions pass; uniform first-model/frozen-error exponent gap >1/400.')
