"""Uniform Green side constants through the exact product-envelope threshold."""
from fractions import Fraction as F
from pathlib import Path
import contextlib,io,json
with contextlib.redirect_stdout(io.StringIO()):import half_scalar as v
v.K=64
v.r=F(3,5)
height=v.H(F(1,2));slope=v.hp(F(1,2))
v.strict_less(height,F(8,5),'upper envelope cap')
v.strict_more(slope,0,'upper envelope increases')
r_upper=F(573537286335,10**12)
v.r=r_upper
b=v.H(F(3,5))/v.H(F(2,5))
v.strict_less(b,F(1999,2000),'strict far-branch cap at critical radius')
d=16384;gam=F(99,100);theta=F(199,200);rho=F(1999,2000)
alpha=F(3,4)+(5*d+53)*gam**d+F(99,2)*rho**d
beta=F(1,2)+rho**d/2
rows=[alpha+7*theta**d,beta+F(d,2)*(gam/theta)**d]
checks={
 'near_branch_base':(F(3,5)+F(16,5)/200)*F(8,5)<gam,
 'near_derivative_coefficient':F(4,5)*F(16,5)*F(8,5)/(2*gam)<3,
 'weight_derivative_coefficient':F(4,5)*F(16,5)*F(8,5)<5,
 'projection_coefficient':F(16,5)/2<2,
 'amplitude_product':F(3,5)*F(8,5)<gam,
 'row0':rows[0]<F(4,5),'row1':rows[1]<F(4,5),
 'row0_decreases':gam*F(5*d+58,5*d+53)<1,
 'row1_decreases':gam/theta*F(d+1,d)<1,
 'raw_mean_cap':F(3,5)/(1+F(3,5))+F(3,5)<1,
}
v.need(all(checks.values()),'full-envelope Green side comparisons')
out={'cutoff_even_d':d,'critical_radius_upper':str(r_upper),'upper_envelope_height':v.out(height),'upper_envelope_endpoint_derivative':v.out(slope),'far_branch_cap':v.out(b),'row0_upper_decimal_orientation':float(rows[0]),'row1_upper_decimal_orientation':float(rows[1]),'directed_row_upper_bounds':[str(F((x.numerator*10**12+x.denominator-1)//x.denominator,10**12))for x in rows],'checks':checks,'all_exact_checks_passed':True}
Path(__file__).with_name('full_envelope_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:z for k,z in out.items() if k!='exact_rows'},indent=2))
