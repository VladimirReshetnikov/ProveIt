from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def lower_exp(x,n):
    return sum(x**j/F(factorial(j)) for j in range(n+1))


def upper_exp(x,n):
    if x>=n+2:raise ValueError('Invalid geometric tail')
    return lower_exp(x,n)+x**(n+1)/F(factorial(n+1))/(1-x/F(n+2))


def require(condition,label):
    if not condition:raise RuntimeError(label)

records={}
s=F(51,20)
low=lower_exp(2*s,10);up=upper_exp(s,4)
require(low>160,'exp(51/10)>160')
require(up<13,'exp(51/20)<13')
records['exp_51_over_10_lower']=str(low)
records['exp_51_over_20_upper']=str(up)
pi_lower=F(157,50);pi_upper=F(22,7)
sin_lower=sum((-1)**j*pi_lower**(2*j+1)/F(factorial(2*j+1)) for j in range(8))
require(sin_lower>0,'sin(157/50) positive alternating lower bound')
records['sin_lower_at_157_over_50']=str(sin_lower)
B_upper=F(1,80)+s*F(161,160)/(s*s+(pi_lower/2)**2)
require(B_upper<F(3,10),'height bound')
J_comparison=pi_upper+F(3111,100)/pi_upper
require(J_comparison>13,'height real-value sign')
records['height_upper']=str(B_upper)
records['height_margin']=str(F(3,10)-B_upper)
records['J_margin']=str(J_comparison-13)
require(lower_exp(F(3),8)>20,'exp(3)>20')
require(upper_exp(F(3),8)<21,'exp(3)<21')
records['exp_3_lower']=str(lower_exp(F(3),8))
records['exp_3_upper']=str(upper_exp(F(3),8))
c=F(23,25)
P=5*c**4+202*c**3+1925*c*c+1152*c-2880
require(P<0,'transformed likelihood polynomial')
require(pi_lower*pi_lower*c>9,'radius bound above 3')
records['angular_polynomial_at_23_over_25']=str(P)
records['radius_margin']=str(pi_lower*pi_lower*c-9)
H_margin=F(36225,167042)-F(112,625)
require(H_margin>0,'tilted derivative margin')
require(sum(F(1,j*j) for j in range(2,8))>F(1,2),'tail reciprocal squares')
records['tilted_derivative_margin']=str(H_margin)
T=F(14,5)
S_lower=sum((-1)**j*T**(2*j+1)/F(factorial(2*j+1)) for j in range(8))
C_upper=sum((-1)**j*T**(2*j)/F(factorial(2*j)) for j in range(7))
C_lower=sum((-1)**j*T**(2*j)/F(factorial(2*j)) for j in range(8))
K_lower=S_lower/T-2*C_upper-2
F_lower=(2*T*T-1)*S_lower+T*C_lower
require(K_lower>0 and F_lower>0,'nontrivial phase curvature base')
records['K_lower_at_14_over_5']=str(K_lower)
records['F_lower_at_14_over_5']=str(F_lower)
area=F(1,2)*(F(1,2)-F(420,931))*(F(1,2)-F(20,131))
require(area==F(169,19912),'positive triangle area')
wide_area=F(1,4)/F(23,10)
require(wide_area==F(5,46),'wide cone area')
combined=F(3,8)+wide_area+area
require(combined==F(28176,57247),'combined constant')
require(combined>F(49,100),'0.49 lower constant')
records['positive_triangle_area']=str(area)
records['wide_cone_area']=str(wide_area)
records['combined_constant']=str(combined)
records['margin_over_049']=str(combined-F(49,100))
Path(__file__).with_name('exact_constants.json').write_text(json.dumps({'status':'PASS','scope':'Exact elementary constants and areas; the analytic saddle and density proofs are in the manuscript','records':records},indent=2)+'\n')
print('All rational Taylor, angular-selection, and area certificates pass')
