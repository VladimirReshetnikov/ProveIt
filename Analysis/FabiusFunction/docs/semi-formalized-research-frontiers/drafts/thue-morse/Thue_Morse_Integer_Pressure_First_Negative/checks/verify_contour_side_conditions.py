"""Exact non-grid constants and saddle coverage for the first-negative contour proof."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_eventual_66 import values,I,iv,S,PI,sinp,cosp
sys.path.insert(0,str(Path(__file__).resolve().parent))
from complex_interval_core import C,spatial_product

def need(x,msg):
 if not x:raise ArithmeticError(msg)

tlo=F(3413848,10**7);thi=F(3484140,10**7)
ml,gl=values(tlo);mu,gu=values(thi)
need(F(ml.hi,S)<F(33,20),'lower second saddle')
need(F(mu.lo,S)>F(833,500),'upper second saddle')
# Positive model lower rate, uniformly over sigma in[3.3,3.332].
need((F(gl.lo,S)**2)**10>F(3)**10*thi**33,'second-model rate exceeds3')
ml1,gl1=values(F(7752157,10**7));mu1,gu1=values(F(781,1000))
need(F(ml1.hi,S)<F(33,10),'lower first saddle')
need(F(mu1.lo,S)>F(833,250),'upper first saddle')
need(F(gl1.lo,S)**250>3**250*F(781,1000)**833,'first-model rate exceeds3')
a=F(303,1000);L2=spatial_product(C(iv(a),iv(0)),F(1,2),24)
need(F(L2.lo,S)>F(21,20)**2,'L(.303)>1.05')
r=F(38,100);re=F(303,1000);w=F(49,100);kappa=F(73,100)
checks={
 'secondary_endpoints':max(r*r,(1-2*re+r*r)/2)*F(7,5)**2<kappa*kappa,
 'substitution_gap':kappa*w<F(348,1000)*F(21,20),
 'rankone_gap':r*F(11907,20000)<F(348,1000)*F(21,20),
 'negative_branch_end':F(sinp(F(1,8)).hi,S)<2*re*F(cosp(F(1,8)).lo,S),
 'first_local_denominator':re*F(cosp(F(1,128)).lo,S)-F(sinp(F(1,128)).hi,S)>F(27,100),
 'remaining_local_denominator':F(cosp(F(65,256)).lo,S)>F(2,3),
 'origin_local_denominator':F(cosp(F(1,128)).lo,S)>F(99,100),
 'logQ_second_derivative':F(22,7)**2*(1+r*r)*(F(1,4)/F(27,100)**2+F(3,16)+F(1,3)/F(99,100)**2)<46,
 'tail_decay':F(9,10)-F(46,128)>F(1,2),
 'real_J_lower':3*re>F(9,10),
 'third_cluster_range':F(833,250)<F(7,2),
}
need(all(checks.values()),'local complex side condition')
Path(__file__).with_name('contour_side_conditions.json').write_text(json.dumps(dict(all_checks_passed=True,checks=checks,second_saddle_t_interval=[str(tlo),str(thi)],slope_interval=['33/10','833/250'],both_model_exponential_rates_exceed=3),indent=2)+'\n')
print('All local analytic constants, saddle coverage, and both model rates>3 pass exactly.')
