"""Exact scalar constants in the analytic spiral-descent proof."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_intervals import PI,S,iv,sinp,cosp

def need(b,m):
 if not b:raise ArithmeticError(m)
checks={
 'log_bound':1+F(9,40)+F(9,40)**2/2>F(56,45),
 'pi_lower':PI.lo>iv(3).hi,
 'spiral_c_upper':F(9,40)/F(3,5)==F(3,8)<F(2,5),
 'phase_quadratic_margin':F(21,25)*3*F(9,20)*F(4,5)/F(8,5)**4==F(567,4096)>F(1,10),
 'real_part_upper':F(23,50)*F(128,119)<F(1,2),
 'real_endpoint_lower':cosp(F(1,5)).lo>iv(F(45,56)).hi,
 'imag_endpoint_upper':sinp(F(1,5)).hi<iv(F(33,56)).lo,
 'cosine_lower':cosp(F(1,5)).lo>iv(F(4,5)).hi,
 'rectangle_radius_below_point_six':F(1,4)+F(1089,10000)<F(3,5)**2,
 'rectangle_real_dominates_imag':F(9,20)**2>F(1089,10000),
 'edge_concavity':F(9,20)-F(1,10)>F(33,100),
 'secondary_inverse_lower_left':F(4,1)*F(1,4)**2-3*F(1,4)+4*F(1089,10000)<0,
 'secondary_inverse_lower_right':F(4,1)*F(1,2)**2-3*F(1,2)+4*F(1089,10000)<0,
 'secondary_log_derivative':-F(3,2)*F(4,3)+F(3,4)<-1,
}
need(all(checks.values()),'spiral or corridor side condition')
out={'all_checks_exact':True,'all_checks_passed':True,'checks':checks,'phase_bound':'Delta(phi)<=-phi^2/20','corridor':['.45<=Re a<=.50','|Im a|<=.33','|a|<=14/25'],'integral_representation':'Proved analytically in spiral_phase_proof.md, not checked numerically here'}
Path(__file__).with_name('spiral_constants_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
