"""Exact side constants for the diagonal and tangent lower bounds."""
from fractions import Fraction as F
from pathlib import Path
import json
alpha=F(707,275)
assert alpha>2 and 2**128>4*20*128
rate=F(7,4)/alpha
assert 26000*128**3*rate**128<F(3,20)
assert rate*F(129,128)**3<1
assert 128**2-F(25,2)*128-F(385,8)>0
assert F(5,3**4)<F(4,3*7)
assert 2*F(22,7)*3*F(13,12)<25
out=dict(all_checks_passed=True,diagonal_cutoff_d=128,diagonal_ratio=str(rate),
         cosine_absorption=True,coefficient_log_concavity_base_case=True,
         entropy_constant_less_than_5=True)
Path(__file__).with_name('coefficient_lower_bounds_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('Diagonal, log-concavity, entropy and cosine constants pass.')
