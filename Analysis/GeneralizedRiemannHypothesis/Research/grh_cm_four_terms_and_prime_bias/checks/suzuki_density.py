"""Verify the numerical tail estimates in suzuki.tex, using rational bounds."""
from fractions import Fraction as F

from suzuki_constants import SCALE, constant_bounds

# Validate all three elementary bounds before using the coarser rational inputs.
bounds = constant_bounds()
assert F(bounds["S"][1], SCALE) < F(462, 10000)
assert F(bounds["c"][0], SCALE) > F(2686, 1000)
assert F(bounds["logH"][1], SCALE) < 29
# S = 2 + EulerGamma - log(4*pi), c = (pi/2 + EulerGamma + log(8*pi))/2.
S_upper = F(462, 10000)
c_lower = F(2686, 1000)
height = 3 * 10**12
log_height_upper = 29
tail = F(8, height) * (log_height_upper**2 + 2 * log_height_upper + 2)
variance_upper = S_upper / (1 - S_upper / 8) + tail
# S_upper is a deliberately coarser input than S itself.
assert variance_upper < F(4647, 100000)
minority_upper = variance_upper / (2 * c_lower**2)
assert minority_upper < F(323, 100000)
print("variance bound from rational inputs:", float(variance_upper))
print("upper density bound for E(x)>0:", float(minority_upper))
print("lower density bound for E(x)<0:", float(1 - minority_upper))
