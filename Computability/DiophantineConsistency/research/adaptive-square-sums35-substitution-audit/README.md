# Direct substitutions in the 35-variable degree-six candidate

`audit.py` pins the 35-variable candidate and scans its 14 residuals of the
form `positiveVariable - expression`. For each separate substitution, it
finds a remaining residual with a degree-four monomial whose coefficient is a
nonzero integer times a power of the first port β. Since the fixed β is
positive, that coefficient remains nonzero. Squaring that residual raises the
sum-of-squares degree to at least eight.

Run from any directory with `python3 audit.py`. The check concerns only these
single direct substitutions into the existing residual system. It does not
rule out joint substitutions, changing the residual system, other encodings,
or a smaller degree-six equation. The 35-variable equation remains an
unproved candidate.
