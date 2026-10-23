# Forty-two unrestricted integers, degree four

Use `quartic42.json` for the exact27-residual system and `quartic42_expanded.json`
for its391-term sum-of-squares quartic. All42 unknowns range over integers.
The four fixed coefficients are the whole retained package34 tuple.

The new idea is to use w=4u², a canonical cofinal restriction, to force
|E|>3R+1 before Pell recovery. This lets one product positivity guard
replace two separate eta/zeta guards. The negative common-sign branch
would force n>R, while the sign-insensitive auxiliary rank proof gives p=R
and p>n. Three variables and one residual disappear.

See PROOF.md and section.tex for the ordered proof and inherited boundaries.
Run `python build_verify.py`; Python's standard library is sufficient.
The checks do not execute a consistency search or certify the compiler by sampling.

Two exact monic projections are also included:
- sextic36.json:36 unrestricted integers,21 residuals of degree<=3;
  single sum-of-squares polynomial degree6,435 symbolic terms.
- octic32.json:32 unrestricted integers,17 residuals of degree<=4;
  single polynomial degree8,395 symbolic terms.
Run `python build_projections.py` with SymPy1.14.0. See PROJECTIONS.md.
These are different degree/variable tradeoffs, not fewer-variable quartics.
