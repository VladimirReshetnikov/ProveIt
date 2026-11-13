# Independent review of the free first-square obstruction

**PASS within the stated external, arbitrary-port scope.** The independent
fail-closed `check.py` pins both graphs, reconstructs the 75-row candidate
from the 76Y graph by deleting the sole `t*t` row and replacing its sole use
with `tFirst`, verifies liveness and operation counts, and checks 128 forward
substitution controls. A separate finite-field polynomial ray has degree 104
and the expected leading coefficient; the general degree claim relies on the
parent leading form and the fact that replacing the first square cannot
increase the first residual's degree. The parent Lean/provider ancestry is
inherited; this is not a Lean theorem.

The checker computes the finite Pell core by direct recurrence, confirms the
main norm, positive exact free-carrier quotient, positive `eta`, `zeta` and
old `gamma`, and the nonsquare certificate `tFirst≡2 (mod 5)`. It computes
the enormous strong and auxiliary coordinates only modulo two separate
moduli, checking every candidate graph row there. Modular evaluations are
controls, not an integer zero proof.

The symbolic completion is valid: the `c`th strong Pell power has second
coordinate divisible by `c²`, so `i=D L/c²` is a positive integer and the
strong norm holds. For odd `m=199`, the auxiliary power has `I|x`. The odd
Chebyshev identity at `I²≡1−650² (mod f²)` gives
`V≡−U_(m−1)(650)=−c (mod f²)`, so `Q=(c+V)/f²` is a positive integer.
The constant term of `T_m(I)/I` is `−m`; with `c²|I` and `f²≡1 (mod c)`,
this gives `Q≡−m (mod c)`, so `T=(m+Q)/c` is a positive integer. The
auxiliary Pell norm then makes `Na=1`. The first residual is 1 by the
definition of `tFirst`, the main and strong residuals vanish by their
norms, and the transport residual vanishes at the stated ports; the complete
sum of squares is zero.

This full positive zero is at **noncompact** ports `(2,2,159,0)`. Its
nonsquare `tFirst` prevents the direct same-witness inverse requiring
`tFirst=t²`; it does not exclude a different 76Y zero at those ports, prove
inequivalence of existence, settle the fixed compact tuple, or supply an
iPRA endpoint. The author's checker uses Python `assert` and does not itself
reject `-O`; the independent checker uses explicit checks and refuses optimized
Python. No Lean replay was performed.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-free-first-square75-obstruction-independent/check.py
```
