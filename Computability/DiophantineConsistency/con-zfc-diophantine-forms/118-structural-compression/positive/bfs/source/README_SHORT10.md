# Complete ten-positive equation,degree368,101 operations

`equation.pdf` and standalone `equation.tex` give the entire equation and
all fixed constants on one Letter page in9-point body type. The only
unknowns are the ten strictly positive integers

```
J, F, alpha, i, T, w, Y, n, eta, zeta.
```

The single equation is E^2-64*U*V_N=0, with every polynomial abbreviation
printed. Exact total degree is368. The evaluator has101 live binary
operations:60 multiplications,24 additions and17 subtractions. Every
input and all four coefficient ports are live. The printed specification
has no external table, program oracle, hidden coefficient, variable
exponent or radical in the polynomial evaluation.

The page replaces the preceding102-operation projection numerator by

    K_2=X*(3c-2X)+2

and deletes the unused a' alias. It retains I=i*c^2, L=H*I+b' and the
single weighted radicand9*delta*M^2*Dtau. This saves one operation at
the same exact degree and unknown count. Relative to the earlier
105-operation degree408 page, the combined reductions save4 operations
and lower degree by40. All preceding pages and canonical root files
remain untouched. No global simplicity minimum is claimed.

## Entire formula and universal evaluator binding

`polynomial.json` contains the complete101-gate schedule and actual
four compressed coefficient payloads. Its parent is the frozen
`ten-positive-short-projection` endpoint. The scalar K_2 is the new
positive-on-solutions projection numerator Kpos, and is distinct from
the fixed native coefficient K. The page's A is one less than the full
main Pell parameter in the proof, so H=4A-1 is that proof's4A_full-5.
The page writes M for Mtot, Z for Znum and S for fs; q_- reuses the
already computed beta*J=q-1. Sigma1/Sigma2,P,U,V_N,E correspond to the
literal symmetric tail's U/ab,Po,sc,aXb,Pe.

The renderer universally matches the full printed arithmetic front to
every literal gate over four free coefficient ports, using exact shared
terms modulo associativity and commutativity of addition and
multiplication. Equality is not inferred from samples or an expanded
polynomial hash. The full transcribed schedule and aliases are retained
in `SOURCE_PINS.json` and `PAGE_VERIFY` receipts.

The parent independently checks all101 rows and their complete102-row
parent map, all35 weighted norm coefficients, all projection/center
identities and the entire leading-degree argument. The difference
between old and new complete polynomials has degree at most360<368.
Thus the whole degree368 leading component stays unchanged, including
selected coefficient

    [J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^184>0.

The other three fixed ports do not occur in that coefficient, so this
exact degree holds for the whole BFS page tuple too.

## Complete constants and native transfer

The complete TeX body from "The four fixed integers" to the end is
verbatim from `one-page-weighted10`, and ultimately from the accepted
scaled10 page. It prints all436 seed characters, the ordered62-symbol
alphabet, every quotient/remainder decoder equation, all943 typed tiles,
their arithmetic floor ranks, both masks and the full native numeral.
Every index is fixed or bound. The initializer uses the decoded first
transition's renamed target. The reciprocal intermediate cancels exactly
in K, and all four results are positive integers.

The seed and four payloads are byte-identical to the entire coherent
BFS-renamed compact44 tuple. Normal and optimized
`verify_one_page_tuple44.py` runs independently reconstruct all four
integers from the printed recipe. They verify every430 transition and
943 tile under complete state/color bijections, all66062 native
basis/convolution identities, the corrected initializer, padding, carry
threshold and controller units. MF_source includes beta exactly once.
Full raw and compressed payload hashes are retained in the receipts.

The BFS tuple has a different K0 from original compact44. Their
polynomial values are not being identified. The previous pages' full
typed-color, initializer, native and controller argument supplies the
coefficient-uniform positive source theorem for this entire BFS tuple.
Its README, whole polynomial and complete constant body are pinned in
`SOURCE_PINS.json`; no single port is replaced independently.

## Ordinary correctness of the new projection

The arithmetic proof is uniform for beta odd,beta>=31,K0>0 and
0<MC<beta<MF<2beta; the renderer checks these conditions on the whole
actual tuple. All weighted-root rationality and main/auxiliary folding
steps are unchanged. Before transport, q parity or partial fractions,
they give c>8X*mu^2*Y^2>2X. Only then is Kpos>0 used to drop its
negative term in the bad-transport contradiction. Kpos is not asserted
to be positive at every arbitrary positive input.

With A_full the main Pell parameter and Kquad the old projection,

    Kpos=H*X*c-2*Kquad, H=4A_full-5 odd.

Thus H|P*Kpos is equivalent to H|P*Kquad. Only2 is inverted modulo H;
the possibly noncoprime factor P is not cancelled. The retained strict
whole-product bound recovers X=2^R, and the remaining CRT, ratio and
fresh unscaled positive source61 reconstruction proceed in the same
order, including the positiveJ=1 case.

For completeness any old zero supplies the integer kappa=Kquad/H.
The map n_new=n_old+3*kappa-X*c is strictly positive because

    3*Kquad-H*X*c=3*(X^2-1)+(2*A_full-7)*X*c>0.

Every other input stays fixed and the full normalized center, integer Z
and weighted norm output remain identical. No positive pointwise inverse
n map is assumed for arbitrary new zeros. These arguments retain the
ordinary positive-solvability/refutation equivalence. The full proof,
focused independent peer and inherited interfaces are content-pinned.

Composing with the ordinary native/source calibration gives the same
ZFC-provable no-positive-zero/Con(ZFC) statement. This is not a new encoded
object-ZFC derivation or Lean completion. Neither consistency nor actual
absence of zeros is asserted; the footer records the remaining Lean
boundary explicitly. Lean remains paused.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/render_short10_page.py --render
python -B Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py --output Computability/DiophantineConsistency/candidates/one-page-short10
```

Both commands also pass under `-O`. Complete render/tuple/replay logs,
visual receipts and the closed packet seal are retained separately.
