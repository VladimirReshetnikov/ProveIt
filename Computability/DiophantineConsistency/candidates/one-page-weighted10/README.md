# Complete ten-positive equation,degree368,102 operations

`equation.pdf` and standalone `equation.tex` print the entire equation
and every constant on one Letter page in9-point body type. The only
unknowns are the ten strictly positive integers

```
J, F, alpha, i, T, w, Y, n, eta, zeta.
```

The single equation is E^2-64*U*V_N=0. Every polynomial abbreviation is
printed, with no radical or division in its evaluation. Exact total
degree is368. The complete evaluator has102 live binary operations:
60 multiplications,24 additions and18 subtractions. Every input and all
four fixed ports are live. No variable exponent, external table, hidden
constant or program oracle is needed to read the printed specification.

Compared with the preceding102-operation degree388 page, the total
operation count and unknown count stay the same while degree falls by20.
Relative to the earlier105-operation degree408 page, the combined changes
save3 operations and lower degree by40. The preceding pages and canonical
root files remain unchanged. No global simplicity minimum is claimed.

## The complete printed front

`polynomial.json` contains the entire102-gate schedule with the actual
four compressed coefficient payloads. Its parent is the frozen
`ten-positive-weighted-roots` endpoint. The new page writes

    I=i*c^2,    A_tau=9*delta*M^2*Dtau,

and retains all other preceding front definitions, including L=H*I+b'.
Removing the i+q^2 shift saves one addition; multiplying one radicand by9
adds one multiplication. The octic now encodes the weighted signed roots
3*tau,f,y. It is not asserted to be pointwise equal to the preceding
polynomial.

The page's A is one less than the main Pell parameter in the proof,
so H=4A-1 is the proof's4A_full-5. The page writes M for Mtot, Z for
Znum, S for fs, and K for the fixed native coefficient K0. Its q_-
reuses beta*J=q-1. The polynomial K_2=X(X+2a'c)-1 is distinct from K.
The printed Sigma1/Sigma2,P,U,V_N,E match the literal symmetric tail's
U/ab,Po,sc,aXb,Pe respectively.

The renderer checks the entire transcribed front against every literal
gate over four free coefficient ports, using exact shared terms modulo
associativity and commutativity of addition and multiplication. It does
not infer identity from samples or a claimed expanded-polynomial hash.
The full printed schedule and aliases are in `SOURCE_PINS.json` and
`PAGE_VERIFY` receipts. The frozen parent separately checks every cut,
all35 octic coefficients, topology/liveness, the exact centered leading
form, and whole actual-port degree368 slices.

## All printed constants and the native transfer

The entire TeX body from "The four fixed integers" to the end is copied
verbatim from `one-page-shifted10`, and ultimately from the accepted
scaled10 page. It includes all436 seed characters, the ordered62-symbol
alphabet, the full quotient/remainder decoder, all943 typed tiles, their
arithmetic ranks, both masks and the full native numeral. Every index
is fixed or bound. The initializer uses the decoded first transition's
renamed target. The reciprocal intermediate cancels exactly in K.

The seed and four coefficient payloads are byte-identical to the whole
coherent BFS-renamed compact44 tuple. Normal and optimized
`verify_one_page_tuple44.py` runs independently reconstruct every actual
integer from the printed recipe. They check all430 action conjugacies,
all943 tile conjugacies, the full horizontal/vertical color bijections,
all66062 native basis/convolution identities, padding, carry threshold,
controller units and the corrected initializer. MF_source is shifted by
beta exactly once. Raw and compressed payload hashes are retained.

The BFS tuple and original compact44 tuple have different K0. Their
polynomial values are not identified. The earlier pages' complete
state/color/native/controller argument transfers the coefficient-uniform
positive source theorem to this whole BFS tuple. Its README, literal
polynomial and printed constant body are pinned by `SOURCE_PINS.json`.
No single port is replaced independently of that complete tuple.

## Why the new weights preserve ordinary correctness

The arithmetic proof is uniform for beta odd,beta>=31,K0>0 and
0<MC<beta<MF<2beta. These conditions are checked on the entire actual
page tuple. For the weighted roots3*tau,f,y, multiply by sqrt(delta).
Their integer squared arguments are(-9,-1,-1) modulo mu=q^2+1.
A zero signed pair involving3*tau forces mu|8. Equality f=y instead
forces the impossible integer identity V^2-Df=-1/Delta. A zero signed
triple forces mu|2025=3^4*5^2; gcd(q^2+1,3)=1 would then give
mu|25, contradicting mu>=1025. This excludes every zero signed subsum
before parity, rational-root extraction or source soundness.

The character argument and integer-square/adjacent descents recover all
three integral roots. Main folding then gives c>8X*mu^2*Y^2. Together
with I>=c^2, this restores the weighted inequality3*tau+f<H*I and
licenses the unchanged shorter transport L=H*I+b'. The free-J proof
recovers q even before using carrier coprimality. Rank/first-index,
whole-product projection and the fresh unscaled source61 construction
then apply in the same order, including the positive J=1 soundness case.
There is no soundness assumption i>=mu or mu|I.

For completeness, canonical old witnesses have positive center tau+f+y.
The maps i_new=i_old+q^2 and n_new=n_old+2*tau preserve I and all other
strong/transport data and produce center3*tau+f+y. Both new coordinates
are positive. No positive inverse i_old=i_new-q^2 is assumed for an
arbitrary new zero. This proves the required existence equivalence.
The full ordinary proof, focused independent peer and inherited source
interfaces are pinned in `SOURCE_PINS.json`.

The unique leading form is omega0^4. Its selected degree368 coefficient
is2^28*beta^184>0 at monomial
J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4. The new scalar9 cannot change
this leading term. The other three ports do not occur in its coefficient,
so exact degree368 holds at the whole BFS page tuple as well.

The ordinary calibrated no-positive-zero/Con(ZFC) equivalence is
retained. This is not a new encoded object-ZFC derivation or a Lean
completion; neither consistency nor actual absence of zeros is asserted.
The printed footer explicitly records the remaining formalization
boundary. Lean remains paused.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/render_weighted10_page.py --render
python -B Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py --output Computability/DiophantineConsistency/candidates/one-page-weighted10
```

Both commands also pass under `-O`. Full replay and visual receipts and
the packet seal are retained separately. No canonical file was edited.
