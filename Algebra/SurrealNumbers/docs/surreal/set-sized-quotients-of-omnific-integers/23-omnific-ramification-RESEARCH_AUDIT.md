# Research and proof audit

## Baseline and actual scope

Repository: https://github.com/VladimirReshetnikov/Surreal  
Pin: **343dc2c471212bb9b53ff4623bace2e1943f255b**  
Research date: 23 September 2026.

The repository connector was used to read the root and documentation guides,
relevant report guides, and selected contiguous sections of
`docs/surreal/set-sized-quotients-of-omnific-integers/article.tex`.
The relevant comparisons include its fixed-workspace definitions,
normalization-fibre statements, support descent, one-scale rational
criterion, explicit non-claims, and open-question status discussions.
This is not an exhaustive audit of all reports or Git history.

Exact repository labels:

* `osq:nf:q:fibre` (b): radicality and Boolean atomlessness in fixed workspaces.
* `osq:q:normalization`: membership questions for the normalization.
* `osq:bb:thm:descent`: contraction of the *radical* from larger supports.
* `osq:bb:thm:rational`: the already-known rational one-scale slice.

The new manuscript resolves the first two fixed-workspace questions for
**every nonzero cyclic exponent group**, not for every ordered exponent group.
Its one-scale *rational* formula is credited to the repository. Its new
finite-place criterion concerns algebraic Laurent elements in the specified
normalization. The full rational-exponent Hahn field is not identified with
the smaller bounded-denominator Puiseux field.

## Primary literature and ordinary dependencies

Finite normalization and Dedekind rings:
https://stacks.math.columbia.edu/tag/032L
https://stacks.math.columbia.edu/tag/09IG
https://math.mit.edu/classes/18.785/2017fa/LectureNotes5.pdf

Valuations and ramification:
https://stacks.math.columbia.edu/tag/00I8
https://stacks.math.columbia.edu/tag/0EXR
https://stacks.math.columbia.edu/tag/0EXT

Puiseux theorem:
K. J. Nowak, *Some elementary proofs of Puiseux's theorems*,
Universitatis Iagellonicae Acta Mathematica 38 (2000), 279–282.
https://emis.de/ft/47917

Generalised series / omnific framework:
S. L'Innocente and V. Mantova, arXiv:1710.07304.
https://arxiv.org/abs/1710.07304

Classical context for periodic resolutions:
D. Eisenbud, *Homological algebra on a complete intersection, with an
application to group representations*, Trans. AMS 260(1) (1980), 35–64.
Bibliographic record: https://eisenbud.github.io/papers/index.html

These are classical ingredients or context, not claimed discoveries. The
periodic resolution is proved directly from the annihilator identity; the
manuscript does not apply a Noetherian hypersurface theorem to a ring that
lacks its hypotheses. The targeted literature search does not certify
historical priority.

## Proof checkpoints

1. **Two places are separated.** Laurent expansions are at infinity. The
   integrality obstructions use primes of finite function-field normalizations
   over T=0, never termwise evaluation of an infinite Laurent series.
2. **Exact nilpotence is proved without I=TB.** A finite ideal expression
   would have value at least 1, whereas z_n^j has value j/n. This provides a
   short independent route to the central nonradicality result.
3. **Residue criterion includes regularity.** It is stated for f in B_L.
   Arbitrary rational poles away from zero are not silently ignored.
4. **Arithmetic coefficients are retained.** B=kN means finite k-linear
   span; it does not mean k is a subring of N. This distinction is what makes
   I=TB different from a claim that I=TN.
5. **Refinement is branchwise.** In finite composita normalized values
   multiply by m under T=U^m, and every old prime has an extension.
6. **The limit is support-restricted.** Finite integral relations descend to
   a bounded-denominator stage. Arbitrary Hahn supports need not do so.
7. **Boolean splitting has both an irreducibility and a lying-over step.**
   Fresh ramification at factors of T^2+c forces a quadratic extension; its
   two distinct residues over zero both extend to the full normalization.
8. **No continuum regularity is assumed.** Fewer than continuum many finite
   sets of excluded parameters still form a set smaller than continuum.
9. **The periodic complex is exact over the coefficient fibre only.** The
   arithmetic annihilator is x^(n-j) C, which strictly contains x^(n-j) R.
   The manuscript proves this strictness using the forbidden residue 1/2.
10. **All objects in the new proofs are set-sized.** There is no class Zorn
    argument, no class module category, and no new large-cardinal assumption.

## Verification boundary

`verify.py` uses exact rational arithmetic and finite polynomial/Boolean
models. Its recorded run passes 18,040 checks. This number counts assertions,
not independent theorems or proofs. In particular, clipped-order composition
and threshold checks account for most assertions. The file states its limits.

The full proofs have not been checked in Lean or another proof assistant.
No repository build, independent referee report, or historical priority
certification is claimed. PDF compilation and visual inspection check the
artifact, not the truth of the mathematics.
