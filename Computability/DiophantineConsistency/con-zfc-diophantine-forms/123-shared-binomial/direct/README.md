# One binomial for factorial and CRT arithmetic

The principal equation is an explicit degree-four polynomial in **319
nonnegative integers**, with **254 quadratic residuals**, **10,283
collected monomials**, and coefficient height **86,842,335**.

Its complete literal definition is the sum of squares of the residuals
in `equation319/natural/equation.json`. The equivalent fully collected
coefficient list is `equation319/natural/expanded_polynomial.json`.
Each monomial is encoded by the list of its variable indices, including
repeated indices; the empty list denotes the constant monomial. All indices
are zero-based. The variables array specifies their order.

The lower-height square-shell companion `equation320` has 320 natural
unknowns, 255 quadratic residuals, 13,828 monomials and height 15,248,812.
Its different syntax is transported by the retained square-shell calibration.
The main 319-variable result uses the original Cantor C222 syntax.

## Mathematical contribution

Use `B=binom(F^2+t,t)` both in the inherited squared-radius factorial fixed
point and as the reciprocal CRT product. The independent radix
`q=N^K`, `N=B^K`, `K=2R`, with `B>=2`, validates that same binomial before
assuming its intended meaning. A common modular Pell root then replaces
eleven full binomial numerator powers. The complete compiler uses six exact
power requests, one exact binomial, ten divisibility ranges and fifteen
independent Pell indices.

The squared-radius factorial fixed-point lemma was already proved in
package 105, and the modular-residue lemma in package 108. The new result
is their integrated use with the Round 14 reciprocal/factorial-carrier
architecture, its independent radix bootstrap, and the measured complete
equations. See `PROOF.md` and `INDEPENDENT_REVIEW.md`.

The ordinary theorem, composed with the retained C222/ZFC refutation
calibration, is that ZFC proves no natural zero iff Con(ZFC). This does not
decide consistency, provide a new Lean proof term, or claim global minimality.

## Reproduction

Only the Python 3 standard library is needed. No network is used.

```sh
python3 -B verify.py
python3 -B verify.py --equation equation320
python3 -B check_semantics.py
python3 -B reproduce.py
python3 -B -O reproduce.py
```

The independent checker verifies all natural restoration identities and
every coefficient of each quartic. Reproduction rebuilds the principal and
companion equations from the retained sources into a temporary directory,
compares every generated JSON file byte for byte, and deletes the temporary
directory. These checks do not search for roots or establish unbounded
claims by testing.

To produce a fresh principal equation:

```sh
python3 -B build_modular_factorial.py --radix power --merge-factorial --output NEW_DIRECTORY
```

## Provenance

The reviewed public ProveIt snapshot is
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6` (24 October 2026). The exact
Round 14 input arrived as `ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`
in `docs/incoming`. `frozen_round14` preserves its imported compiler files,
source proofs and notices. Its historical source pins remain unchanged.
`provenance/squared_radius_factorial_105.md` gives the preexisting factorial
theorem; `provenance/pell_residues_108.tex` gives the preexisting residue
construction. `SOURCE_LEDGER.json` records exact SHA-256 identities.

New material is AI-assisted research prepared for ProveIt. Independent
review means a separate mathematical and computational audit within this
workflow, not an external human endorsement. Inherited material retains
its licenses and notices.
