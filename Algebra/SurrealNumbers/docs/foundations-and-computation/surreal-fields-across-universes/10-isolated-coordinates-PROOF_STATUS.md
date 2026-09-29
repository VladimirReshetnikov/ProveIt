# Proof status and assumptions

## Scope of the mathematical claims

All the manuscript's new theorem statements have written proofs. They have not
been independently refereed or checked by a proof assistant. The results are
proposed research contributions, not certified breakthroughs or priority claims.

### Reproved prior result

The fresh-sign correspondence for set-presented gaps is already in the ProveIt
`surreal-fields-across-universes` report. The article supplies a self-contained
sign-order proof for use by the later arguments.

### Imported published result

Fischer, Koelbing, and Wohofsky, *Fresh function spectra* (2023), Definition 4.8,
Propositions 4.3 and 4.10, and Theorem 4.24: under GCH, the set-sized Easton
product of ground Cohen forcings preserves cardinals and cofinalities and has
fresh-function spectrum the Easton closure of its coordinates. The regular-limit
clause excludes Mahlo cardinals; the singular-limit clause adds the successor.
This forcing calculation is not claimed as new.

### Written additional arguments

1. The cofinality transport formula explicitly keeps ground regular domains
   separate from their outer cofinalities.
2. The filter-base argument bounds the outer cofinality of a fresh function by
   the size, in the actual extension, of a cofinal base of the generic filter.
3. Initial-segment bases give the complete singleton Cohen and collapse spectra
   without cardinal-arithmetic assumptions.
4. Relative localization reorders the high and low factors, verifies high closure
   after the kept-high forcing, and proves the needed small-poset distributivity.
5. Sparse coordinates give an exact isolated-character profile for all 2^theta
   intermediate grounds, an order-reversing Boolean inclusion pattern, and
   nonisomorphism despite a common saturation spectrum.
6. Set-stage class back-and-forth transports the fields to nonconjugate real forms
   while fixing a prescribed common set-sized conjugation-stable core.

## Important hypotheses

- All external sizes are computed INSIDE the specified final universe N.
- The compared inner universes have the same ordinals and usable class predicates.
- Single-Cohen and single-collapse calculations do not assume GCH.
- The Easton and simultaneous-ground constructions do assume ground GCH.
- The simultaneous forcing is set-sized, not class forcing.
- The class isomorphism and involution constructions use GBC with Global Choice.
  Starting from V=L gives a concrete relative setting with definable grounds;
  no large-cardinal hypothesis is required by the construction.
- A uniform indexed class relation is used, not a set of proper-class maps.

## Deliberately excluded claims

- No proof that equal FULL gap spectra imply isomorphism, and no explicit pair
  with equal full spectra but nonisomorphic fields is asserted.
- No full spectrum formula for every intermediate quotient at accumulation points.
- No automatic equality of ground Cohen posets with recomputed intermediate
  Cohen posets; an equality is proved only for the singleton endpoint where used.
- No preservation of ambient valuation, simplicity, exponentiation, derivation,
  Hahn summation, or omnific integer parts by the class-field maps.
- Saturation assertions concern the fixed finite language, not an arbitrary
  expansion naming a large set of constants. Elementary equivalence over a large
  common core is a separate assertion.
- No solution of a more general published forcing-spectrum conjecture is claimed.

## Finite tests

`verification_results.json` records exhaustive bounded tests of local formulas.
There are no finite fresh signs; the tests do not test freshness, forcing,
cofinality, cardinal preservation, saturation, or class recursion. They also do
not certify mathematical novelty.
