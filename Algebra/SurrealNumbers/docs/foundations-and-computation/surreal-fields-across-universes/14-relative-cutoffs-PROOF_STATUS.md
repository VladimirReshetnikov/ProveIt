# Proof status and scope

## Overall

Written mathematical proofs are supplied. No independent referee assessment or
Lean verification has been performed. The finite test program cannot certify
the transfinite assertions. The report uses the exact hypotheses stated in its
theorems, and the priority of its relative-spectrum formulations is not certified.

## Contributions developed in the report

| Result | Location | Evidence supplied |
|---|---|---|
| External cofinality pushforward | Theorem 4.1 | Two explicit codings, using old ordinal codes and fixed-length sign blocks |
| Full single-Cohen gap spectrum without GCH | Theorem 5.3 | External dense-size bound, enumeration of all ground short strings, and distributivity |
| Exact finite relative spectra | Theorem 7.1 | Product preservation, short-name localization and mutually generic intersection |
| Exact countable relative spectra for every intermediate subproduct ground | Theorem 9.1 | Explicit lower witnesses and a rectangular exclusion argument; the infinite-tail lower witness uses the published theorem below |
| Exact cutoff gap pairs and equal cardinality | Theorem 11.3 | Fresh-sign/birthday-boundary dichotomy, explicit old boundary signs, and counting names |
| Common-threshold nonconjugate real forms | Theorems 12.1, 12.3 | Set transcendence-basis argument; separate uniform set-stage class back-and-forth |

These are proposed contributions relative to the inspected baseline. The
single-ground Easton spectrum, sign-gap correspondence and underlying classical
methods are not claimed as new.

## Explicit imports

1. Classical surreal real closedness and real closedness of No_<theta for
   uncountable regular theta, plus the simplest-separator birthday bound.
2. Standard forcing theorem, product factorization, closure/distributivity and
   small-forcing preservation facts.
3. Quantifier elimination for real closed fields; algebraically closed field
   classification by characteristic and transcendence degree.
4. The repository's fresh-sign bridge, reproved as Theorem 3.3 here.
5. **The specialized published input:** Fischer, Koelbing and Wohofsky,
   *Fresh function spectra*, Corollary 4.21 (2023), based on Shelah,
   *Embedding Cohen algebras using pcf theory* (2000). A full product of Cohen
   forcings at an unbounded set of regulars below a singular lambda adds a
   lambda^+-Cohen subset under GCH. The article states it as Theorem 8.3.
   Its pcf proof is not reproduced or independently verified here.

The fifth input is needed only to put lambda^+ into the relative spectrum when
the missing coordinate set is infinite. All exclusions, the finite construction,
and the single-Cohen result do not use it.

## Critical hypotheses and checks

- All relative forcing posets remain the *ground* posets. The argument does not
  replace them with Add(kappa,1) recomputed in an intermediate universe.
- Short-name localization uses the closure/distributivity of the high factor
  in the original ground. It does not assert that old closure persists after
  lower forcing.
- To keep a fresh witness out of the *new base* M_A, the proof uses the
  intersection of mutually generic disjoint subproduct extensions. Persistence
  of freshness with a fixed base alone would be insufficient.
- Full support at the countable singular limit is explicit. An infinite
  missing set contributes lambda^+; omitting this term would be wrong here.
- Cardinalities and cofinalities in the order invariant are ambient ones.
  Ground regular indices and outer cut characters differ when forcing collapses
  cardinals. This is essential for the no-GCH Cohen theorem.
- Genuine gaps have neither endpoint and have nonempty sides. At a cutoff the
  exact boundary includes asymmetric pairs (mu,theta) and (theta,mu).
  Only the full old proper-class field has the all-symmetric conclusion.
- Class isomorphisms respect sets; the class construction is explicitly in
  GBC + Global Choice with the relevant inner-model predicates.

## What is not proved

- General classification of old fields having equal complete gap spectra.
- Arbitrary fresh-spectrum or gap-spectrum realization.
- Elimination of the singular-successor character under cardinal preservation.
- Compatibility with valuations, surreal exponentiation, derivations,
  normal-form summation, simplicity or omnific integer predicates.
- An arbitrary continuum size or an arbitrary cardinal-sized index family.
- A formal consistency proof of ZFC, or existence of transitive models in ZFC.
- Any new Lean-checked theorem.

## Finite regression scope

The Python run passes 619,026 assertions across sign-cone, prefix-bound,
block-code, finite Boolean and eventually-periodic-index identities.
The eventually periodic sets are exact descriptions of ordinary subsets of the
natural numbers; their checks validate index manipulations, not the spectrum
theorem. There is no finite model here of a fresh sign over an inner universe.

Recommended independent review order: Lemma 6.1 (localization), the retained-
coordinate exclusion in Theorem 9.1, the use of mutual genericity for the
lambda^+ witness, Lemma 11.1 (asymmetric boundary cases), then the uniform
class recursion in Lemma 12.2.
