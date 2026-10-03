# Research and verification status

## Mathematical setting

The main class-theoretic setting is GBC = GB + Global Choice. In this document,
GB alone does not silently include set choice. Classes have sets as members;
there is no same-level class of proper classes. A class well-order is required
to give a least point to every admitted nonempty subclass.

The termination theorem assumes a set-cut saturated class alphabet. A marker
is an extra symbol at a specified class cut. "Set-cut saturated" allows either
constraint side to be empty. The arbitrary-word, injective-word, and strictly
increasing-word carriers are distinct ordinary classes of set functions.

The global enumeration and raw-order domains are predicates on class
functions/relations. Statements about all their elements are not statements
about an ordinary class carrier. The dense-core interpolation theorem requires
uniformly set-indexed families.

## Additions in this manuscript

- Theorem 5.2: exact termination-marker criterion for arbitrary and injective
  set-length words. The endpoint alternatives are part of the theorem.
- Theorem 6.1: exact, uniform point characters for interior markers.
- Theorem 7.1: countable cut obstruction for increasing words at every fixed
  marker placement, even after removing the empty word.
- Theorem 10.2: least-representative set-interval block decomposition.
- Theorem 11.3: explicitly defined polynomial condensation hierarchy for every
  given admitted class well-order; these examples need no ETR axiom.
- Theorem 12.2: prescribed internal raw-order complexity between any two
  distinct set-like exhaustive enumeration endpoints.

The numbers above refer to the distributed PDF/TeX. All these assertions have
written proofs. No historical-first or peer-review claim is made. The
set-interval construction is a size-relative analogue, not an application
of a theorem about finite condensation with the word "finite" erased.

## Prior results credited and re-proved

Fixed-set cardinality/universality/ordinal spectra, direct raw comparison,
and the set-supported dense core and uniform small-cut interpolation are
credited to the repository and its companion reports. Their inclusion provides
context and reusable proofs; it is not a claim of new discovery.

The fine singular-cutoff dichotomy and previous cut-recognition,
automorphism-extension, and support-bound results are not dependencies of the
new proofs, and are not certified by this manuscript.

## Checks performed

- The finite Python checker ran successfully: 547,480 exact checks, seed
  20261003. See `data/finite_checks.json` for separate counters.
- The checks include comparison consistency, convex cylinders, bounded
  crossing chains, finite-vector polynomial ordering, tail equivalences,
  least representatives, finite raw comparison, and a paired diagonal.
- The TeX compiled successfully with pdfLaTeX. The final log contains no
  undefined references/citations, duplicate destinations, or overfull boxes.
- All 30 PDF pages were rendered and inspected for layout. Key formula and
  interface pages were also inspected at larger resolution.

The checker does not prove the infinitary theorems. All finite intervals are
sets, so a finite test of the class/set distinction would be vacuous. No Lean
executable was available, no Lean proof was generated, and no repository
formalization build was performed. The formalization section is a proposed
implementation plan using source interfaces actually inspected.

## Main unresolved boundaries

General condensation iteration may require additional class-recursion
principles; GBC + ETR is a sufficient framework, not claimed necessary for
this operator. The explicit polynomial examples do not settle whether every
raw class well-order eventually collapses. They do not give one hierarchy
indexed by a supposed order of all class well-orders. Internal condensation
complexity is not asserted to be definable from the bare outer lexicographic
order. The ten research questions preserve these distinctions.
