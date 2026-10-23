# Sparse carry encodings for Con(ZFC)

Start with report.pdf and its editable report.tex. This package improves
explicit fixed Diophantine equations for ZFC consistency by changing the
exponent encoding, guard merger, root recovery, and native coefficient
layout. It does not decide consistency or claim a global minimum.

## Main results

- Ten unrestricted integers: degree 69,554,088,184, 1,407 operations.
  This explicitly uses Sun's 2026 Lucas/bridge theorems.
- Nine positive integers: degree 23,321,536,264, 1,378 operations.
  Over nonnegative integers the corresponding circuit uses 1,383 operations.
- Thirteen unrestricted integers without Sun's 2026 reduction: degree
  226,334,238,192, 1,409 operations. The fourteen-integer comparator has
  degree 226,295,141,096 and 1,420 operations.
- Twelve positive integers: degree 901 at 112 operations, or degree 905
  at 110 operations. Shifted three-equation systems have maximum degree
  892 / 896 and cost 106 / 104 operations.
- A new coherent native coefficient tuple has B=2^590069 and 295,388 raw
  bytes, down from 506,664. The actual compressed payloads are included.
  It rebinds the 67-operation polynomial and 59-operation system; it does
  not reduce their operation counts.

All named circuit registers abbreviate polynomial expressions. They do not
add unknowns. Every coefficient is fixed, with no unspecified enumeration
index or truth-dependent choice. Every equation's domain is explicit.

## Reproduce

Use Python 3.10+ with the packages in requirements.txt, then run:

    python3 verify.py

The 19-stage verifier checks the sealed file manifest, rebuilds 46 files in a temporary copy,
and requires byte-identical regenerated artifacts. It leaves the original
release unchanged. Run negative_controls.py separately for three deliberate
corruption controls. These finite audits support implementation and proof
inspection; they are not tests of unbounded unsolvability.

## Layout and bindings

- sun/: ten-integer equation, complete source-interface proof, TeX/PDF,
  fixed parent, coefficient recipes, byte payloads, generator and verifier.
- nine/: natural/positive nine-variable equations and strict near-square
  majorant, with exact degree certificates.
- signed_audit/: fixed-polynomial carry proof, cofinal-base review, merged
  interval/approximation guard, thirteen/fourteen-integer equations.
- positive/: unit inner-separator proof and eight low-degree presentations.
- native/: new aggregate complement decoder, complete coefficient generator,
  rebound P67/system59, literal machine binding and rank certificates.
- quartic/: parent-elimination review and independent Sun/positive reviews.
- root_checks/: independent finite-field/collision, carry, norm, decoder and
  live-circuit checks, plus the skeptical release review.
- review/: pinned comparison sources and the post-pin formalization status.

The low-variable families share the complete package-31 121-by-8801 tuple.
Their active bindings identify the shared bytes under sun/sources/data.
The new native complement tuple is a DIFFERENT complete tuple, bound only
to the two native/ equations. Never splice coefficient ports between them.
The positive family points explicitly to the shared Sun31 tuple. Historical
source bindings are retained as provenance and are not implicit rebinding.

## Proof level

The new two-sided adapters are ordinary mathematical proofs formalizable
in ZFC, conditional on the explicitly imported literal-machine calibration,
compiler and arithmetic theorems. No new end-to-end Lean/Rocq certificate
or exported object-language ZFC derivation is claimed. The newer repository
formalization work log is included and its open obligations remain open.
No sub-ten unrestricted or sub-nine natural-variable claim is made.

Pinned comparison: 22e75dd6b87b1b199bb08c778d7cf075ae5aae08.
Post-pin formalization-only update: 8747904f8b973f9016434993e7ec6ae6ec7549ef.
Read NOTICE.md and inherited notices before incorporation. New material is
MIT No Attribution. No external repository was changed by this work.

