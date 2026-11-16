# Observational transport at arbitrary formula depth

`observationalRewrite_all_codes` proves bidirectional target implication under
observational equality for every internally valid source formula, including
nonstandard codes and arbitrary nested quantifier depth. It compares the same
source code and binder base under two initial bound stacks, with the same free
stack. The hypotheses bound the distinguished labels below the base, place
the root code's allocation range and relevant stack entries below the reserve,
and require bounded alignment of the two bound stacks.

A Σ₁-definable depth relation and internal bounded-depth induction carry the
proof through atoms and quantifiers. The theorem does not compare different
binder bases. General alpha/base-shift conversion, parameter renaming for
closed separation axioms, a complete compiler, PA identification, and the
physical-machine/consistency equivalence remain open.
`check-observational-general.sh` replays the source closure and checks five
axiom reports. Retained objects and workspace foundations require their own
provenance.
