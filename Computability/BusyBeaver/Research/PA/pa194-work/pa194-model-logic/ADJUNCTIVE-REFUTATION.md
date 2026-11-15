# Finite-adjunctive refutations imply target provability

`finiteAdjunctive_refutation_target` proves that for any model-internal code d, an internal proof of falsum from the finite relational theory `adjunctiveTheory` (five equality axioms plus weak adjunction) implies `TargetProvable 1`. The proof chooses the existing finite-adjunctive numerical simulation, its admission bound, and the canonical seeded initial environment for d; it applies the compiler and the target translation of falsum. No simulation, environment, admission or bound is left as a theorem assumption. The source model satisfies PRA and IΣ₁, and proof codes may be nonstandard.

The result concerns the finite adjunctive source theory, which has not been identified with PA; it does not by itself establish scheduler halting, physical machine halting, native iPRA derivability, or the requested PA/machine equivalence.

The incremental replay rebuilt the source and combined QF-existential-import audit top against the separately source-replayed finite simulation and its dependencies. Two main axiom reports are free of `sorryAx`; other workspace objects are retained prebuilt. This is not a clean whole-workspace build.

The independent incremental source replay passed against the separately replayed finite simulation and its dependencies, with workspace objects retained prebuilt. Run `check-adjunctive-refutation.sh --out OUTPUT` for the repository source-closure audit and two axiom reports; `check_bridge.py` documents retained workspace foundations.
