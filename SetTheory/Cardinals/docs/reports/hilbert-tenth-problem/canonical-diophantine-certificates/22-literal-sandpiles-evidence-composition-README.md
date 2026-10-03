# Precisely counted literal sandpile certificate composition

Read PROOF.md for the theorem, source boundary and full ledger. For any fixed nonempty rectangular prism, the new binary specialization has a unique natural witness exactly when the global sandpile stabilizes there with a binary odometer. It uses8V+6E+H witnesses,8V+7E+H nonnegative summands, degree3 and a mandatory full external halo. This specializes the existing10V+6E compact compiler; it is not an unbounded fixed-arity result.

Portable release layout is composition/ beside loader/. The default loader path is the sibling ../loader, with no fallback to the author's workspace. Run scoped verification:

    python test_prism_certificate.py
    python -O test_prism_certificate.py

Small general example and exact collected ledger:

    python prism_certificate.py --lengths 2 1 1 --seed 6 --collect

Huge literal dimension-only ledger, with no background expansion:

    python literal_composition.py --ell 10 --right 1 --time 40 --head 0

Literal raw coefficient stream (can be astronomically large):

    python literal_composition.py --ell 10 --right 1 --time 40 --head 0 --stream raw

The time/head arguments specify a candidate containment prism; they do not assert or verify a halt. --take limits emitted records, but a fully collected stream computes its global constant first, so --take does not make that path cheap. The default hypothetical bound example is not a U15 halting result.

The implementation can emit fully collected coefficients with bounded local workspace, charging at most10738 local raw records per vertex bucket. The background is a literal bounded evaluator tied to the separately frozen loader manifest, not a table materialized here. All test/size/materialization limitations are explicit in PROOF.md.

For separate source directories, pass --loader-root /path/to/literal-loader to test_prism_certificate.py or literal_composition.py. Review scripts reside in review/ and may use their own documented replay interface.
