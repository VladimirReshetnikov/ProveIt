# Primitive odd carriers

Read PROOF.md for the full ordinary proof; report_section.tex is ready for the
combined report. All variables range independently over the unrestricted integers.

| Complete fixed equation | Variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| integer14_degree86_ops112.json |14|86|112|
| integer14_degree94_ops110.json |14|94|110|
| integer13_degree156_ops125.json |13|156|125|
| integer14_degree88_ops115.json |14|88|115|

The first two are new zero-existence reductions from the literal retained
fifteen-variable source. The last two preserve the old output polynomials
pointwise and simply compile their unit factors directly. The86/112 equation
dominates the88/115 row and the prior88/119 row;94/110 is a cost/degree tradeoff.
No global optimality, consistency proof or new proof-assistant theorem is claimed.

## Replay

Python3 with SymPy is required for the independent checker; the builder and
coefficient reconstruction use only the Python standard library.

    python3 build.py
    python3 check.py
    python3 -O check.py
    python3 reconstruct_coefficients.py
    python3 -O reconstruct_coefficients.py

The reconstruction wrapper imports the unchanged recipe's construct() function,
whose entire reachable validation uses explicit require/raise, with no assertions
or optimization-dependent branches. Both modes reconstruct and compare all six
payloads byte for byte and produce identical receipts. The legacy recipe's own
__main__ refusal under -O remains unchanged and is not invoked. See
RECONSTRUCTION_MODES.json for the source inspection and both-mode comparison.
The algebraic/DAG checker also uses explicit conditions and passes under -O.
CHECK.json, CHECK_OPTIMIZED.json, REBUILD.json and COEFFICIENT_REBUILD.json record
the released results. The independent peer review is delivered by the enclosing
packet. Rebuilding changes generated receipts only; compare supplied hashes first
when unchanged-source authentication is desired.

## Files and dependency boundary

- The four JSON DAGs contain every actual gate, variable and fixed-numeral binding.
- Each *_spec.json gives every polynomial abbreviation in evaluation order.
- baseline/ retains immediate source equations/proofs, original independent cut
  specifications, coefficient bytes and the known leading-form correction.
- recipe/ retains the complete native machine/tile numeral reconstruction.
- source_closure/ retains the inherited signed-Pell/native source dependency
  notes, with CLOSURE_MAP.md separating that inherited theorem from new algebra.
- BASELINE_PINS.json and SOURCE_CLOSURE_PINS.json authenticate copied sources.

The complete coefficient tuple is unchanged: beta=2^1064921−1,K0,MC,MF already
shifted,cone_A=2^1113,cone_B=2^666104;615,883 raw bytes. Every numeral is rebuilt
and compared byte for byte. Finite checks do not decide zero existence and do not
reprove the unbounded source compiler/refutation theorem.
