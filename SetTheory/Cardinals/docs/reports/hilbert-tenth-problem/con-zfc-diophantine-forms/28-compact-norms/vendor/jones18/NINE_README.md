# Nine-variable equation with a signed divisor and structured majorants

This subpackage defines one ordinary polynomial in **nine nonnegative integer
unknowns**. Its degree is exactly

    93264*5^33 + 288 = 10857358574867248535156250288.

The literal division-free DAG has **20,547 binary operations**: 668 additions,
23 subtractions, and 19,856 multiplications. Every fixed exponent is expanded
into multiplication gates. All 20,911 nodes are live; exactly nine leaves are
unknowns. The 348 nonliteral fixed leaves have complete bounded recipes.

Relative to package 18-jones9, this is a **42.3741380589% degree reduction** for
16 additional binary operations. It does not reduce the variable count or beat
the low-operation direct Pell equations. No global optimality is claimed.

## Mathematical result

Composing the ordinary proofs in `sections/nine.tex` with the explicitly
identified Jones, native/Pell compiler, and K215 calibration theorems gives

    ZFC proves: no nonnegative solution of this equation iff Con(ZFC).

This is an equivalence, not a proof of consistency. The new complete endpoint
has not been kernel checked in Lean or Rocq.

The improvement has two parts:

1. Polynomial bounds adapted to the actual expressions reduce the degrees of
   the two radical weights. The proof first establishes R != 0 modulo q,
   without assuming that R is positive or any final equation holds.
2. A signed-divisor relation-combining lemma replaces the squared divisor and
   squared dividend by a signed divisor and an unconditional quotient bound.
   The last natural unknown still enforces the positive margin.

Every bound is proved before enforcing the square, divisibility or margin
conditions. Cases with negative R, zero C or zero H are included.

## Exact fixed instance

Use the entire materialized compact Wang943 tuple, with

    beta -> beta.bin
    K0   -> K.bin
    MC   -> MC.bin
    MF   -> MF_source.bin

The last port is the shifted native mask, MF_native+B-1. `vendor/jones18/NINE_BINDING.json` records
all four hashes and the precise index recipe. There are no free compiler
parameters or unspecified recursively enumerable indices.

The inherited 32-variable parent remains byte-for-byte package 18's
`base/quartic32.upstream.json`, SHA-256

    149eacd479896a113d869c5b74163efa4dab2cabaca8b581a6405cc9f580ca60.

Its relative-path metadata describes an earlier binding. The enclosing
release's **whole Wang943 tuple** is authoritative here. The mathematical
adapter is justified by the compiler interface theorem; matching four modular
congruences would not suffice.

The parent uses the old positive transport quotient in row 16. The proof
section records the relation to notes that use the shifted quotient. No row
or coefficient of the parent is changed.

`circuits/nine/constants.json` defines the 346 nonzero weighted coefficients, z_index and
y_index. `circuits/nine/index_bound_s.json` is the exact polynomial recipe for the exponent
in z_index=2^s. These index integers are not expanded. The four lower-level
compiler coefficients are materialized and authenticated; the much larger
Jones index constants are specified by finite formulas.

## Reproduce

The only runtime dependency is Python 3's standard library. Run, with paths
adjusted to the enclosing release layout:

    python3 code/nine_structured.py vendor/jones18/quartic32.upstream.json circuits/nine
    python3 code/verify_structured.py vendor/jones18/quartic32.upstream.json circuits/nine compiler/coefficients_compact

The coefficient directory may contain the four `.bin` files or their `.bin.gz`
forms. The verifier accepts either, verifies the uncompressed SHA-256 hashes,
and evaluates the exact fixed instance modulo three primes without expanding
its index constants.

The generator writes `circuits/nine/constants.json`, `circuits/nine/index_bound_s.json`,
`shifted_quartic.json`, and `nine_structured_dag.json`. The verifier writes
`verification.json`; it regenerates the delivered DAG in memory and checks
exact source/index records, operation counts, symbolic leading terms, direct
finite-sum formula evaluations, and signed/degenerate arithmetic cases.

The mathematical proofs establish the unbounded equivalence. These finite
checks support source fidelity, implementation and algebra; they do not
establish consistency, run K215 to a halt, or decide the equation's solvability.

## Provenance

The new generator is derived from package 18's `nine/nine_compressor.py`,
preserving its normalized quartic, bounded index construction and Jones body.
The new weight and finalizer branches are the changes proved here. The source
file, degree, and semantic comparisons are against ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. All listed upstream files were compared byte-for-byte
with this exact pinned revision. Retain the enclosing release's upstream licenses
and source manifest. The new proof and verification work is AI-assisted.
