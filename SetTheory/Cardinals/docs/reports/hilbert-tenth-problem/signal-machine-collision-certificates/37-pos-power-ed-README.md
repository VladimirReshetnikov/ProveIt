# Exact interpolation degree

This separate, unnumbered arithmetic continuation proves the exact degree of
the retained three-witness bounded-halting polynomial for every horizon.
It preserves the original packet and sealed Report 66.

For K=T+1 and N=K^2, the two interpolation polynomials have degree N-1 when K
is even and N-2 when K is odd and at least 3. The proof establishes explicit
integer leading coefficients and their signs. A finite roots-of-unity identity
reduces the delicate odd-K case to a strictly positive alternating sum.

The exact joint total degree of the six-square polynomial is:

- T=0: 2
- Positive odd T: 4(T+1)^2-4
- Positive even T: 4(T+1)^2-8

These statements hold for every acceptance subset. The full highest homogeneous
part is explicitly (1+K^4) a_K^4 j^(4 delta_K), where a_K is the leading
coefficient of the integer-cleared U interpolant and delta_K is its degree.

Start with `PROOF.md`. `HANDOFF.md` identifies the independent-review targets.
`exact_degree_check.py` is a fresh inspected checker based on finite differences
and Newton interpolation. It passed:

- Full finite-difference degree and coefficient checks for K=1,...,40
- Full interpolation reconstruction and 285 node checks for K=1,...,9
- 38 complete five-variable, six-square expansions for K=1,...,7
- Every acceptance subset at K=1 and K=2

Finite evidence is in `evidence/exact_degree_results.json`. The all-horizon
theorem is the proof, not an extrapolation from those checks. No source script,
machine interpreter, physical simulator, upstream code, or Lean was executed.
The main theorem imports no Pell or physical result; retained copies preserve
the context of the optional native-gap degree corollary.

`SOURCE_PINS.json` records provenance. `MANIFEST.json` hashes all other packet
files. The before/after source inventories match exactly. No novelty,
minimality, or fixed-polynomial unbounded-halting claim is made.
