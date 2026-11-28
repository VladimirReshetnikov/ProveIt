# Lean architecture and the finite spectral trace replacement

Audited revision: `f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f`.

## Baseline and scope

The pinned `Lean/grh/src` tree contains 803 Lean modules and 476,849 physical
lines, counting comments and blank lines. All 803 are reachable from the
`Main` module by a static traversal of `import` declarations. This is an import
closure, not a declaration-level dependency count. It supplies no evidence
that every declaration is used, but rules out a large saving by simply removing
unimported files. The machine-readable counts are in `lean_source_metrics.json`.

The four relevant modules have the following physical sizes:

| Module | Lines | Declarations |
| --- | ---: | ---: |
| `Lib/Adelic/TraceFormula/LineDeterminant.lean` | 367 | 26 |
| `Lib/Adelic/TraceFormula/LevelCut.lean` | 385 | 30 |
| `Lib/Adelic/TraceFormula/CuspidalComparison.lean` | 114 | 3 |
| `New/Spanning/Multiplicities/EqualMultiplicities.lean` | 399 | 16 |

The complete `Lib/Adelic/TraceFormula` subtree has 7,438 lines. The proposed
spectral replacement targets only the moment-recovery layer, not that entire
subtree. A report must not count 7,438 lines as removable.

## Existing architecture

`LineRelation d c A Tp Tm e` asserts positive real `d,c`, idempotence of `e`,
adjointness of `Tp,Tm`, the identity `Tp*Tm=d*(1+c*e)`, and commutation of `A`
with both operators. The endpoint `LineRelation.trace_mul_mean_eq` assumes

    trace(A^(l+1) * Tp^(i+1)) = trace(A'^(l+1) * Tp'^(i+1))

for every pair of natural indices `l,i`, and concludes equality of
`trace(A*e)` and `trace(A'*e')`.

The proof decomposes into generalized eigenspaces of `A`, recovers traces of
positive powers of `Tp` on every nonzero eigenblock, recovers characteristic
polynomials there, compares determinants, recovers ranks of `e` on the blocks,
then reassembles the weighted trace. `LevelCut.trace_eq_of_trace_cutLevel_eq`
transports this to adelic levels, and `CuspidalComparison.trace_eq_of_isCuspidalAt`
supplies all the two-index trace comparisons by the geometric trace formula.

## New finite first-order trace theorem

Let `V,V'` be finite-dimensional complex inner product spaces. Suppose

    TT* = d(I+ce),    T'T'* = d(I+ce'),
    e^2=e,           e'^2=e',
    d>0, c>0,

and `A` commutes with `T,T*`, while `A'` commutes with `T',T'*`. Let `S` be the
union of the *distinct* eigenvalues of `T` and `T'`, and put `s=#S`. Then `0` is
not in `S`, and `s <= dim V+dim V'`. Equality of the finite list

    trace(A T^j) = trace(A' T'^j),    1 <= j <= s,

already implies `trace(Ae)=trace(A'e')`.

No powers of `A` above the first appear. Neither `T` nor `T'` is assumed normal.

### Full mathematical proof of the spectral certificate

Set

    f(z) = log(|z|^2/d) / log(1+c)       (z != 0).

Interpolate the values `f` at `S` and the value zero at zero. Lagrange
interpolation gives a polynomial `p` with `p(0)=0`, `deg p <= s`, and
`p(lambda)=f(lambda)` for each `lambda` in `S`.

We claim `trace(Ae)=trace(A p(T))`. First let `A` be self-adjoint. Decompose
`V` into the orthogonal eigenspaces `H_alpha` of `A`. Since `A` commutes with
both `T` and `T*`, each `H_alpha` is invariant under both. It is also invariant
under `e=(d^-1 TT*-I)/c`; on each block the same line relation holds.

Write `n_alpha=dim H_alpha` and `r_alpha=rank e|H_alpha`. Taking determinants
on the block gives

    |det T|H_alpha|^2 = d^n_alpha (1+c)^r_alpha > 0.

This proves invertibility of `T` on each block (also globally). For the
eigenvalues of `T|H_alpha`, counted with their algebraic multiplicities,

    sum_lambda f(lambda)
      = [log |det T|H_alpha|^2 - n_alpha log d] / log(1+c)
      = r_alpha.

The trace of a polynomial is the sum of its values on these eigenvalues with
algebraic multiplicity. This fact follows by triangularization; it does not
require diagonalizability of `T`. Therefore

    trace(A p(T))
      = sum_alpha alpha trace(p(T|H_alpha))
      = sum_alpha alpha r_alpha
      = trace(Ae).

For arbitrary `A`, write

    H=(A+A*)/2,   K=(A-A*)/(2i),   A=H+iK.

Both `H` and `K` are self-adjoint and commute with `T,T*`: the two commutation
identities for `A` imply the corresponding identities for `A*` after taking
adjoints. Apply the preceding argument separately to `H,K` and use complex
linearity of trace. The same polynomial works for `T'` because it was chosen
on the union of the spectra. Expanding the zero-constant polynomial into its
positive powers now gives the conclusion from the listed moments.

### Why this is not a functional-calculus identity

The conclusion is a trace pairing identity on the commutant. It is generally
false that `e=p(T)`. Likewise, commutation with `T` alone is insufficient.
Nonnormal and Jordan-block examples in the audit should be retained in the
deliverable to prevent these two tempting but invalid shortcuts.

## Source migration

1. Preserve `LineRelation`, its restriction operation, `norm_det_sq`, and the
   elementary rank/determinant lemma. These are useful source interfaces and
   directly support the new proof.
2. Add `trace_mul_eq_trace_mul_spectralPolynomial`, the mathematical certificate
   proved above. Add the finite first-order trace recovery theorem.
3. Change the hypothesis of `trace_eq_of_trace_cutLevel_eq` from all
   `A^(l+1) Tp^(i+1)` to `A Tp^(i+1)`. The existing `offAction` and `localAction`
   identities can specialize the old power lemma at `l=0`; no level definitions
   or local counting theorem need change.
4. In `trace_eq_of_isCuspidalAt`, supply the comparison for the finite test
   function `lineHecke^(i+1) * offPlace(a)`, rather than for a positive power
   of `a`. Cuspidality remains available for the original `a`, and the positive
   power of `lineHecke` still supplies the simple-zero condition. The external
   statement of this theorem can remain unchanged.
5. Preserve `charpoly_eq_of_trace_pow_eq`, or replace it with a direct Mathlib
   Newton-identity result after verifying the exact API. It is used by
   `EqualMultiplicities.charpoly_heckeOnGood_eq`, so it is not dead code merely
   because the new recovery theorem stops using it. Keeping this helper may
   also retain part of the old generalized-eigenspace infrastructure until an
   independent replacement is made.

The exact number of lines saved is not yet established. The definite advance
is a strictly weaker, finite, one-index moment hypothesis and elimination of
the need to insert higher powers of the off-place operator into the geometric
trace formula. A full formal port may or may not reduce physical lines until
the spectral-certificate lemma and characteristic-polynomial helper are
optimized. No percentage reduction should be claimed on the present evidence.

## Formal support file and verification boundary

`SpectralTraceCore.lean` formalizes:

1. finite interpolation at nonzero nodes with zero constant coefficient and
   degree at most the number of nodes;
2. finite positive-moment transport for arbitrary linear functionals;
3. its weighted-trace specialization;
4. the scalar logarithmic extraction of rank from the determinant norm formula;
5. the final trace transfer conditional on the two polynomial trace certificates.

`SpectralTraceSpectrum.lean` additionally formalizes a common zero-constant
interpolant on the characteristic roots of two endomorphisms with nonzero
determinant, with degree at most the sum of their dimensions. Its two supporting
lemmas prove that zero is not a characteristic root and that the number of
distinct characteristic roots is at most the dimension.

The certificate from the line relation and the GRH source adapters are not
formalized here. These support files do not import or rebuild the GRH project.
Their `#print axioms` checks must be reported separately from the human-readable
proof. Both files compiled successfully with exit status zero and no warnings;
every printed theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

The available runtime is Lean 4.35.0 at
`/workspace/scratch/37fbfd908a4b/research/runtime/lean-4.35.0-linux/bin/lean`.
The Mathlib checkout is commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. An isolated overlay compiled the
missing `Mathlib.LinearAlgebra.Lagrange` and `Mathlib.LinearAlgebra.Charpoly.Basic`
modules without modifying that checkout.

### Why the full certificate was not kernel-checked here

A focused API investigation found no ready theorem in this Mathlib revision
stating `trace(p(T)) = sum_lambda p(lambda)` over the characteristic roots,
and no convenient matrix triangularization-basis theorem. The identity is
straightforward mathematics, but its formal port needs an adapter built from
generalized eigenspaces, nilpotent traces and polynomial evaluation. Further
adapters then combine the logarithm of the determinant root product, spectral
inclusion for restrictions, and the symmetric-operator decomposition of `A`.
The relevant existing endpoints are
`LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent`,
`LinearMap.trace_eq_sum_trace_restrict`,
`Module.End.det_eq_prod_roots_charpoly_of_splits`, and
`LinearMap.IsSymmetric.direct_sum_isInternal`.

No unfinished Lean file, `sorry`, extra axiom, or replacement of the missing
certificate by a claimed formal result is supplied. This is a concrete
formalization boundary, not a mathematical gap in the written proof.
