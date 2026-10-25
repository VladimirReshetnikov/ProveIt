# Independent baseline and mathematical review

## Reviewed target and conclusion

This review concerns the combined pooled-residue construction at the frozen
ProveIt source commit `f4d8db99e060339f3306a04d507c35bc1d0d68c5`, the final
`final_sparse` and `final_small` data, and the accompanying
`output/con_zfc_pooled_residues/report.tex` as read on 2026-10-25 UTC.

The independent review found no mathematical defect in the selected equations.
The two selected outputs have the claimed metrics:

| Output | Natural variables | Quadratic residuals | Expanded terms | Coefficient height | Degree |
|---|---:|---:|---:|---:|---:|
| Recommended sparse form | 234 | 183 | 9,019 | 87,741,134 | 4 |
| Companion smaller-variable form | 233 | 182 | 50,762 | 88,674,690 | 4 |

This is a reduction within the repository's direct finite-refutation compiler
family. It is not a variables-only record among every Diophantine representation
in the repository, a proof of optimality, or an independently established claim
of worldwide novelty.

## Mathematical points independently checked

1. **The growth frame must include modular indices.** The frame includes every
   exact-power base, exponent, and output atom, together with all eleven modular
   upper-index atoms. Including only the exact-power atoms would not justify
   simultaneous recovery of the modular seed indices. The final offset of 16
   covers fourteen independent seeds and also makes `q+1<W` without adding a
   redundant `q+1` atom.

2. **The cap index and size budget are distinct.** The cap is at
   `H=J(A_a,A_b,A_c,A_d)`, whereas the error estimate uses `W`. Soundness does
   not assume that intended indices are below `H`: the cap bounds the decoded
   indices by `H<W`, the frame bounds the intended indices by `W`, and the
   pooled sum of squares is less than `W^3<A-1`. Divisibility then forces every
   decoded index to equal its intended index. Thus no omitted dominance guard
   is needed.

3. **The CRT lift establishes completeness of the reused cap.** Each of the
   nine encoded representatives initially lies in `(0,N^2]` and has common
   period `N^2=product_i d_i^(2K)`. Adding `N^2` to `A_a` preserves every local
   polynomial congruence. The shifted representative is at most `2N^2`, the
   total is at most `10N^2`, and `J>=2A_a^2>2N^4` dominates all fourteen other
   seed indices. This proves existence of cap witnesses without a new
   existential dominance condition.

4. **The changed aggregate bound preserves digit separation.** For ordinary
   upper indices bounded by `10N^2`, the binomial coefficients through the
   requested lower indices remain below `q=N^K`. The separate source majorant
   for `J`, together with `10N^2+1<=N^3` and
   `3*2^22*(t+1)<=2t!<K`, supplies its digit bound. The derived index `J` is
   correctly excluded from the aggregate bound on the nine CRT representatives.

5. **Consecutive coordinates are oriented by existing rows.** Every ordinary
   seed has a power or modular residue row `nY=Z+R`, with `R>=0` and `n<A`.
   Together with `Y^2+Z^2-2AYZ=1`, this gives `Y>0` and `AY-Z>0`; the positive
   Pell branch follows. No unconstrained seed conic remains. The full anchor
   correctly keeps ordinary coordinates.

6. **The split Pell scale is sufficient and noncircular.** Its decoded index
   is a positive multiple of `W`, so `A>=L>=X_W(W+1)>=(W+1)^W` before any
   proposed power is interpreted. Its free additive slack leaves `A` available
   for the later linear root congruence. The exponential strength, rather than
   merely `A-1>W^3`, is needed for exact power recovery.

7. **The dominant denominator is established early enough.** The six powers
   are recovered before using the ceiling and endpoint equations. Those rows
   imply `F>=1`, `y>=2`, and `x>=2+(t+1)y`, hence `x>t+1,y+1`. Therefore
   `M=N*q^(x+1)` is divisible by every required digit modulus. Its common-root
   congruence is soluble and admits arbitrarily large bases `A`.

8. **The single exact binomial is decoded before its factorial meaning.** Its
   carry bound follows from the literal `B>=2`, `R`, and `K` definitions. The
   ceiling fixed-point proof then supplies `F=t!`. This order avoids using the
   factorial interpretation to justify its own binomial extraction.

9. **Prime-power range extraction and the Horn-flow endpoint are valid.** The
   binomial divisibility implication used is one-way; its false converse is not
   needed. Precision `2K` in the CRT construction leaves sufficient valuation
   after division by the lower-index factorial. The Horn-flow multiplicity
   argument remains sound in the presence of cycles.

10. **The anchor's oriented congruence quotients need a separate completeness
    argument.** The retained Lean interface supplies modular equalities. The
    report now explicitly proves that its oriented natural quotients exist:
    `H=J>=2` gives `Y_*>=2A`; `C>1` and `C=1 mod 4Y_*` give `C>A`; the residue
    condition for `T` gives `T>=H>=2`; Pell classification at `C` gives
    `T>=2C`, and therefore `S>X_*`. All displayed quotient differences are
    nonnegative. This amendment closes the interface gap without changing the
    equation.

## Independent finite checks

`check_semantics.py` is a standard-library checker written independently of
the producer. It imports no producer code. It expands the monic gate DAG over
exact sparse integer polynomials and checks 92 local identities, all output
incidences, complete frame coverage, the exact-power and modular digit rows,
and the inherited source prefix with its explicitly permitted changes.

Both final semantic graphs passed with normal Python and with `python -O`.
Five separate corruptions were rejected: pooled-coefficient corruption,
anchor auxiliary-norm corruption, wrong modular-pair binding, omission of a
modular frame atom, and alteration of the aggregate coefficient. Receipts are
retained as `final_{sparse,small}_{normal,optimized}_semantic_receipt.json`.

The common raw semantic JSON has SHA-256
`d4366a5256758a703c357f856cad134ca61679de98628c13fbabb37094f6e243`.
This review is complementary to the independent exporter, contraction,
expanded-polynomial, and release-reproduction checks; those are separately
reported by the release checker.

## Logical endpoint and scope

The retained `KEndpoint.c222_iff_zf_refutation` statement occurs before the
later machine hypotheses and contains no machine-bootstrap or tape-coverage
assumption. `ConstructibleChoice.zf_refutation_iff_zfc_refutation` is outside
the model-parameter section. The three copied immediate interface files were
checked byte-for-byte against the pinned Git blobs; the identities are in
`LOGICAL_INTERFACE_IDENTITIES.json`. The direct numerical constructors were
also compared with the inherited Code254 definitions.

The supplied argument is an ordinary mathematical proof, with exact finite
algebra checks, composed with the inherited logical endpoints. This review did
not rebuild or independently audit the complete transitive Lean development.
It does not turn the release into a fresh end-to-end kernel certificate or a
sealed object-language ZFC derivation. The report accurately discloses that
distinction.

## Minor exposition notes

These do not change any equation or invalidate a proof:

- The general range lemma is clearest with explicit assumptions `k>=1` and
  `e>=1`, which hold at its use sites.
- The local-value extraction only needs `p^(Km)>=2^K`, because its value is
  already strictly smaller than `2^K`. Replacing a displayed strict comparison
  by this weak one avoids relying on the unstated oddness of the CRT bases.
- The power-modulus estimate can be made explicit in one line:
  `T_n>=2A-W^2-1`, while `(W+1)^W>2W^W` for `W>=3`; hence
  `T_n>W^W+W`.

