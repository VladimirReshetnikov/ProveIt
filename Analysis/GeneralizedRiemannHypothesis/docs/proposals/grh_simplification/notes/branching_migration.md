# One highest-vector coefficient replaces the extended-tensor norm proof

Target revision: `9050b04000647d588d0c78d945180abcd3b0bcf7`.

This is a secondary local simplification, not a replacement for the main height-first chain proposal. Its mathematical argument is complete at the level below; source integration and source line savings have not been checked by Lean.

## Prior implementation and attribution

The central Gram-adjoint / Schur-lemma / highest-vector argument is **already implemented in the upstream compact edition**. It is not a new proof technique discovered here. The inspected source is:

- Repository: `lsernau/grh-lean`.
- Revision: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- File: `grh-compact/src/Lib/GLn/Branching/Branching.lean`.
- Git blob: `669d2de08c3fa16386120153629ca6cde94e5dde`.
- Theorem: `exists_branching_matrix`, beginning at line 230.
- Lines 244–257 construct the Gram adjoint and use `scalar_of_commute_schur` plus Cauchy–Schwarz to reduce the norm bound to one highest vector.
- Lines 258–261 bound that vector with `weylNormSq_le_mul_of_toPoly_eq`, using the Cartan-product norm inequality.

The recommendation is to **port this shorter argument back to the readable edition**. The fixed unit tensor below is an alternative calibration that isolates a standalone highest-coefficient criterion and avoids invoking the general Cartan-product norm estimate. That extracted criterion does not require the combinatorial `hκ₀` hypothesis. This is a sharpening of the helper interface, not a claim of priority for the Schur argument. The compact existence theorem still needs the weight relation when it constructs the branching matrix.

The compact Cartan calibration is already four lines. Consequently there is no evidence that formalizing the fixed-tensor variant would yield fewer Lean lines than a direct compact-proof port. The substantial source target is the readable edition's extended-tensor detour, not the compact argument.

## Exact target

`New.GL.weylNormSq_mulVec_le_of_equivariant`, in `src/Lib/GLn/Branching/NormBound.lean:656–708`, is called externally only at `src/Lib/GLn/Branching/IntegralMap.lean:516`.

Write

- `V` for the Schur/Weyl module on rows `n` and columns `κ₀`,
- `W` for the module on rows `N` and columns `γ + κ'`,
- `G_V,G_W` for their positive definite Gram matrices,
- `E = fillingMatrixOver ℂ N (γ + κ')`, so `G_W = Eᴴ E`,
- `B : W → V` for the integral matrix in the theorem,
- `v = weylEval n κ₀ (permArray rowEquivFin)`, whose Gram norm is exactly 1,
- `δ(g) = ∏_τ det(g_τ)^{κ'_τ(rank n_τ)}`.

The two substantive hypotheses are

1. `B W(g) = δ(g) V(g) B`, where `W(g)` denotes the block action on `W`;
2. `nablaCombination(vᵀ G_V B) = c branchVector`.

The existing theorem also assumes the combinatorial weight relation `κ₀(h) = κ'(h) + γ(h+1)`. The replacement norm argument does not use that relation: it only uses the displayed equivariance and coefficient hypotheses. The old argument needs it to calculate the extended tensor at all points.

## The replacement argument

Define the Gram adjoint

`D = G_W^{-1} Bᴴ G_V`.

Since `B` and both Gram matrices are integral/real, this is also the transpose Gram adjoint. Existing transpose contravariance gives `S(g)† = S(gᴴ)`. Applying equivariance at `gᴴ` and taking adjoints therefore gives

`W(g) D = δ(g) D V(g)`.

Consequently

`δ(g) V(g) B D = B W(g) D = δ(g) B D V(g)`.

For invertible `g`, `δ(g) ≠ 0`; hence `BD` commutes with every `V(g)`. In particular it commutes with the unitary tuples required by the existing theorem `New.mem_range_scalar_of_commute_schur`. That theorem gives

`B D = λ I_V`.

No additional irreducibility theorem is required. The word “unitary” is used only to match the existing Schur lemma's interface; the commutation identity is already valid for every invertible tuple.

Next define one fixed real tensor, indexed by column fillings,

`w_T = ∏_{τ,h,j} det(I[branchRows(τ,h,j), fillingRows(T,τ,h,j)])`.

Every `branchRows` column is injective, because it is an inverse row enumeration composed with the inclusion of the first `h` positions. The determinant is therefore nonzero for exactly one increasing row set, where it is ±1. Thus `w` is a signed coordinate vector and `‖w‖ = 1`.

A convenient formal proof avoids choosing sorted columns explicitly: apply Cauchy–Binet at the identity separately in every column. The sum of squares of its minors is `det(I[U,U]) = 1` by `Matrix.submatrix_one` for the injective row map `U`. Multiplying these identities gives `∑_T |w_T|² = 1`. Only this single identity tensor is needed; no `extendedTensor(a)` for general `a` is constructed.

Apply `rowSubst_prod_tableauPoly` at `z = 1`, then `branchVector_eq_prod_tableauPoly`, to obtain

`branchVector = ∑_T w_T fillingPoly(T)`.

The existing `nablaCombination_transpose_mulVec` and injectivity of `nablaCombination` turn the highest coefficient hypothesis into the exact row identity

`vᴴ G_V B = c wᴴ E`.

There is no factorial, dimension factor, or sign loss here. The source vector `v` is real, and both `c` and `w` are real. Therefore, for every `x ∈ W`,

`|⟨Dv,x⟩_W| = |⟨v,Bx⟩_V| = |c| |⟨w,Ex⟩| ≤ |c| ‖x‖_W`.

Putting `x = Dv` gives `‖Dv‖_W² ≤ |c| ‖Dv‖_W`, hence `‖Dv‖_W ≤ |c|`. Because `v` has norm 1,

`λ = ⟨v,BDv⟩_V = ‖Dv‖_W²`,

so `λ` is real, nonnegative, and at most `c²`.

Finally, let `q = ‖Bx‖_V²`. Cauchy–Schwarz and `BD = λI` give

`q² = |⟨DBx,x⟩_W|² ≤ ‖DBx‖_W² ‖x‖_W² = λ q ‖x‖_W²`.

If `q = 0`, the target bound is immediate; if `q > 0`, divide by `q`. In both cases

`weylNormSq(Bx) ≤ c² weylNormSq(x)`.

This final step can reuse the source's `posDef_cauchy_schwarz` and elementary real arithmetic, without constructing normed-space instances or using the continuous-linear-map adjoint library.

## Existing source support

| Needed fact | Exact declaration and source |
|---|---|
| Positive Gram form | `New.weylGramOver_posDef`, `Lib/GLn/SchurModule/WeylKernel.lean:440` |
| Tensor isometry | `New.weylGramOver_eq_transpose_mul`, `WeylKernel.lean:418` |
| Transpose contravariance | `New.weylGramOver_mul_schur`, `WeylKernel.lean:458` |
| Base change/conjugation | `New.schur_map`, `Lib/GLn/SchurModule/SchurMatrix.lean:532` |
| Schur commutant is scalar | `New.mem_range_scalar_of_commute_schur`, `WeylKernel.lean:647` |
| Highest vector has norm 1 | `New.GL.weylNormSq_weylEval_permArray`, `Lib/GLn/SchurModule/GramMatrix.lean:428` |
| Gram Cauchy–Schwarz | `New.GL.posDef_cauchy_schwarz`, `GramMatrix.lean:401` |
| Branch vector as column minors | `New.GL.branchVector_eq_prod_tableauPoly`, `NormBound.lean:393` |
| Expansion at the identity | `New.rowSubst_prod_tableauPoly`, `Lib/GLn/SchurModule/TensorModel.lean:156` |
| Coefficients of tensor rows | `New.nablaCombination_fillingMatrixOver`, `TensorModel.lean:200` |
| General tensor coefficient combination | `New.nablaCombination_transpose_mulVec`, `TensorModel.lean:223` |
| Coefficient injectivity | `New.GL.nablaCombination_injective`, `SchurMatrix.lean:341` |

## Replacement region and scope

The 246 physical lines `NormBound.lean:403–648` contain the `extendedTensor` construction and its supporting arbitrary-point determinant/isometry/span argument. The old final theorem body is another 41 lines (`668–708`). The four-line `leadingMinorAlong` definition at `379–382` can also disappear if the auxiliary general calculation is removed. These are gross candidate regions, not a promised net deletion count; scope scaffolding and some comments would be adjusted, and new adjoint and single-tensor lemmas must be added.

A repository-wide text scan found **no external references** to any of the following declarations outside this file:

`extendedTensor`, `leadingMinorAlong`, `newRowOrder_symm_of_val_eq_succAbove`, `leadingMinorAlong_newRowOrder_zero`, `leadingMinorAlong_newRowOrder_top`, `prod_det_blockScalar_branchRows`, `extendedTensor_dotProduct`, `weylEval_dotProduct_weylGram_mulVec_weylEval`, `det_mul_dotProduct_mulVec_eq_extendedTensor`, `span_weylEval_eq_top`, `star_extendedTensor`, and `re_dotProduct_mulVec_le_of_forall_dotProduct_eq`.

Keep `branchRows` and `branchVector_eq_prod_tableauPoly`. Keep the external theorem's statement initially, even though `hκ₀` becomes unused, to avoid call-site churn.

## Nonduplication and remaining work

A scan of the 18 proposal directories' TEX/Markdown sources found no proposal targeting this highest-vector branching estimate or `extendedTensor`. This establishes separation from those proposal bundles, **not novelty relative to the compact edition**, which already contains the central argument as documented above. The existing `gram_adjoint_simplification` instead targets the integral adjoint/tight-frame construction in the one-lift comparison operator, using `GH = hI` and paired-conjugate norms. It does not propose replacing the full branching contraction by a single highest coefficient. The existing CM proposal mentions a different local lemma, `frontPermutation_val`, earlier in this file; that change is compatible.

Remaining Lean work for the fixed-tensor variant is specific: instantiate the positive Gram adjoint, derive the commutant identity, prove the norm of the identity tensor using injective columns, extract the exact coefficient identity, and replay the caller in `IntegralMap`. A direct compact-proof port could instead reuse the readable `weylNormSq_le_mul_of_toPoly_eq` and omit the new identity-tensor calibration. None of these can be silently omitted when claiming an integrated replacement. No whole-file or whole-project Lean replay of this shortcut is claimed.
