# Independent review of the complete74 nonlinear index scout

**PASS for the stated source-only result.** The three emitted circuits are exact full-polynomial graph projections of their authenticated complete74 parents. The comparison schedules still cost74; their complete SOS schedules cost127,103,97. Removing the positive coordinate `r` has not been justified as a positive-domain equivalence, and the scout correctly makes no new universal operation or witness claim.

This review covers the frozen [author source](complete74_nonlinear_index_projection_scout.py), [receipt](complete74_nonlinear_index_projection_scout.json) and [note](complete74_nonlinear_index_projection_scout.md). Their SHA256 pins, all five immediate source/proof pins, and this reviewer's source hash are recorded in the [independent receipt](review_complete74_nonlinear_index_projection.json). The [independent helper](review_complete74_nonlinear_index_projection.py) imports no author or historical Python module. It reconstructs the circuits directly from the pinned [complete74 parent receipt](complete74_factored_first_norm.json).

## Complete source and exact graph proof

In all three literal parents, the only source consumers of supplied `r` are `r1=r+1` and `H17=jc-r`; its only direct comparison consumer is `r=r_lhs`. The private `r1` feeds `R11=r1+hpm1`, used only by the index comparison. The paid gate `hpm1=h*UM` stays. Actual k is supplied `k` in `raw30` and computed `R10b=eta+zeta` in the other two modes.

The independent reconstruction removes `r1,R11`, inserts `index_partial=actual_k-hpm1` and `restored_r=index_partial-1`, and redirects both the packing comparison and `H17`. It removes exactly the index comparison and the supplied coordinate `r`. Two additions become two subtractions. Every retained gate, coordinate, fixed numeral port, comparison and complete finalizer is checked; all paid gates and supplied coordinates remain live.

| Mode | Witnesses | Comparisons | Comparison schedule | Complete SOS | Exact degree |
|---|---:|---:|---:|---:|---:|
| raw30 | 29 | 18 | 40M+34A=74 | 58M+69A=127 | 52 |
| positive22 | 21 | 10 | 40M+34A=74 | 50M+53A=103 | 84 |
| signed20 | 19 | 8 | 40M+34A=74 | 48M+49A=97 | 84 |

The intended supplied-coordinate domain is strictly positive in all three modes; the name `signed20` does not permit arbitrary signed supplied witnesses in its inherited universal theorem. The complete SOS cost is `74+3e-1`, including all residual subtractions, squares and final additions.

Writing `R=K-hE-1`, an independent coefficient calculation proves `R+1+hE=K` and the retained auxiliary argument `jc-R`. Structural induction through all72 common registers proves every retained comparison after substitution. Reconstructing both complete SOS finalizers then gives the polynomial identity

\[
F_{\rm child}(v)=F_{\rm parent}(v,r=K(v)-hE(v)-1).
\]

This is an all-value identity over every commutative ring. It is stronger than checking sampled outputs. For unrestricted integer zero sets, the SOS property forces the old index residual to vanish, so coordinate deletion and restoration give inverse zero-set maps. An arbitrary-ring zero-set bijection is not claimed.

## Positive inverse remains an obligation

A positive parent zero projects to a positive child zero. A positive child zero lifts to a positive parent zero exactly when `actual_k>h*UM+1`. Thus the proved positive bijection is restricted to that child slice; the note does not certify the inequality for all positive child zeros.

I checked the relevant use of positive `R` in the pinned [signed projection proof](complete75_signed_projection_elimination101.md) and [half-binomial compiler](complete75_half_binomial_compiler.md). With `MF_native=MF_source-(B-1)`, the packing remainder is

\[
T'=MCJ+1+q(MF_{\rm native}J-1),\qquad
R=(q^2-S')(q^2-1)+T',\quad S'=Z+qF-1.
\]

The valid mask bounds give `0<T'<q²-1`. They exclude `R=0`, but not the negative representative obtained at `S'=q²+1`. The old positive-R hypothesis is used before deriving its packing and index bounds; importing those conclusions to prove new positivity would be circular. The helper separately checks the translation between the native mask and paid shifted mask.

The saved negative-inverse assignments have nonzero full output. The negative remainder examples are partial algebraic assignments. Neither is a full positive child zero or an authenticated false acceptance. They establish no impossibility theorem. The unresolved question is whether all retained equations force the strict inequality, or whether a genuine full counterexample exists.

## Independent degree proof

Fixed compiler numerals have degree0; ordinary input and retained supplied witnesses have degree1. In the raw form, restored r and `H17` have degree9, making the changed auxiliary residual at most24. The unchanged first residual uniquely reaches26, so the full degree is52 with leader

`w^4*s^8*k^4*q^36`.

In either projected form, the changed auxiliary residual is at most40. The helper verifies every literal producer in the retained input norm, where `a` has degree8, `H=4a+3` has degree8 and `κ=odd_index+delta*(a²+H)` has degree17. Expanding its residual gives

\[
W^2+2aW\kappa+2\rho WH+2a\rho\kappa H+
\rho^2H^2-H\kappa^2-1.
\]

The term degrees are `2,26,10,34,18,42,0`; the unique leader is `-4delta²*a⁵`. Every other residual has degree below42. Squaring gives the unique full leader

`16*Bm1^60*delta^4*w^10*s^10*Jrep^60`,

which is nonzero at every actual `Bm1>0`, proving exact84 uniformly. This argument uses the actual source cones and algebraic cancellation, not the naive unexpanded upper100 or numerical degree samples.

## Reproducible bounded evidence

The independent receipt records three complete source/finalizer reconstructions,216 common-register transfers,36 retained residual transfers, three full graph identities and327 live paid full gates. Additional execution checks cover60 complete tuples, including12 rational tuples, and720 retained residual values. Three negative inverse diagnostics are explicitly off-zero.

```sh
python3 review_complete74_nonlinear_index_projection.py \
  --root /path/to/native-stream-queue \
  --artifacts /path/to/author-trio \
  --expect review_complete74_nonlinear_index_projection.json
```

The writer and a fresh exact typed saved-receipt replay from `/` pass. This is a bounded source/proof review, not a maintained hostile-packet API audit, a historical suite rerun, or a search over other nonlinear substitutions. No author correction was requested. The established universal74 and universal86 bounds remain unchanged.
