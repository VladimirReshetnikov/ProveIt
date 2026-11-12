# Fact-level early index for the actual 13/82 residue root

The first Pell index and its q⁴ congruence can be obtained from the **actual residue-adjusted first root**, without proving that it equals or has the magnitude of the original free-J `core.z`. This is a source-interface and arithmetic analysis, not an elaborated Lean theorem or a completed 82-to-84 model bridge.

Write `b=J*beta>0`, `q=1+b`, `Y=q³*s`, `Q=X*Y²>0`, `k=eta+zeta`, and let `Z82` be the signed first root of the 82 graph. Its actual residual is

```text
Z82² = b² * (1 + Q*(Q+1)*k²).
```

The proposed `Residue90GraphNormsDraft.first_ring_norm` and `Residue90SignedNormsDraft.first_natural_norm` are an available source-only extraction route. For a positive 82 valuation, the proposed `Residue90To82TransportDraft.mixed_lower` and `zero_iff` reduce the graph binding to its 90 literal; these declarations and the norm/quotient sources have not been elaborated. A direct 82 extraction is another option. The quotient step supplies **this graph's** natural `tau` with `tau²=1+Q*(Q+1)*k²`. It requires the actual signed norm and positive represented b, not any old-root identity.

## Source recurrence and early residue

`ArithmeticPellFirstNorm.positive_parameter_solution Q tau k` requires only `Q>0` and that natural norm; it yields model-natural `n<=k`, `xcoord n B=tau` and `2*ycoord n B=k`, with `B=2*(Q-1)+1`. Since `Q>0`, `B+1=2Q`. From `Y=q³*s`,

```text
2Q = q⁴ * (2*X*q²*s²).
```

Applying `ArithmeticPellCongruences.residue_quotients n B (q⁴)` gives `ycoord n B=n+q⁴*t`, so `k=2*n+q⁴*(2*t)`. Separately, applying the same recurrence theorem with modulus `2Q` gives the exact form `k=2*n+4*Q*w` needed by `P72Exact.indices_ordinary`.

Suppose the actual main-root argument supplies `q⁴ | magnitude(R+1,k)` and the rank window supplies `R+1<q⁴`. `ArithmeticAdaptiveFirstDivisibility2011.magnitude_mod` then gives `(R+1)%q⁴=k%q⁴`; the preceding quotient gives `(2*n)%q⁴=R+1`, hence `R+1<=2*n` and `R+1<=k`. If also `24<=R`, `13<=n` follows. None of these steps inspects `core.z` or assumes exact `2*n=R+1`.

The existing `FreeJEarlyIndex.early_index_of_facts` cannot simply be invoked: both its input `FreeJPellIndices.FreeJIndices` **and its result** require `magnitude(pairEval (core ...).z v)=M*first`, where M is the original free-J scale. Reusing its recurrence/modular proof in a smaller fact-level client avoids this extra assumption. The separate `ArithmeticAdaptiveEarlyIndex2011.early_index_of_facts` likewise bundles its own original expression root. The independently reviewed first-index toy control satisfies the early q⁴ congruence but has `2*n=R+1+q⁴` and a nonzero complete output; early congruence alone does not produce the later exact index.

## Actual main root and later hypotheses

The graph's main shift contains the essential extra `X*Y*q` term. Put `U=Y*q²`, `a=X*Y+Y`, `c=eta+Y*k`, `H=3+4*a`, and let `R` be the represented natural rank. The signed main expression is

```text
Dstar = U*(X+a*c) + H*(U*gamma + X*Y*q + R+1-k).
```

After proving `F+alpha<q` so that the natural truncated rank equals the signed graph rank, the unelaborated `Residue90XZeroGraphDraft.main_ring_norm` supplies its squared norm for arbitrary gamma. `Residue90SignedNormsDraft.main_pair_norm` proposes the signed-to-natural magnitude conversion. `DirectMainNorm.direct_main_orientation` can be instantiated with its rank argument `R'=R+X*Y*q`, plus U>0, Y>=8 and k>0; it then supplies an oriented positive main quotient and balance. Using `Y=q³*s`, that balance is exactly the explicit arithmetic premise `FreeJMainOrientation.FreeJMainCongruence`, whose `rank_congruence_from_main` is fact-level and concludes the q⁴ magnitude divisibility. This requires constructing the correct 12-coordinate FreeJ *arithmetic* tuple, not a FreeJ zero:

```text
FreeJ index:  0  1  2      3  4  5  6  7  8    9     10 11
value:        J  F  alpha  f  i  X  Y  T  eta  zeta  y  gamma
```

The original 82 input s is used to define Y, and its r coordinate does not occur in this arithmetic tuple. The actual rank is `((q-1)*(q-F)+alpha)*(q²-1)+(MC+q*MF)*J`; cast/truncated-subtraction compatibility and the compact port bounds are separate graph/provider obligations. The literal `first_ring_norm`, `main_ring_norm`, signed norm client, positive C/gap and 90↔82 source transport are unelaborated proposals; their source signatures are pinned, not certified as compiled dependencies.

To go beyond the early congruence, classify the positive main norm with `ArithmeticPellClassification.solution_index`; use the strong residual with the actual graph i and obtain a positive old auxiliary offset u from the direct y and **signed** ordinate. The proposed `AuxRootModelDraft.positive_aux_coordinate_iff` explicitly requires `1<Qstrong` and `1<ordinate²`; `AuxNormsToBoundsDraft.aux_bounds_of_natural_norms` proposes these from explicit first/main/strong norms and signed bindings, but is itself unelaborated and needs graph-specific adaptation. `P72Exact.indices_ordinary` then needs its full listed main-index, strong, auxiliary, q³-scale, rank and positivity premises; in particular it asks for `R>=26`, stronger than the generic window's `R>=24`. Under q>=3 and the positive-C gap, one possible separate derivation uses `R>=(2q-1)(q²-1)>=q³>=27`; it is not supplied by the 24-bound alone.

Even the exact-index conclusion is not yet the desired carrier bound. `P72Exact.exact_ordinary` additionally requires `Bez q H 1`; it must not be invoked with that hypothesis silently assumed for arbitrary compact q. The sign-free calibration instead describes a separate main-balance route to `q | 3*X`, `X>=16`, `ArithmeticPellPowerRecovery.power_bound` and `projection_quotient`, then `X=2^R>=q²`. Those graph-specific algebra, order, auxiliary and provider steps have not been composed in Lean. Only then does `C>=1`, `F<=q-2`, K0>=0 give the sufficient companion bound `B>=2q>0`; a full all-model 82↔84 graph transfer and all later parent/endpoint/port bindings still remain.

The checker pins the named source snapshots and the critical direct-vs-bundled interfaces, verifies the q⁴ divisor algebra on bounded controls and checks the toy early-index distinction. It does not prove an arbitrary-model statement, execute Lean or authenticate source/object ancestry.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue82-first-index-interface-audit/check.py | cmp - reviews/ordinary13-residue82-first-index-interface-audit/result.json
```
