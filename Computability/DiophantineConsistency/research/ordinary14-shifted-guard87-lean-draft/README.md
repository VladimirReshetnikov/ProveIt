# Source-only Lean route for the shifted-guard 87/26 graph

This is a literal graph draft and an arbitrary-model proof plan, **not a
compiled Lean result**. The reviewed external calibration establishes a
standard-integer positive-existence comparison, but the modified graph has no
Lean/iPRA endpoint yet. The 88/26 quotient-guarded graph and the 88/30 and
88/46 parent model clients are themselves uncompiled drafts. No PDF or file
semantics, graph-count theorem, provider-closure replay or global minimality
claim is made.

`make_graph.py` pins the 87-row candidate and emits `Expr (Fin 14)` source in
`P87ShiftedGuardGraph.lean`, including a proposed definitional
`output_shape`. Slot 8 (`r`) is sigma-prime and slot 13 is omega. The
`--check` mode reproduces the exact source bytes without invoking Lean.
Parser treatment of `guard`, all elaboration, reduction and resource behavior
are untested.

## The new model statement needed

For `V` an `ORingStructure` whose underlying structure models `IΣ₁`, the
missing result is a **model-wise positive-zero existence equivalence** between
the shifted graph and the quotient-guarded 88 graph, at appropriately cast
compact44 ports. It is not implied by the external standard-integer review.
The proposed proof must use `DiffRing V`, signed pairs or explicit inequalities
for negative intermediate expressions; natural subtraction alone is not ring
subtraction. Exact `Fin 14` maps and all cast/positivity lemmas are new.

In the easy 88→87 direction, a quotient-guarded witness has positive t and
`Bt=b*t`. Set `omega=t+F`; the identity

```
C*(X+K0*q)−F−b*omega = Bt−b*t
```

makes the new guard zero, while the four residuals are definitionally or
algebraically the same. A new graph-evaluation client must prove this in
`DiffRing V` and transfer positivity; it cannot rely merely on the JSON row
comparison.

The reverse direction needs a model proof of `omega>F` for **every** shifted
zero. The reviewed standard-integer argument is a useful blueprint but its
factorizations, valuations and source-theorem applications must be rebuilt as
clients for this graph. Once the inequality is proved, set
`t=omega−F>0`, justify the natural subtraction/cast equality, and transfer
all residuals and the zero guard. The 88/26 model bridge to the 13-coordinate
parent remains separately unfinished.

## Fact-level decoder and exact reusable sources

A plausible staged model route is:

1. From the five squares and positive inputs derive the guard equality,
   `C>0` and `F+alpha<q`, independently of Bt's sign. Promote C and R from
   signed ring expressions to natural model elements only after the required
   order bounds. `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`
   applies once its positive beta,J,F,alpha, port-mask bounds, q equation and
   gap hypotheses are constructed. A new elementary lower-bound client must
   strengthen its `24<=R` to `R>=26` for the later theorem.
2. Extract first/main roots and `q³|Y` from this graph's residuals. In an
   arbitrary model `ArithmeticAdaptiveQuotients2011.scaled_quotient` uses
   `ArithmeticSquareDivisibility.dvd_of_square_dvd` internally for a
   **natural nonnegative magnitude** and positive scale. The standard ℤ
   prime-valuation argument does not directly justify the model statement.
   `ArithmeticSignedPairs.magnitude`, `P72Root.ι_magnitude_sq` and
   `FreeJRootBinding` illustrate signed-pair techniques, but their
   graph-specific representations need new adaptations. A separate proof
   must orient the main signed root positively using the gap and the bound
   `U*a*c>H*k`; it must not assume the old first input positive.
3. Classify the first and main natural Pell roots using
   `ArithmeticPellFirstNorm.positive_parameter_solution` and
   `ArithmeticPellClassification.solution_index`, then obtain the index
   congruence. `ArithmeticAdaptiveFactorThree2011.cancel_factor_three`
   proves the internal loss of at most one q factor **even if 3 divides q**:
   from q³|Y and q⁵|H*z it obtains q⁴|z. A new signed-magnitude carrier
   client must supply the exact q⁵ premise and derive the q⁴ residue. The
   uncompiled probe is not an input to `FreeJMainOrientation.rank_congruence`
   or `FreeJEarlyIndex.early_index`; those old-literal wrappers must not be
   called as though they were generic shifted-graph theorems.
4. The existing fact-level `P72Exact.indices_ordinary` permits **any** μ
   satisfying its explicit window and residue. Instantiate μ=q⁴ only after
   proving all its other inputs: positive q,X,y0,eta,i,f; Y=q³y0;
   c=eta+Yk; the first and main Pell-index equations; R>=26; the ordinary
   strong and auxiliary norm equations; and the q⁴ window/congruence.
   The correct strong input is **i_prime=i**, since the graph gives
   `(i*c²)²=Delta*(f²−1)`; using Delta*i would introduce an extra factor.
   The two `absdiff` terms in the theorem need explicit model bridges to
   the signed V and V+u squares. Model casts and all theorem arguments remain
   unelaborated obligations.
5. Replay the fact-level carrier algebra behind
   `FreeJPowerProjection.graph_projection` to get q|3X, then derive X>=16
   from the compact beta bound. `ArithmeticPellPowerRecovery.power_bound`
   gives `2^R<Y` after the exact indices and its explicit eta/zeta, Pell and
   size hypotheses. Reconstruct the three-multiplier projection from
   `FreeJPowerFinish.graph_power` using
   `ArithmeticPellPowerRecovery.projection_quotient`, obtaining X=2^R;
   then the scalar rank lower bound yields X>=q² and Bt>0. The old FreeJ
   **wrappers** call `freej_first_factor_transport` and require the old
   positive literal zero; they cannot simply be imported for the shifted
   input. The new fact-level proof has not been elaborated or checked.

## Ports and endpoint

The standard-integer equivalence uses compact44 beta positivity, mask bounds,
K0>=0 and, through the quotient-guarded parent→guarded map,
`K0<(beta+1)²`. `CompactFixedBeta.beta_identity` and
`CompactFixedBeta.bounds` are source ingredients for the beta/mask facts;
`CompactCellProductBound.symbolic_kernel_lt` and exponential monotonicity
can support a new internal kernel bound. The precise symbolic-to-port casts,
including nonnegative integer-port representations, remain to be proved.
The byte association is external; no theorem reads a JSON or PDF file.

Only after a checked equivalence for every required IΣ₁ model may this graph
be composed through the unfinished quotient-guarded/88/30 clients and the
existing `FreeJ13Halt.positive_model_iff` / iPRA adapters. A generator check
is not a Lean preflight: any future run requires independently reviewed
provider/companion routes, compatibility and resource guards, and an
exclusive Lean allocation.

```
python3 -I -S -B research/ordinary14-shifted-guard87-lean-draft/make_graph.py --check
```

Independent source review is recorded in
`../../reviews/ordinary14-shifted-guard87-lean-draft-independent/`.
