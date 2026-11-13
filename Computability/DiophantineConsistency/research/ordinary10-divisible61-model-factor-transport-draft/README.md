# Proposed IΣ₁-model factor transport for 9/64 ↔ 10/61

`Divisible61ModelFactors.lean.src` is an **unelaborated, fact-level source proposal**, not a graph-zero equivalence or a proof-object in iPRA. It isolates the two arithmetic pieces of the standard-integer witness maps in an arbitrary `V` carrying the repository's `ORingStructure` and IΣ₁-model assumptions. Signed graph expressions live in `DiffRing V`; b, ell, k, h, tau and r are model naturals.

The proposed `normalized_first_of_signed` assumes a positive natural scale b, a **positive signed carrier B**, the actual signed-root form `z=ι b*Q−B`, and its first scaled norm. It proposes to use `ModelRelationCombining.sq_dvd_sq` twice: first to extract a signed quotient of z, then the root form to make B divisible by b. Positivity of B and b makes the carrier quotient a positive signed element; `ModelDifferenceRing.nonneg_iff` represents it by a model-natural h. A sign split represents the absolute value of the first quotient by a model-natural tau, yielding the normalized first norm. The source does not silently assert B>0 or extract the hypotheses from a graph.

The proposed `reconstructed_first_root` takes positive b,h and the model-natural normalized norm. It derives `tau>ell` using order and an explicit square comparison, and constructs

```text
r = (tau−ell) + k*(b*h−1) + h.
```

The subtractions are **model-natural truncated subtraction**, used only after establishing `ell≤tau` and `1≤b*h`; `P72Root.ι_tsub` then casts them to the signed difference-ring expression. The resulting polynomial identity is the old first root `z=b*tau`. This is the fact-level reverse construction, not yet a valuation map between two literals.

## Additional graph and model obligations

* Both exact 9/64 and 10/61 literals must be provided and bound to their actual signed first/main residuals and valuation slots. The sum-of-squares zero must supply each residual equation in the model difference ring. Their main expression must be shown identical under the maps.
* J>0, positive b and positive C/B must be derived from each graph's actual first residual or carrier constraint, shifted F/alpha and the represented natural port hypotheses `beta>0,K0>0`. The forward source theorem keeps B>0 explicit. The standard-integer proof uses the old negative-C first-root contradiction and the new `B=b*h≥0` constraint; these require model-order/cast proofs.
* X>0 must be bound to the **actual** main-root and norm expressions. The separate unelaborated `Residue90XZeroArithmeticDraft.xzero_impossible` already gives a promising signed-ring factor-level route for `q≥2`, `Y≥q³`, and its exact shape/norm premises. Its cancellation uses `ModelRelationCombining.sq_dvd_sq` and `Trace75IntegralTransport.natural_dvd_of_signed`; the new graph bindings and source/provider compatibility remain open. J>0 and represented beta>0 would supply q≥2 before that call.
* `ArithmeticAdaptiveQuotients2011.scaled_quotient` is another existing model-natural square-divisibility interface, provided the signed root is first converted to its natural magnitude with the exact equality preserved. No such conversion is assumed by the graph maps here.
* Fixed compact port casts, selection of coherent source/object providers, tactic elaboration, `#print axioms` output and proof replay are all pending. The actual statements are only proposed under IΣ₁-model assumptions; they do not show that a proof exists in the target iPRA, nor establish the missing reverse bridge to the original 85-parent or an equivalence with Con(ZFC).

The checker pins the proposed source, both graphs and the cited direct source interfaces, checks declarations and runs bounded first-norm arithmetic controls. It is not a Lean parser, type checker, graph-proof or provider audit.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-divisible61-model-factor-transport-draft/check.py | cmp - research/ordinary10-divisible61-model-factor-transport-draft/receipt.json
```
