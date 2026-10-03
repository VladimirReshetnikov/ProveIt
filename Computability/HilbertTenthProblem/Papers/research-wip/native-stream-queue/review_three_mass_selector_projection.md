# Independent review: natural selector projection

PASS for the frozen `three_mass_selector_projection.py` source SHA256 `8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8` and author receipt `c5e8e5c8b0fd5490b4758c892408a6415b1e1fb97718722ba72764942f77d4ef`. I read the complete source and companion note, independently derived the general zero-fiber proof, and checked all 252 emitted candidate forms across the 38 actual native/compact-clean certificates. No change requested.

The parent is the already reviewed complete mass-coordinate emitter, SHA256 `d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0`. Its original archive and producer pins are carried into the independent receipt. This review concerns the selector projection as a separate stage; it does not assume a new endpoint-penalty rewrite has also been applied.

## Mathematical audit

At a nonempty step, fix the omitted branch `k` at compilation and write `S=sum_(j!=k)e_j`. All retained selectors and all masses are natural. The actual replacement polynomial is

`G = S(S-1) + sum_(j!=k)(1-e_j)^2 v_j + S v_k`.

Every summand is nonnegative on the complete natural orthant: in particular `S(S-1)>=0` uses integrality. If G vanishes, `S=0` or `S=1`. When S=0, all retained selectors vanish and G forces all their masses to vanish; the missing selector is restored to one and its mass is unrestricted. When S=1, one retained selector is one, all other retained selectors vanish, the missing selector is zero, and G forces exactly all the inactive masses to vanish. Conversely each natural one-hot selector tuple with inactive masses zero projects to G=0. Thus the restoration `e_k=1-S` is unique and natural at every new zero, without presupposing a legal source execution.

The retained affine squares are precisely the old rows under this substitution. Hence the new full natural zeros biject with the complete natural zeros of the mass-coordinate parent, and the previously proved mass restoration `u=v-e` then bijects with the original natural certificate zeros. No positive or natural inverse is claimed on arbitrary supplied tuples. The input/value/time coordinates are unchanged. This proof also applies to the compact-clean certificate because its extra affine bridge/clock/end rows are retained under exactly the same substitution.

For `B=1`, S and G are identically zero and the unique omitted selector restores to one. For `B=0` nothing is omitted, and at positive horizon the original one-hot `(-1)^2` row remains. For `h=0` nothing is projected and original endpoint/halt conditions remain. Fixed compilation choices may differ between steps. These are structural facts of the transformation, not exceptions requiring a valid preselected execution.

As a formal polynomial identity, after restoration the old total selector is exactly one, and the old inactive expression is `sum_(j!=k)(1-e_j)v_j+S v_k`. Therefore

`F_new = F_mass(restored tuple) + sum_t[S_t(S_t-1)+sum_(j!=k_t)e_tj(e_tj-1)v_tj]`.

This holds over the integers and rationals, indeed as an identity with integer coefficients. It is not an off-zero equality to the parent. The direct, factored, and two-branch Horner schedules all expand to the displayed G. The Horner schedule `(1-e)((1-e)v-e)+e v_k` costs three multiplications and three additions before whole-source reuse. The factored intermediate `S-1+v_k` need not be nonnegative; the expanded complete penalty is what proves soundness.

If `B>=2` and `h>=1`, each retained explicit branch contributes the monomial `e_j^2 v_j` with coefficient +1. The affine residual squares have degree at most two, and separate time/branch witness names prevent cancellation of these cubic monomials. Thus the full degree is exactly three. In the tested endpoint-bearing boundary cases without such a pair it is exactly two. Nonnegative-real or arbitrary signed-witness zero equivalence is not asserted.

The recorded actual one-step `INC2;DEC2` counterfeit is correct. With `x=4,e_0_0=2,v_0_0=5,v_0_1=0,y=10,T=1508`, the reconstructed missing selector is -1. Direct expansion of every original source row gives the naïvely substituted parent value 0; the new correction is 12 and the new polynomial is 12. Thus the proof really needs the new nonnegative guard, rather than simply deleting the selector and its one-hot row.

## Complete source and paid counts

The independent checker implements its own sparse coefficient algebra and gate interpreter. It does not call the candidate's `expected`, `projected_form`, `restore`, `verify`, or parent polynomial/evaluation routines. It constructs the original exporter fixtures independently, expands `u=v-e` and the omitted selectors directly in every actual certificate square/product, and compares both the complete correction identity and each emitted retained-row/step-penalty port. It verifies exact integer literals, topological closure, fresh register names, every charged gate's liveness, the paid `N0=x+1` loader, all output summations, and witness-coordinate deletion.

Every binary `+`, `-`, and `*` in the complete live source is charged, including fixed coefficients, all state/value/time/endpoint rows, squaring, and final summation. No precomputed value from the baseline emitter is fed into the candidate. I separately recounted all 76 actual parent direct/factored schedules and compared their saved ledgers. The parent received an independent complete-polynomial review previously; this new review expands every projected candidate from the original certificate itself.

| Source and fixed horizon | Best emitted parent | New M | New A | New total | Natural core witnesses |
|---|---:|---:|---:|---:|---:|
| INC2;DEC2, h=2, native y,T |56|18|29|47|6, formerly8|
| INC2;DEC2, h=2, compact-clean T |56|19|27|46|6, formerly8|
| Three INC2, h=3, native y,T |107|28|63|91|15, formerly18|
| Three INC2, h=3, compact-clean T |105|28|60|88|15, formerly18|
| Prime-three zero test, h=1, native y,T |30|9|15|24|3, formerly4|
| Empty already-halted source, h=0, compact-clean T |5|2|3|5|0|

These minima are only over the emitted gate schedules and uniform implicit-branch choices. They are neither unrestricted circuit optima nor a claim that a per-step branch-choice search has been exhausted. The declared witness formula is `(2B-1)h` when B is nonzero, and zero when B=0. Every new variable list has exactly that many witness coordinates besides its unchanged named input and endpoints.

## Bounded validation and interface scope

Independent receipt totals:

- 252 complete coefficient identities with the full correction; 1,680 retained affine rows; 516 entire cubic step penalties; 18,847 live paid gates.
- 76 actual parent gate recounts.
- 24 additional complete identities using alternating per-step omitted selectors and separately scaled native/compact-clean clocks.
- 9,534 local natural cases over all implicit positions for B=1,...,4, with 90 zeros matching the exact restored one-hot/inactive-mass condition.
- 3,066 complete natural supplied tuples with actual affine endpoints, including seven zeros; every zero has natural restored selectors and original offsets and zero parent score.
- Seven invalid implicit-layout rejections and five unsupported actual exporter-interface rejections.
- Independent full-source evaluation of the naïve counterexample above.

The local census and finite complete-tuple checks supplement the proof; they do not prove the quantified natural-zero theorem by exhaustion. No original author suite was rerun. Fresh independent `--expect` replay passed.

The implementation deliberately inherits the parent prototype's fresh authenticated certificate contract: free raw input named x, native free output/time y,T or compact-clean free time T. It is not a hostile packet validator, an unrestricted hygienic compiler, or a promised natural restoration on off-zero data. The branch table and horizon remain external parameters. The raw number's valuation interpretation is not an ordinary-counter input decoder. Neither a fixed-arity unbounded history nor an improvement to the global universal-polynomial bound follows from these finite-horizon counts. The author note states those limitations accurately.

The helper has explicit paths and authenticates candidate, parent, and author receipt bytes before executing sources. It imports pinned bytes through `compile`, not cached bytecode, and obtains the unchanged original producers through the pinned parent archive loader. Its saved receipt comparison is exact and type-sensitive. It modifies only the requested output file and temporary producer context.

```sh
python review_three_mass_selector_projection.py \
  --source three_mass_selector_projection.py \
  --receipt three_mass_selector_projection.json \
  --root /path/to/native-stream-queue --repo /path/to/Proofs \
  --output /tmp/selector-projection-review.json \
  --expect review_three_mass_selector_projection.json
```
