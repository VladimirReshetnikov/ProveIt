# Additional independently reviewed round-5 candidates

Same immutable source pin and **uncompiled/source-only** status as `REVIEW.md`.

## WangTiles942PhysicalOrder.strictMono_fin_eq_self — EXCLUDED

**Correct at source level, but EXCLUDED as an exact duplicate.** The closing proposal scan at `91dce223cda86c0755b8a9b2504f84be04443fce` found `2026-10-26zh/report/03-physical.tex:1–18`, which supplies this exact `OrderIso`/`Equiv.ofBijective`/`Fin.coe_orderIso_apply` construction and the same 180 → 156 metric. `2026-10-26zj/report.tex:82–113` also proposes a shorter finite monotone-map rigidity route. Both are assumed applied; none of this candidate’s 24 saved lines is new. Copies are under `../baseline_audit/closing_sources/`. The following correctness review is retained only as comparison evidence.

Full source module 180 → 156, net 24 lines. The theorem declaration goes from 30 to 6 physical lines. No import is added.

The constructor and application types align:
1. `hf.injective` plus `Finite.surjective_of_injective hf.injective` gives `Function.Bijective f`, exactly as already used in the old argument.
2. `Equiv.ofBijective f ...` has `toFun := f` (`Logic_Equiv_Defs.lean:820–826`). Its coercion to a function is definitionally `f`, with `coe_ofBijective := rfl` explicitly present.
3. `OrderIso` is an abbreviation of `RelIso (≤) (≤)` (`Order_Hom_Basic.lean:105–106`). `RelIso` extends an `Equiv` and requires `∀ {a b}, e a ≤ e b ↔ a ≤ b` (`Order_RelIso_Basic.lean:558–560`). `hf.le_iff_le` has precisely this type (`Order_Monotone_Basic.lean:368–369`). The positional structure constructor is therefore appropriate.
4. `Fin.coe_orderIso_apply e i` states that the natural value of `e i` equals the natural value of `i` (`FinBasic.lean:396–405`); `Fin.ext` lifts that equality to `e i = i`, definitionally the goal `f i = i`.
5. `WangTiles942PhysicalOrder` imports `WangTiles942PhysicalData`, which already imports `Mathlib.Order.Fin.Basic` at line 2. No new Mathlib import is necessary.

All map/data definitions and downstream applications are untouched. The generic `n = 0` case is covered: the theorem takes an `i : Fin n`, so no inhabitance premise is added. No new computational inverse is introduced into the physical-map definitions; the constructed isomorphism is local to a proof.

**Choice caveat:** `Equiv.ofBijective` is noncomputable and constructs an inverse using `surjInv`. Using it within a theorem does not require making an executable definition noncomputable, nor a separate `classical` command merely to reference the constant. Nonetheless this source review does **not** establish equality of old/new axiom sets. The original proof also uses finite surjectivity, but that alone is not evidence of axiom parity. Require `#print axioms` in later authorized validation.

Pinned Mathlib evidence is at `../mathlib_evidence`; the independently rechecked FinBasic and EquivDefs SHA-256/Git blob bindings match revision `81a5d257c8e410db227a6665ed08f64fea08e997`, also pinned in `lake-manifest.json`. See `structural_check.json`.

## CurrentPowerCoordinates2011 order-zero endpoints

**Accept at source level, with dependency tradeoff noted.** Full source module 105 → 102, net 3 lines across two proof bodies. No import, helper, public statement, representation, controller constant, or definition changes.

- `CurrentAuxiliaryOrder2011.generator_order_succ 0` has conclusion
  `orderOf ((B : ZMod (auxiliary^(0+1)))^(auxiliary-1)) = auxiliary^0`.
  The given `simp only [Nat.zero_add, pow_one, pow_zero]` reduces this to the required order-one proposition. `orderOf_eq_one_iff.mp` then yields the existing auxiliary endpoint.
- `full_order 0` makes the identical specialization at modulus `d * auxiliary`; the same simplification yields the order-one proposition for `generator_cast_C0`.
- `orderOf_eq_one_iff.mp` is already used in the pinned module's `generator_cast_fixed` and original `generator_cast_C0`, anchoring the precise interface without introducing an unverified API guess.
- No dependency cycle is created. `generator_order_succ` is defined in an imported file (`CurrentAuxiliaryOrder2011.lean:52–55`) using `PrimePowerOrder.order_succ`; it cannot depend on the later importing module's endpoints. `full_order` is declared before `generator_cast_C0` and depends only on `generator_cast_fixed`, the coprimality theorem, and `generator_order_succ`; it does not use `generator_cast_auxiliary`.
- The local irreducibility setting on the large constant `B` remains; only exponents/modulus expressions at index zero are simplified, not the huge base.

**Tradeoff:** The auxiliary endpoint now depends on a stronger exact-order family, whose proof includes the nontrivial prime-square lift, instead of using only the prime congruence. The complete module already uses that family. This is legitimate reuse and a small maintenance reduction, **not** a claim of smaller theorem dependencies, less trust, or faster elaboration/kernel checking.

## Structural receipt

`check_sources.py` regenerates `structural_check.json`. It independently matches all four original files to the frozen source manifest/Git blob identities, verifies six theorem statements unchanged, records exact proof-only regions, and verifies two pinned Mathlib source identities. The four reviewed source deltas total 33 lines, but 24 belong to the now-excluded exact PhysicalOrder duplicate. The final closing screen retained the other three files, so the eligible new reduction is **9 lines**. The baseline reviewer read the seven newly substantive reports plus 37 pointers/notes at `91dce223cda86c0755b8a9b2504f84be04443fce`. None of the prior Sidon savings is reclaimed. Count full files, not isolated snippets.

None of these checks compile Lean. Candidate source, axioms, tactics, and performance remain unexecuted.
