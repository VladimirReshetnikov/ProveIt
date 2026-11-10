import Mathlib.Computability.PartrecCode
import Mathlib.Computability.RE

/-!
# Selection from a recursively enumerable relation

`exists_selector`: for a recursively enumerable relation `R` between a parameter `a` and a number
`y` there is a partial recursive function `f` with `R (a, y)` for every `y ∈ f a`, and with `f a`
defined whenever some `y` has `R (a, y)`.

The selector dovetails. A code `cg` computes the semi-decision procedure of `R`. Stage `k` reads
`k` as a pair `(y, s)`, runs `cg` on the code of `(a, y)` for `s` steps
(`Nat.Partrec.Code.evaln`), and returns `y` if that bounded run halts. `Nat.rfindOpt` takes the
first successful stage.

This module depends on Mathlib only.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open Nat.Partrec.Code Computable

/-- A recursively enumerable relation has a partial recursive selector. -/
theorem exists_selector {α : Type*} [Primcodable α] {R : α × ℕ → Prop} (hR : REPred R) :
    ∃ f : α →. ℕ, Partrec f ∧ (∀ a, ∀ y ∈ f a, R (a, y)) ∧ ∀ a n, R (a, n) → (f a).Dom := by
  obtain ⟨cg, hcg⟩ := exists_code.1 hR
  -- `cg` halts on the code of `p` exactly when `R p`.
  have hdom : ∀ p : α × ℕ, (eval cg (Encodable.encode p)).Dom ↔ R p := fun p => by
    have he : eval cg (Encodable.encode p)
        = (Part.assert (R p) fun _ => Part.some ()).map Encodable.encode := by
      rw [hcg]
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    rw [he]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
  have hrun : Computable fun q : α × ℕ =>
      evaln q.2.unpair.2 cg (Encodable.encode (q.1, q.2.unpair.1)) :=
    primrec_evaln.to_comp.comp (((snd.comp (unpair.comp snd)).pair (const cg)).pair
      (Computable.encode.comp (fst.pair (fst.comp (unpair.comp snd)))))
  have hstage : Computable₂ fun (a : α) (k : ℕ) =>
      (evaln k.unpair.2 cg (Encodable.encode (a, k.unpair.1))).map fun _ => k.unpair.1 :=
    Computable.option_map hrun (fst.comp (unpair.comp (snd.comp fst))).to₂
  refine ⟨_, Partrec.rfindOpt hstage, fun a y hy => ?_, fun a n hn => ?_⟩
  · obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hk
    exact (hdom _).1 (Part.dom_iff_mem.2 ⟨z, evaln_sound hz⟩)
  · obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 ((hdom (a, n)).2 hn)
    obtain ⟨s, hs⟩ := evaln_complete.1 hz
    exact Nat.rfindOpt_dom.2 ⟨Nat.pair n s, n, by
      simp only [Nat.unpair_pair, Option.mem_def.1 hs, Option.map_some, Option.mem_def]⟩

#print axioms exists_selector

end PAFlexibleOutput
