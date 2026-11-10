import Mathlib.Computability.PartrecCode
import Mathlib.Computability.RE

/-!
# Effective search through a recursively enumerable relation

For a recursively enumerable relation `R` between program codes and outputs,
`exists_search` gives a partial recursive `search : Code → ℕ →. ℕ` that ignores its second
argument, returns only outputs `y` with `R (c, y)`, and returns some output whenever one
exists.

The search dovetails. A code `cg` computes the semi-decision procedure of `R`. Stage `k` of
`search c` reads `k` as a pair `(y, s)`, runs `cg` on the code of `(c, y)` for `s` steps
(`Nat.Partrec.Code.evaln`), and returns `y` if that bounded run halts. `Nat.rfindOpt` takes the
first successful stage.

This module depends on Mathlib only.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open Nat.Partrec Nat.Partrec.Code Computable

/-- Stage `k = (y, s)` of the search for `c`: output `y` if the semi-decision procedure `cg`
accepts `(c, y)` within `s` steps. -/
def searchStage (cg : Code) (c : Code) (k : ℕ) : Option ℕ :=
  (evaln k.unpair.2 cg (Encodable.encode (c, k.unpair.1))).map fun _ => k.unpair.1

/-- The search: the output of the first successful stage. The second argument is ignored. -/
def searchWith (cg : Code) (c : Code) (_ : ℕ) : Part ℕ :=
  Nat.rfindOpt (searchStage cg c)

theorem searchStage_computable (cg : Code) :
    Computable₂ fun (p : Code × ℕ) (k : ℕ) => searchStage cg p.1 k := by
  have hev : Computable fun q : (Code × ℕ) × ℕ =>
      evaln q.2.unpair.2 cg (Encodable.encode (q.1.1, q.2.unpair.1)) :=
    primrec_evaln.to_comp.comp
      (((snd.comp (unpair.comp snd)).pair (const cg)).pair
        (Computable.encode.comp ((fst.comp fst).pair (fst.comp (unpair.comp snd)))))
  have hout : Computable₂ fun (q : (Code × ℕ) × ℕ) (_ : ℕ) => q.2.unpair.1 :=
    (fst.comp (unpair.comp (snd.comp fst))).to₂
  exact Computable.option_map hev hout

theorem searchWith_partrec (cg : Code) : Partrec₂ (searchWith cg) :=
  Partrec.rfindOpt (searchStage_computable cg)

/-- Search through a recursively enumerable relation. -/
theorem exists_search {R : Code × ℕ → Prop} (hR : REPred R) :
    ∃ search : Code → ℕ →. ℕ, Partrec₂ search ∧ (∀ c x, search c x = search c 0) ∧
      (∀ {c : Code} {x y : ℕ}, y ∈ search c x → R (c, y)) ∧
      (∀ {c : Code}, (∃ n, R (c, n)) → ∃ m, m ∈ search c 0) := by
  obtain ⟨cg, hcg⟩ := exists_code.1 hR
  -- `cg` halts on the code of `a` exactly when `R a`.
  have hdom : ∀ a : Code × ℕ, (eval cg (Encodable.encode a)).Dom ↔ R a := by
    intro a
    have he : eval cg (Encodable.encode a)
        = (Part.assert (R a) fun _ => Part.some ()).map Encodable.encode := by
      rw [hcg]
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    rw [he]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
  refine ⟨searchWith cg, searchWith_partrec cg, fun _ _ => rfl, ?_, ?_⟩
  · intro c x y hy
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
    have hk' : (evaln k.unpair.2 cg (Encodable.encode (c, k.unpair.1))).map
        (fun _ => k.unpair.1) = some y := hk
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hk'
    exact (hdom _).1 (Part.dom_iff_mem.2 ⟨z, evaln_sound hz⟩)
  · rintro c ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 ((hdom (c, n)).2 hn)
    obtain ⟨s, hs⟩ := evaln_complete.1 hz
    have hs' : evaln s cg (Encodable.encode (c, n)) = some z := hs
    have hstage : searchStage cg c (Nat.pair n s) = some n := by
      unfold searchStage
      rw [Nat.unpair_pair]
      show (evaln s cg (Encodable.encode (c, n))).map (fun _ => n) = some n
      rw [hs']
      rfl
    have hdom' : (searchWith cg c 0).Dom :=
      Nat.rfindOpt_dom.2 ⟨Nat.pair n s, n, hstage⟩
    exact Part.dom_iff_mem.1 hdom'

#print axioms exists_search

end PAFlexibleOutput
