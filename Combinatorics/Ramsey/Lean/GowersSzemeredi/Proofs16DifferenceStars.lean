import GowersSzemeredi.Proofs16FibreStars

/-! Dense pair relations admit large families coherent within each
index-difference fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def differencePair {N : Nat} (d a : ZMod N) : ZMod N × ZMod N := (d+a,a)

/-- Reparametrize equal-difference pair relations by three coordinates. -/
theorem difference_relation_card {N : Nat} [NeZero N]
    (R : (ZMod N × ZMod N) → (ZMod N × ZMod N) → Prop)
    (hR : ∀ p q, R p q → p.1-p.2 = q.1-q.2) :
    (Finset.univ.filter (fun t : ZMod N × ZMod N × ZMod N =>
      R (differencePair t.1 t.2.1) (differencePair t.1 t.2.2))).card =
    (Finset.univ.filter (fun t : (ZMod N × ZMod N) × (ZMod N × ZMod N) => R t.1 t.2)).card := by
  apply Finset.card_bij (fun t _ => (differencePair t.1 t.2.1, differencePair t.1 t.2.2))
  · intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
  · intro t ht u hu heq
    have ha : t.2.1 = u.2.1 := congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.1.2) heq
    have hb : t.2.2 = u.2.2 := congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.2.2) heq
    have hd : t.1 + t.2.1 = u.1 + u.2.1 := congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.1.1) heq
    exact Prod.ext (add_right_cancel (ha ▸ hd)) (Prod.ext ha hb)
  · intro p hp
    have hr := (Finset.mem_filter.mp hp).2
    have hd := hR p.1 p.2 hr
    have h1 : differencePair (p.1.1-p.1.2) p.1.2 = p.1 := by
      ext <;> simp [differencePair]
    have h2 : differencePair (p.1.1-p.1.2) p.2.2 = p.2 := by
      rw [hd]; ext <;> simp [differencePair]
    refine ⟨(p.1.1-p.1.2,p.1.2,p.2.2), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [h1, h2] using hr⟩
    · exact Prod.ext h1 h2

/-- Reparametrize selected leaves by their difference and second entry. -/
theorem difference_star_card {N : Nat} [NeZero N]
    (R : (ZMod N × ZMod N) → (ZMod N × ZMod N) → Prop) (c : ZMod N → ZMod N) :
    (Finset.univ.filter (fun t : ZMod N × ZMod N =>
      R (differencePair t.1 (c t.1)) (differencePair t.1 t.2))).card =
    (Finset.univ.filter (fun p : ZMod N × ZMod N =>
      R (differencePair (p.1-p.2) (c (p.1-p.2))) p)).card := by
  apply Finset.card_bij (fun t _ => differencePair t.1 t.2)
  · intro t ht
    simpa [differencePair] using ht
  · intro t ht u hu heq
    have ha := congrArg (fun p : ZMod N × ZMod N => p.2) heq
    change t.2 = u.2 at ha
    have hd : t.1+t.2 = u.1+u.2 := congrArg (fun p : ZMod N × ZMod N => p.1) heq
    exact Prod.ext (add_right_cancel (ha ▸ hd)) ha
  · intro p hp
    refine ⟨(p.1-p.2,p.2), ?_, ?_⟩
    · simpa [differencePair] using hp
    · ext <;> simp [differencePair]

/-- Select at least `|R|/N` pairs so that any two selected pairs with
the same difference have a common relation centre. -/
theorem exists_difference_stars {N : Nat} [NeZero N]
    (R : (ZMod N × ZMod N) → (ZMod N × ZMod N) → Prop)
    (hR : ∀ p q, R p q → p.1-p.2 = q.1-q.2) :
    ∃ P : Finset (ZMod N × ZMod N),
      (Finset.univ.filter (fun t : (ZMod N × ZMod N) × (ZMod N × ZMod N) => R t.1 t.2)).card ≤ N * P.card ∧
      (∀ p ∈ P, ∃ z, R z p) ∧
      (∀ p ∈ P, ∀ q ∈ P, p.1-p.2 = q.1-q.2 → ∃ z, R z p ∧ R z q) := by
  obtain ⟨c, hc⟩ := exists_large_fibre_stars
    (fun d a b : ZMod N => R (differencePair d a) (differencePair d b))
  let P := Finset.univ.filter (fun p : ZMod N × ZMod N =>
    R (differencePair (p.1-p.2) (c (p.1-p.2))) p)
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [difference_relation_card R hR, difference_star_card, ZMod.card] at hc
    exact hc
  · intro p hp
    exact ⟨_, (Finset.mem_filter.mp hp).2⟩
  · intro p hp q hq hd
    refine ⟨differencePair (p.1-p.2) (c (p.1-p.2)), (Finset.mem_filter.mp hp).2, ?_⟩
    rw [hd]
    exact (Finset.mem_filter.mp hq).2

end LeanProofs.GowersSzemeredi
