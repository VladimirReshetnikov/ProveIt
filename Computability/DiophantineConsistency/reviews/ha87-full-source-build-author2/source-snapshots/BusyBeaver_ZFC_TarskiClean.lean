import BusyBeaver.ZFC.TarskiLeibniz

/-!
Clean forms for the completeness proof of the machines' Tarski calculus.

A formula is *clean* when no binder rebinds its own label inside its scope.
`cl K d f` relabels every binder of `f` by `K + depth`, which makes it clean,
and the calculus proves `f ↔ cl K d f` whenever `K ≥ top f` (by repeated
alpha-renaming). The semantic counterpart is the substitution lemma
`sat_rn`: renaming a free label in a formula is the same as updating the
assignment.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF Kalmar

/-! ## Size, cleanliness and relabelling -/

def size : NF → Nat
  | imp a b => size a + size b + 1
  | all _ a => size a + 1
  | _ => 0

theorem size_rn (x y : Nat) : ∀ f : NF, size (rn x y f) = size f
  | rel _ _ => rfl
  | NF.eq _ _ => rfl
  | NF.bot => rfl
  | imp a b => by simp only [rn, size, size_rn x y a, size_rn x y b]
  | all i a => by by_cases h : i = x <;> simp [rn, h, size, size_rn x y a]

/-- No binder rebinds its own label inside its scope. -/
def Clean : NF → Prop
  | rel _ _ => True
  | NF.eq _ _ => True
  | NF.bot => True
  | imp a b => Clean a ∧ Clean b
  | all i a => ¬ Bound i a ∧ Clean a

theorem clean_rn (x y : Nat) : ∀ f : NF, Clean f → Clean (rn x y f)
  | rel _ _, _ => trivial
  | NF.eq _ _, _ => trivial
  | NF.bot, _ => trivial
  | imp a b, h => ⟨clean_rn x y a h.1, clean_rn x y b h.2⟩
  | all i a, h => by
      by_cases hi : i = x
      · simp only [rn, hi, if_true]; subst hi; exact h
      · simp only [rn, hi, if_false]
        exact ⟨fun b => h.1 ((bound_rn x y i a).mp b), clean_rn x y a h.2⟩

/-- Relabel every binder by `K + depth`. -/
def cl (K : Nat) : Nat → NF → NF
  | d, all i a => all (K + d) (rn i (K + d) (cl K (d + 1) a))
  | d, imp a b => imp (cl K d a) (cl K d b)
  | _, rel i j => rel i j
  | _, NF.eq i j => NF.eq i j
  | _, NF.bot => NF.bot

theorem bound_cl (K : Nat) : ∀ (d : Nat) (f : NF) (n : Nat), Bound n (cl K d f) → K + d ≤ n
  | d, all i a, n, h => by
      simp only [cl, Bound] at h
      cases h with
      | inl h => omega
      | inr h => have := bound_cl K (d + 1) a n ((bound_rn i (K + d) n _).mp h); omega
  | d, imp a b, n, h => by
      simp only [cl, Bound] at h
      exact h.elim (fun h => bound_cl K d a n h) (fun h => bound_cl K d b n h)
  | _, rel _ _, _, h => h.elim
  | _, NF.eq _ _, _, h => h.elim
  | _, NF.bot, _, h => h.elim

theorem occurs_rn_cases {x y n : Nat} : ∀ {f : NF}, Occurs n (rn x y f) → Occurs n f ∨ n = y
  | rel i j, h => by
      simp only [rn, Occurs, rv] at h
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] at h <;> simp [Occurs] <;> omega
  | NF.eq i j, h => by
      simp only [rn, Occurs, rv] at h
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] at h <;> simp [Occurs] <;> omega
  | NF.bot, h => h.elim
  | imp a b, h => by
      simp only [rn, Occurs] at h
      exact h.elim (fun h => (occurs_rn_cases h).imp_left Or.inl)
        (fun h => (occurs_rn_cases h).imp_left Or.inr)
  | all i a, h => by
      by_cases hi : i = x
      · simp only [rn, hi, if_true] at h; subst hi; exact Or.inl h
      · simp only [rn, hi, if_false, Occurs] at h
        exact h.elim (fun h => Or.inl (Or.inl h)) (fun h => (occurs_rn_cases h).imp_left Or.inr)

theorem occurs_lt_top {n : Nat} : ∀ {f : NF}, Occurs n f → n < top f
  | rel i j, h => by simp only [Occurs] at h; simp only [top]; omega
  | NF.eq i j, h => by simp only [Occurs] at h; simp only [top]; omega
  | NF.bot, h => h.elim
  | imp a b, h => by
      simp only [top]
      cases h with
      | inl h | inr h => have := occurs_lt_top h; omega
  | all i a, h => by
      simp only [top]
      cases h with
      | inl h => omega
      | inr h => have := occurs_lt_top h; omega

/-- Labels of a relabelled formula are old labels or new binders. -/
theorem occurs_cl (K : Nat) : ∀ (d : Nat) (f : NF) (n : Nat),
    Occurs n (cl K d f) → n < top f ∨ K + d ≤ n
  | d, all i a, n, h => by
      simp only [cl, Occurs] at h
      cases h with
      | inl h => omega
      | inr h =>
          cases occurs_rn_cases h with
          | inl h => have := occurs_cl K (d + 1) a n h; simp only [top]; omega
          | inr h => omega
  | d, imp a b, n, h => by
      simp only [cl, Occurs] at h
      cases h with
      | inl h => exact (occurs_cl K d a n h).imp_left (fun h => by simp only [top]; omega)
      | inr h => exact (occurs_cl K d b n h).imp_left (fun h => by simp only [top]; omega)
  | _, rel i j, n, h => Or.inl (occurs_lt_top h)
  | _, NF.eq i j, n, h => Or.inl (occurs_lt_top h)
  | _, NF.bot, _, h => h.elim

theorem clean_cl (K : Nat) : ∀ (d : Nat) (f : NF), Clean (cl K d f)
  | d, all i a => by
      simp only [cl, Clean]
      refine ⟨fun b => ?_, clean_rn _ _ _ (clean_cl K (d + 1) a)⟩
      have := bound_cl K (d + 1) a (K + d) ((bound_rn i (K + d) (K + d) _).mp b)
      omega
  | d, imp a b => ⟨clean_cl K d a, clean_cl K d b⟩
  | _, rel _ _ => trivial
  | _, NF.eq _ _ => trivial
  | _, NF.bot => trivial

/-! ## Semantic substitution -/

universe u
variable {V : Type u}

theorem update_comm (e : Nat → V) {i x : Nat} (h : i ≠ x) (d v : V) :
    update (update e i d) x v = update (update e x v) i d := by
  funext n
  simp only [update]
  by_cases hn : n = x <;> by_cases hm : n = i
  · exact absurd (hm.symm.trans hn) h
  · simp [hn, Ne.symm h]
  · simp [hm, h]
  · simp [hn, hm]

/-- Renaming a free label is updating the assignment. -/
theorem sat_rn (mem : V → V → Prop) (x c : Nat) :
    ∀ (f : NF) (e : Nat → V), ¬ Bound x f → ¬ Bound c f →
      (Sat mem e (rn x c f) ↔ Sat mem (update e x (e c)) f)
  | rel i j, e, _, _ => by
      simp only [rn, Sat, rv, update]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj]
  | NF.eq i j, e, _, _ => by
      simp only [rn, Sat, rv, update]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj]
  | NF.bot, _, _, _ => Iff.rfl
  | imp a b, e, hx, hc => by
      simp only [rn, Sat]
      rw [sat_rn mem x c a e (fun h => hx (Or.inl h)) (fun h => hc (Or.inl h)),
        sat_rn mem x c b e (fun h => hx (Or.inr h)) (fun h => hc (Or.inr h))]
  | all i a, e, hx, hc => by
      have hix : i ≠ x := fun h => hx (Or.inl h.symm)
      have hic : i ≠ c := fun h => hc (Or.inl h.symm)
      simp only [rn, hix, if_false, Sat]
      refine forall_congr' fun d => ?_
      rw [sat_rn mem x c a (update e i d) (fun h => hx (Or.inr h)) (fun h => hc (Or.inr h)),
        update_other e d (Ne.symm hic), update_comm e hix]

/-! ## Provable equivalence with the clean form -/

variable {Ax : NF → Prop}

section Equiv

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

theorem imp_congr {a a' b b' : NF}
    (ha : Thm Ax (imp a' a)) (hb : Thm Ax (imp b b')) :
    Thm Ax (imp (imp a b) (imp a' b')) :=
  ded2 hC (.mp (.ax hb) (.mp h1 (.mp (.ax ha) h0)))

/-- `f ↔ cl K d f` when `K ≥ top f`. -/
theorem cl_equiv (K : Nat) : ∀ (d : Nat) (f : NF), top f ≤ K →
    Thm Ax (imp f (cl K d f)) ∧ Thm Ax (imp (cl K d f) f)
  | d, all i a, hK => by
      simp only [top] at hK
      have ih := cl_equiv K (d + 1) a (by omega)
      let a' := cl K (d + 1) a
      have hne : K + d ≠ i := by omega
      have hb : ¬ Bound i a' := fun b => by have := bound_cl K (d + 1) a i b; omega
      have ho : ¬ Occurs (K + d) a' := fun o => by
        cases occurs_cl K (d + 1) a (K + d) o with
        | inl h | inr h => omega
      simp only [cl]
      exact ⟨syl hC (all_mono hC i ih.1) (alpha_fwd hC hne hb ho),
        syl hC (alpha_bwd hC hne hb ho) (all_mono hC i ih.2)⟩
  | d, imp a b, hK => by
      simp only [top] at hK
      have ha := cl_equiv K d a (by omega)
      have hb := cl_equiv K d b (by omega)
      simp only [cl]
      exact ⟨imp_congr hC ha.2 hb.1, imp_congr hC ha.1 hb.2⟩
  | _, rel i j, _ => ⟨self_imp hC _, self_imp hC _⟩
  | _, NF.eq i j, _ => ⟨self_imp hC _, self_imp hC _⟩
  | _, NF.bot, _ => ⟨self_imp hC _, self_imp hC _⟩

end Equiv

end SetTheory.BusyBeaver.ZFC.Tarski
