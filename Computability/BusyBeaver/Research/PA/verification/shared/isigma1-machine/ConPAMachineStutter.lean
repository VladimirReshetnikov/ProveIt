import ConPAMachine
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSectionVars false
namespace ConPA.Machine.Stutter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem runDefinable (T : Table) : 𝚺₁-Function₁ (run (V := V) T) := by
  have h : 𝚺₁.Definable (fun v : Fin 2 → V =>
      v 0 = (construction T).result (fun _ : Fin 0 => v 1) (v 1)) := by
    simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (construction (V := V) T).result_defined.to_definable
  change 𝚺₁.Definable (fun v : Fin 2 → V => v 0 = (construction T).result ![] (v 1))
  have eqfun : (fun v : Fin 2 → V => v 0 = (construction T).result (fun _ : Fin 0 => v 1) (v 1)) =
      (fun v : Fin 2 → V => v 0 = (construction T).result ![] (v 1)) := by
    funext v
    rw [show (fun _ : Fin 0 => v 1) = ![] from Subsingleton.elim _ _]
  rw [←eqfun]
  exact h

theorem run_add_nat (T : Table) (t : V) (k : ℕ) :
    run T (t + (k : V)) = (step (V := V) T)^[k] (run T t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, run_succ, ih, Function.iterate_succ_apply']

private theorem cast_one_le (k : ℕ) (hk : 0 < k) : (1 : V) ≤ (k : V) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [Nat.cast_succ]
    exact le_add_of_nonneg_left (zero_le : (0 : V) ≤ (k : V))

/-- If the variant has entered an absorbing halt, it remains there at every
    later model-valued time. -/
theorem haltPersists (T : Table) (halt : ℕ)
    (absorb : ∀ y : V, π₁ y = (halt : V) → step T y = y)
    (a b : V) (hle : a ≤ b) (hh : π₁ (run T a) = (halt : V)) :
    π₁ (run T b) = (halt : V) := by
  obtain ⟨c,rfl⟩ := exists_add_of_le hle
  haveI := runDefinable (V := V) T
  have hd : 𝚺₁-Predicate (fun d : V => run T (a+d) = run T a) := by definability
  have fix : ∀ d : V, run T (a+d) = run T a := by
    intro d
    induction d using ISigma1.sigma1_succ_induction with
    | hP => exact hd
    | zero => simp
    | succ d ih =>
      rw [← add_assoc,run_succ,ih]
      exact absorb _ hh
  rw [fix]
  exact hh

private theorem syncDef (P Q : Table) (R : V → V → Prop) (hR : 𝚺₁-Relation R) :
    𝚺₁-Predicate (fun n : V => ∃ t : V, n ≤ t ∧ R (run P n) (run Q t)) := by
  haveI := hR
  haveI := runDefinable (V := V) P
  haveI := runDefinable (V := V) Q
  definability

theorem synchronize (P Q : Table) (R : V → V → Prop) (hR : 𝚺₁-Relation R)
    (initial : R 0 0)
    (advance : ∀ n t : V, R (run P n) (run Q t) →
      ∃ k : ℕ, 0 < k ∧ R (step P (run P n)) ((step Q)^[k] (run Q t))) :
    ∀ n : V, ∃ t : V, n ≤ t ∧ R (run P n) (run Q t) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact syncDef P Q R hR
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    simpa only [run_zero] using initial
  | succ n ih =>
    obtain ⟨t,hle,ht⟩ := ih
    obtain ⟨k,hk,hs⟩ := advance n t ht
    refine ⟨t+(k : V),add_le_add hle (cast_one_le k hk),?_⟩
    rw [run_succ,run_add_nat]
    exact hs

/-- A Σ₁ relation with positive finite stuttering, matched halting and an
    absorbing variant halt transfers modeled halting in both directions. -/
theorem equivalent (P Q : Table) (primaryHalt variantHalt : ℕ)
    (R : V → V → Prop) (hR : 𝚺₁-Relation R) (initial : R 0 0)
    (haltMatch : ∀ x y, R x y → (π₁ x = (primaryHalt : V) ↔ π₁ y = (variantHalt : V)))
    (absorb : ∀ y, π₁ y = (variantHalt : V) → step Q y = y)
    (segment : ∀ x y, R x y → π₁ x ≠ (primaryHalt : V) →
      ∃ k : ℕ, 0 < k ∧ R (step P x) ((step Q)^[k] y)) :
    (∃ t : V, π₁ (run Q t) = (variantHalt : V)) ↔
      (∃ n : V, π₁ (run P n) = (primaryHalt : V)) := by
  classical
  constructor
  · rintro ⟨t,hh⟩
    by_contra h
    have sync := synchronize P Q R hR initial (fun n _ hr =>
      segment _ _ hr (fun he => h ⟨n,he⟩))
    obtain ⟨u,htu,hu⟩ := sync t
    have hp := haltPersists Q variantHalt absorb t u htu hh
    exact h ⟨t,(haltMatch _ _ hu).mpr hp⟩
  · rintro ⟨n,hn⟩
    by_contra h
    have rejects (m t : V) (hr : R (run P m) (run Q t)) :
        π₁ (run P m) ≠ (primaryHalt : V) := by
      intro he
      exact h ⟨t,(haltMatch _ _ hr).mp he⟩
    have sync := synchronize P Q R hR initial (fun m t hr =>
      segment _ _ hr (rejects m t hr))
    obtain ⟨t,_,ht⟩ := sync n
    exact rejects n t ht hn

#print axioms runDefinable
#print axioms run_add_nat
#print axioms haltPersists
#print axioms synchronize
#print axioms equivalent
end models
end ConPA.Machine.Stutter
