import PA194FoundationFormulaEqualityLift
namespace M6.PA.RelationalSource
open LO LO.FirstOrder ND

theorem rel_eq_eta (v : Fin 2 → GroundTerm) :
    Semiformula.rel Relation.eq v = eq (v 0) (v 1) := by
  apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 0) Relation.eq)
  funext i; fin_cases i <;> rfl

theorem rel_mem_eta (v : Fin 2 → GroundTerm) :
    Semiformula.rel Relation.mem v = mem (v 1) (v 0) := by
  apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 0) Relation.mem)
  funext i; fin_cases i <;> rfl

def FormulaEquality.relationTransport {Γ} {k : Nat} (E : FormulaEquality Γ)
    (r : Relation k) (v w : Fin k → GroundTerm)
    (he : ∀ i, ND.Proof Γ (eq (v i) (w i)))
    (h : ND.Proof Γ (.rel r v)) : ND.Proof Γ (.rel r w) := by
  cases r with
  | eq =>
    have h' : ND.Proof Γ (eq (v 0) (v 1)) := h.cast (by rw [rel_eq_eta])
    exact (E.atomTransport (he 0) (he 1) h').cast (by rw [rel_eq_eta])
  | mem =>
    have h' : ND.Proof Γ (mem (v 1) (v 0)) := h.cast (by rw [rel_mem_eta])
    exact (E.memberTransport (he 1) (he 0) h').cast (by rw [rel_mem_eta])

theorem rewrite_compose {n m k : Nat} (p : Semiproposition language n)
    (ω : Rew language Nat n Nat m) (τ : Rew language Nat m Nat k) :
    Semiformula.rewAux τ (Semiformula.rewAux ω p) = Semiformula.rewAux (τ.comp ω) p :=
  (TransitiveRewriting.comp_app ω τ p).symm

theorem eigen_formula {n : Nat} (ω : Rew language Nat n Nat 0)
    (p : Semiproposition language (n+1)) :
    (Semiformula.rewAux ω.q p).free = Semiformula.rewAux (eigenRewrite ω) p :=
  rewrite_compose p ω.q Rew.free

theorem open_shifted (p : Semiproposition language 1) :
    p.shift/[(Semiterm.fvar 0 : GroundTerm)] = p.free :=
  LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free p

theorem relational_shift_all (p : Semiproposition language 1) :
    (Semiformula.all p).shift = Semiformula.all p.shift := by
  change Semiformula.rewAux Rew.shift (.all p) = .all (Semiformula.rewAux Rew.shift p)
  simp only [Semiformula.rewAux,Rew.q_shift]
  rfl

theorem relational_shift_exs (p : Semiproposition language 1) :
    (Semiformula.exs p).shift = Semiformula.exs p.shift := by
  change Semiformula.rewAux Rew.shift (.exs p) = .exs (Semiformula.rewAux Rew.shift p)
  simp only [Semiformula.rewAux,Rew.q_shift]
  rfl

def FormulaEquality.formulaCongruence {Γ : List ND.Form} {n : Nat}
    (E : FormulaEquality Γ) (ω τ : Rew language Nat n Nat 0)
    (hb : ∀ i : Fin n, ND.Proof Γ (eq (ω (.bvar i)) (τ (.bvar i))))
    (hf : ∀ i : Nat, ND.Proof Γ (eq (ω (.fvar i)) (τ (.fvar i))))
    (p : Semiproposition language n) (h : ND.Proof Γ (Semiformula.rewAux ω p)) :
    ND.Proof Γ (Semiformula.rewAux τ p) :=
  match p with
  | .verum => h
  | .falsum => h
  | .rel r v => E.relationTransport r (ω ∘ v) (τ ∘ v)
      (fun i => E.termCongruence ω τ hb hf (v i)) h
  | .nrel r v => by
      apply ND.byContradiction
      let Δ := (Semiformula.nrel r (τ ∘ v)).neg :: Γ
      have inc : ∀ q, q ∈ Γ → q ∈ Δ := fun q hq => List.mem_cons_of_mem _ hq
      let E' := E.weaken inc
      have ht : ND.Proof Δ (.rel r (τ ∘ v)) := ND.assumption (by simp [Δ,Semiformula.neg])
      have hr := E'.relationTransport r (τ ∘ v) (ω ∘ v)
        (fun i => E'.symmetryOf (ND.weaken (E.termCongruence ω τ hb hf (v i)) inc)) ht
      exact ND.contradiction hr (ND.weaken h inc)
  | .and p q => ND.andIntro (E.formulaCongruence ω τ hb hf p (ND.andLeft h))
      (E.formulaCongruence ω τ hb hf q (ND.andRight h))
  | .or p q => by
      apply ND.orElim h
      · let inc : ∀ r, r ∈ Γ → r ∈ Semiformula.rewAux ω p :: Γ :=
          fun r hr => List.mem_cons_of_mem _ hr
        exact ND.orLeft ((E.weaken inc).formulaCongruence ω τ
          (fun i => ND.weaken (hb i) inc) (fun i => ND.weaken (hf i) inc) p
          (ND.assumption (by simp)))
      · let inc : ∀ r, r ∈ Γ → r ∈ Semiformula.rewAux ω q :: Γ :=
          fun r hr => List.mem_cons_of_mem _ hr
        exact ND.orRight ((E.weaken inc).formulaCongruence ω τ
          (fun i => ND.weaken (hb i) inc) (fun i => ND.weaken (hf i) inc) q
          (ND.assumption (by simp)))
  | .all p => by
      apply ND.allIntro
      have hs : ND.Proof (ND.shifted Γ) (Semiformula.rewAux (eigenRewrite ω) p) := by
        have ha : ND.Proof (ND.shifted Γ) (.all (Semiformula.rewAux ω.q p).shift) :=
          (ND.shiftProof h).cast (congrArg (fun q : ND.Form => q :: (ND.shifted Γ).map Semiformula.neg)
            (relational_shift_all (Semiformula.rewAux ω.q p)))
        have hd := ND.allElim _ (.fvar 0) ha
        exact hd.cast (by rw [open_shifted,eigen_formula])
      have ht := E.shifted.formulaCongruence (eigenRewrite ω) (eigenRewrite τ)
        (liftedBoundEquality E ω τ hb) (liftedFreeEquality ω τ hf) p hs
      exact ht.cast (by rw [eigen_formula])
  | .exs p => by
      apply ND.exsElim h
      let Δ := (Semiformula.rewAux ω.q p).free :: ND.shifted Γ
      have inc : ∀ r, r ∈ ND.shifted Γ → r ∈ Δ := fun r hr => List.mem_cons_of_mem _ hr
      have hs : ND.Proof Δ (Semiformula.rewAux (eigenRewrite ω) p) := by
        have hd : ND.Proof Δ (Semiformula.rewAux ω.q p).free := ND.assumption (by simp [Δ])
        exact hd.cast (by rw [eigen_formula])
      have ht := (E.shifted.weaken inc).formulaCongruence (eigenRewrite ω) (eigenRewrite τ)
        (fun i => ND.weaken (liftedBoundEquality E ω τ hb i) inc)
        (fun i => ND.weaken (liftedFreeEquality ω τ hf i) inc) p hs
      have ht' : ND.Proof Δ ((Semiformula.rewAux τ.q p).shift/[.fvar 0]) :=
        ht.cast (by rw [open_shifted,eigen_formula])
      exact (ND.exsIntro _ (.fvar 0) ht').cast (congrArg (fun q : ND.Form => q :: Δ.map Semiformula.neg)
        (relational_shift_exs (Semiformula.rewAux τ.q p)).symm)
termination_by structural p

def FormulaEquality.substituteOne {Γ : List ND.Form} (E : FormulaEquality Γ)
    (p : Semiproposition language 1) (a b : GroundTerm)
    (hab : ND.Proof Γ (eq a b))
    (hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a]) p)) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![b]) p) :=
  E.formulaCongruence (Rew.subst ![a]) (Rew.subst ![b])
    (by intro i; exact Fin.cases (by simpa using hab) (fun j => Fin.elim0 j) i)
    (by intro i; simpa using E.reflexive (.fvar i)) p hp

#print axioms FormulaEquality.formulaCongruence
#print axioms FormulaEquality.substituteOne
end M6.PA.RelationalSource

