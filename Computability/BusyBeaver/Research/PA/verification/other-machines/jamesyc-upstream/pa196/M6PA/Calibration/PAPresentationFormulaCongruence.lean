module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationEqualityLift
@[expose] public section

/-! Constructive equality substitution for arbitrary arithmetic formulas,
including both quantifiers. Every value is an actual finite LK derivation;
the only arithmetic leaves are the six explicit equality axioms. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem rel_eq_eta (v : Fin 2 → GroundTerm) :
    Semiformula.rel Rel.eq v = eq (v 0) (v 1) := by
  apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 0) Rel.eq)
  funext i; fin_cases i <;> rfl

theorem nrel_eq_eta (v : Fin 2 → GroundTerm) :
    Semiformula.nrel Rel.eq v = (eq (v 0) (v 1)).neg := by
  apply congrArg (Semiformula.nrel (L := language) (ξ := Nat) (n := 0) Rel.eq)
  funext i; fin_cases i <;> rfl

theorem eigen_formula {n : Nat} (ω : Rew language Nat n Nat 0)
    (p : Semiproposition language (n+1)) :
    (Semiformula.rewAux ω.q p).free = Semiformula.rewAux (eigenRewrite ω) p :=
  rewrite_compose p ω.q Rew.free

theorem open_shifted (p : Semiproposition language 1) :
    p.shift/[(Semiterm.fvar 0 : GroundTerm)] = p.free :=
  LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free p

theorem presentation_shift_all (p : Semiproposition language 1) :
    (Semiformula.all p).shift = Semiformula.all p.shift := by
  change Semiformula.rewAux Rew.shift (.all p) = .all (Semiformula.rewAux Rew.shift p)
  simp only [Semiformula.rewAux,Rew.q_shift]
  rfl

theorem presentation_shift_exs (p : Semiproposition language 1) :
    (Semiformula.exs p).shift = Semiformula.exs p.shift := by
  change Semiformula.rewAux Rew.shift (.exs p) = .exs (Semiformula.rewAux Rew.shift p)
  simp only [Semiformula.rewAux,Rew.q_shift]
  rfl

def EqualityPremises.formulaCongruence {Γ : List ND.Form} {n : Nat}
    (E : EqualityPremises Γ) (ω τ : Rew language Nat n Nat 0)
    (hb : ∀ i : Fin n, ND.Proof Γ (eq (ω (.bvar i)) (τ (.bvar i))))
    (hf : ∀ i : Nat, ND.Proof Γ (eq (ω (.fvar i)) (τ (.fvar i))))
    (p : Semiproposition language n) (h : ND.Proof Γ (Semiformula.rewAux ω p)) :
    ND.Proof Γ (Semiformula.rewAux τ p) :=
  match p with
  | .verum => h
  | .falsum => h
  | .rel .eq v => by
      have h' : ND.Proof Γ (eq (ω (v 0)) (ω (v 1))) := h.cast (by
        simp only [Semiformula.rewAux,rel_eq_eta,Function.comp_apply])
      have ht := E.atomTransport (E.termCongruence ω τ hb hf (v 0))
        (E.termCongruence ω τ hb hf (v 1)) h'
      exact ht.cast (by simp only [Semiformula.rewAux,rel_eq_eta,Function.comp_apply])
  | .nrel .eq v => by
      have h' : ND.Proof Γ (eq (ω (v 0)) (ω (v 1))).neg := h.cast (by
        simp only [Semiformula.rewAux,nrel_eq_eta,Function.comp_apply])
      have ht : ND.Proof Γ (eq (τ (v 0)) (τ (v 1))).neg := by
        apply ND.byContradiction
        let Δ := (eq (τ (v 0)) (τ (v 1))).neg.neg :: Γ
        have inc : ∀ q, q ∈ Γ → q ∈ Δ := fun q hq => List.mem_cons_of_mem _ hq
        let E' := E.weaken inc
        have ht' : ND.Proof Δ (eq (τ (v 0)) (τ (v 1))) :=
          ND.assumption (by simp [Δ,Semiformula.neg_neg])
        have hr := E'.atomTransport
          (E'.symmetryOf (ND.weaken (E.termCongruence ω τ hb hf (v 0)) inc))
          (E'.symmetryOf (ND.weaken (E.termCongruence ω τ hb hf (v 1)) inc)) ht'
        exact ND.contradiction hr (ND.weaken h' inc)
      exact ht.cast (by simp only [Semiformula.rewAux,nrel_eq_eta,Function.comp_apply])
  | .and p q =>
      ND.andIntro (E.formulaCongruence ω τ hb hf p (ND.andLeft h))
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
          (ND.shiftProof h).cast (congrArg (fun q : ND.Form => ND.negatives (ND.shifted Γ) + ⦃q⦄)
            (presentation_shift_all (Semiformula.rewAux ω.q p)))
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
      exact (ND.exsIntro _ (.fvar 0) ht').cast (congrArg (fun q : ND.Form => ND.negatives Δ + ⦃q⦄)
        (presentation_shift_exs (Semiformula.rewAux τ.q p)).symm)
termination_by structural p

/-- The one-bound-variable instance used by the induction adapter. Free
parameters are unchanged and their equality proofs are reflexivity. -/
def EqualityPremises.substituteOne {Γ : List ND.Form} (E : EqualityPremises Γ)
    (p : Semiproposition language 1) (a b : GroundTerm)
    (hab : ND.Proof Γ (eq a b))
    (hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a]) p)) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![b]) p) :=
  E.formulaCongruence (Rew.subst ![a]) (Rew.subst ![b])
    (by intro i; exact Fin.cases (by simpa using hab) (fun j => Fin.elim0 j) i)
    (by intro i; simpa using E.reflexive (.fvar i)) p hp

#print axioms EqualityPremises.formulaCongruence
end M6.PA.Presentation
