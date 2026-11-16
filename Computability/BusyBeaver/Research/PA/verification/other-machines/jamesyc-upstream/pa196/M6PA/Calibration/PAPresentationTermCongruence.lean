module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationEqualityInstances
@[expose] public section

/-! Equality substitution for every arithmetic term, with actual finite
proofs supplied only by the six allowed equality axioms. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem func_zero_eta (v : Fin 0 → GroundTerm) : Semiterm.func Func.zero v = zero := by
  apply congrArg (Semiterm.func (L := language) (ξ := Nat) (n := 0) Func.zero)
  funext i; exact Fin.elim0 i

theorem func_succ_eta (v : Fin 1 → GroundTerm) : Semiterm.func Func.succ v = succ (v 0) := by
  apply congrArg (Semiterm.func (L := language) (ξ := Nat) (n := 0) Func.succ)
  funext i; fin_cases i; rfl

theorem func_add_eta (v : Fin 2 → GroundTerm) : Semiterm.func Func.add v = add (v 0) (v 1) := by
  apply congrArg (Semiterm.func (L := language) (ξ := Nat) (n := 0) Func.add)
  funext i; fin_cases i <;> rfl

theorem func_mul_eta (v : Fin 2 → GroundTerm) : Semiterm.func Func.mul v = mul (v 0) (v 1) := by
  apply congrArg (Semiterm.func (L := language) (ξ := Nat) (n := 0) Func.mul)
  funext i; fin_cases i <;> rfl

def EqualityPremises.termCongruence {Γ} {n : Nat} (E : EqualityPremises Γ)
    (ω τ : Rew language Nat n Nat 0)
    (hb : ∀ i : Fin n, ND.Proof Γ (eq (ω (.bvar i)) (τ (.bvar i))))
    (hf : ∀ i : Nat, ND.Proof Γ (eq (ω (.fvar i)) (τ (.fvar i))))
    (t : Semiterm language Nat n) : ND.Proof Γ (eq (ω t) (τ t)) :=
  match t with
  | .bvar i => hb i
  | .fvar i => hf i
  | .func .zero v => by
      simpa only [Rew.func,func_zero_eta] using E.reflexive zero
  | .func .succ v => by
      have h := E.termCongruence ω τ hb hf (v 0)
      simpa only [Rew.func,func_succ_eta,Function.comp_apply] using
        ND.mp h (E.successor (ω (v 0)) (τ (v 0)))
  | .func .add v => by
      have h := E.termCongruence ω τ hb hf (v 0)
      have k := E.termCongruence ω τ hb hf (v 1)
      simpa only [Rew.func,func_add_eta,Function.comp_apply] using
        ND.mp k (ND.mp h (E.addition (ω (v 0)) (τ (v 0)) (ω (v 1)) (τ (v 1))))
  | .func .mul v => by
      have h := E.termCongruence ω τ hb hf (v 0)
      have k := E.termCongruence ω τ hb hf (v 1)
      simpa only [Rew.func,func_mul_eta,Function.comp_apply] using
        ND.mp k (ND.mp h (E.multiplication (ω (v 0)) (τ (v 0)) (ω (v 1)) (τ (v 1))))
termination_by structural t

#print axioms EqualityPremises.termCongruence
end M6.PA.Presentation
