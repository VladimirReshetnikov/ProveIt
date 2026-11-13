import ConciseIPRA.NativeComposite
import ConciseIPRA.Interpretation

/-!
# The ordinary round trip

In `T_eq`, every formula is equivalent to the ordinary reading of its native
reading (`Teq.iff_toFm_ofFm`).  Hence `T_eq` proves a sequent exactly when the
native calculus proves its native reading (`Teq.iff_native`).

Most of the work is borrowed from the native calculus: by soundness, a native
derivation is usable inside `T_eq` under arbitrary hypotheses (`Teq.ofN`).
Only two directions mention a non-native formula where soundness cannot
reach it: a disjunction as a conclusion (handled by numerical cases on the
selector, `Teq.selCases`) and an implication as a hypothesis.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

theorem NPrf.hyp1 {Γ : List (NFm n)} {A B : NFm n} : NPrf (A :: B :: Γ) B :=
  .hyp (List.mem_cons_of_mem _ List.mem_cons_self)

namespace Teq

variable {Γ : List (Fm Tm n)}

/-- Native derivations are usable inside `T_eq` under arbitrary hypotheses. -/
theorem ofN {Δ : List (NFm n)} {A : NFm n} (h : NPrf Δ A)
    (hΔ : ∀ B ∈ Δ, Γ ⊢[TeqAx] B.toFm) : Γ ⊢[TeqAx] A.toFm :=
  (NPrf.sound h).trans fun χ hχ => by
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hχ
    exact hΔ B hB

theorem ofN1 {A B : NFm n} (h : NPrf [A] B) (hA : Γ ⊢[TeqAx] A.toFm) : Γ ⊢[TeqAx] B.toFm :=
  ofN h (by simpa using hA)

theorem ofN2 {A A' B : NFm n} (h : NPrf [A, A'] B) (hA : Γ ⊢[TeqAx] A.toFm)
    (hA' : Γ ⊢[TeqAx] A'.toFm) : Γ ⊢[TeqAx] B.toFm :=
  ofN h (by simpa using ⟨hA, hA'⟩)

/-- Interderivable native formulas have equivalent ordinary readings. -/
theorem iffOfN {A B : NFm n} (e : NEquiv A B) : Γ ⊢[TeqAx] Fm.iff A.toFm B.toFm :=
  Prf.iffI (.impI (ofN1 e.1 Prf.hyp0)) (.impI (ofN1 e.2 Prf.hyp0))

/-- Case analysis on a native selector inside `T_eq`. -/
theorem nselCases {X Y : NFm n} {χ : Fm Tm n} (v : Tm n)
    (h : Γ ⊢[TeqAx] (NFm.sel v X Y).toFm)
    (h₁ : X.toFm :: Γ ⊢[TeqAx] χ) (h₂ : Y.toFm :: Γ ⊢[TeqAx] χ) : Γ ⊢[TeqAx] χ := by
  refine casesOn v ?_ ?_
  · have hX : (v ≐ zero) :: Γ ⊢[TeqAx] X.toFm :=
      ofN2 (A := .eq v zero) (A' := NFm.sel v X Y) (B := X)
        ((NEquiv.sel_zero X Y).mp (NPrf.selTr X Y NPrf.hyp0 NPrf.hyp1)) Prf.hyp0 h.wk
    exact .impE (Prf.impI h₁).wk hX
  · have e : (NFm.sel v X Y).shift = NFm.sel (Syn.shift v) X.shift Y.shift :=
      NFm.sel_subst X v Y (fun i => Syn.var i.succ)
    have hS := h.shift.wk (ψ := Syn.shift v ≐ succ (Syn.var 0))
    rw [← NFm.toFm_shift, e] at hS
    have hY := ofN2 (A := .eq (Syn.shift v) (succ (Syn.var 0)))
      (A' := NFm.sel (Syn.shift v) X.shift Y.shift) (B := Y.shift)
      ((NEquiv.sel_succ X.shift (Syn.var 0) Y.shift).mp
        (NPrf.selTr X.shift Y.shift NPrf.hyp0 NPrf.hyp1)) Prf.hyp0 hS
    rw [NFm.toFm_shift] at hY
    exact .impE (Prf.impI h₂).shift.wk hY

/-! ### The connectives -/

theorem bot_iff : Γ ⊢[TeqAx] Fm.iff (NFm.bot : NFm n).toFm Fm.bot :=
  Prf.iffI sep (.impI (.botE _ Prf.hyp0))

theorem and_iff (X Y : NFm n) : Γ ⊢[TeqAx] Fm.iff (NFm.and X Y).toFm (X.toFm ⋏ Y.toFm) :=
  Prf.iffI
    (.impI (.andI (ofN1 (A := NFm.and X Y) (B := X) (NPrf.andE₁ NPrf.hyp0) Prf.hyp0)
      (ofN1 (A := NFm.and X Y) (B := Y) (NPrf.andE₂ NPrf.hyp0) Prf.hyp0)))
    (.impI (ofN2 (A := X) (A' := Y) (B := NFm.and X Y) (NPrf.andI NPrf.hyp0 NPrf.hyp1)
      (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))

theorem ex_iff (A : NFm (n + 1)) : Γ ⊢[TeqAx] Fm.iff (NFm.ex A).toFm (Fm.ex A.toFm) :=
  Prf.iffEx (iffOfN (NEquiv.qGate A))

theorem or_iff (X Y : NFm n) : Γ ⊢[TeqAx] Fm.iff (NFm.or X Y).toFm (X.toFm ⋎ Y.toFm) := by
  refine Prf.iffI (.impI ?_) (.impI (.orE Prf.hyp0 ?_ ?_))
  · have hE : (NFm.or X Y).toFm :: Γ ⊢[TeqAx]
        Fm.ex (NFm.sel (Syn.var 0) X.shift Y.shift).toFm :=
      Prf.iffMp (ex_iff _) Prf.hyp0
    refine .exE hE ?_
    refine nselCases (Syn.var 0) Prf.hyp0 ?_ ?_
    · rw [NFm.toFm_shift]
      exact .orI₁ Prf.hyp0
    · rw [NFm.toFm_shift]
      exact .orI₂ Prf.hyp0
  · exact ofN1 (A := X) (B := NFm.or X Y) (NPrf.orI₁ NPrf.hyp0) Prf.hyp0
  · exact ofN1 (A := Y) (B := NFm.or X Y) (NPrf.orI₂ NPrf.hyp0) Prf.hyp0

theorem imp_iff (X Y : NFm n) : Γ ⊢[TeqAx] Fm.iff (NFm.imp X Y).toFm (X.toFm ⟶ Y.toFm) := by
  refine Prf.iffI (.impI (.impI ?_)) (.impI ?_)
  · exact ofN2 (A := NFm.imp X Y) (A' := X) (B := Y) (NPrf.impE NPrf.hyp0 NPrf.hyp1)
      Prf.hyp1 Prf.hyp0
  · have e : (NFm.sel (Syn.var 0) X.shift Y.shift).toFm.subst (inst zero)
        = (NFm.sel zero X Y).toFm := by
      rw [← NFm.toFm_subst, NFm.sel_shift_inst]
    refine .impI ?_
    have h0 : (NFm.sel (Syn.var 0) X.shift Y.shift).toFm.subst (inst zero)
        :: (X.toFm ⟶ Y.toFm) :: Γ ⊢[TeqAx] (NFm.sel zero X Y).toFm := by
      rw [← e]
      exact Prf.hyp0
    exact .impE (ofN1 (A := Y) (B := NFm.imp X Y) (NPrf.impI NPrf.hyp1)
      (.impE Prf.hyp1 (ofN1 (A := NFm.sel zero X Y) (B := X) (NEquiv.sel_zero X Y).1 h0)))
      Prf.hyp0

theorem all_iff (X : NFm (n + 1)) : Γ ⊢[TeqAx] Fm.iff (NFm.all X).toFm (Fm.all X.toFm) := by
  refine Prf.iffTrans (and_iff _ _) ?_
  rw [NFm.toFm_subst, NFm.toFm_Q]
  exact Prf.iffI (.impI (.impE (.andE₂ Prf.hyp0) (.andE₁ Prf.hyp0)))
    (.impI (.andI (.allE zero Prf.hyp0) (.impI Prf.hyp1)))

/-! ### The round trip -/

/-- In `T_eq`, every formula is equivalent to the ordinary reading of its
native reading. -/
theorem iff_toFm_ofFm (φ : Fm Tm n) :
    ∀ {Γ : List (Fm Tm n)}, Γ ⊢[TeqAx] Fm.iff φ (NFm.ofFm φ).toFm := by
  induction φ with
  | eq s t => intro Γ; exact Prf.iffRefl _
  | bot => intro Γ; exact Prf.iffSymm bot_iff
  | and φ ψ ih₁ ih₂ =>
    intro Γ; exact Prf.iffTrans (Prf.iffAnd ih₁ ih₂) (Prf.iffSymm (and_iff _ _))
  | or φ ψ ih₁ ih₂ =>
    intro Γ; exact Prf.iffTrans (Prf.iffOr ih₁ ih₂) (Prf.iffSymm (or_iff _ _))
  | imp φ ψ ih₁ ih₂ =>
    intro Γ; exact Prf.iffTrans (Prf.iffImp ih₁ ih₂) (Prf.iffSymm (imp_iff _ _))
  | all φ ih => intro Γ; exact Prf.iffTrans (Prf.iffAll ih) (Prf.iffSymm (all_iff _))
  | ex φ ih => intro Γ; exact Prf.iffTrans (Prf.iffEx ih) (Prf.iffSymm (ex_iff _))

/-- `T_eq` proves a sequent exactly when the native calculus proves its native
reading. -/
theorem iff_native {Γ : List (Fm Tm n)} {φ : Fm Tm n} :
    (Γ ⊢[TeqAx] φ) ↔ NPrf (Γ.map NFm.ofFm) (NFm.ofFm φ) := by
  refine ⟨NPrf.ofPrf, fun h => ?_⟩
  refine Prf.iffMpr (iff_toFm_ofFm φ) ((NPrf.sound h).trans fun χ hχ => ?_)
  rw [List.map_map, List.mem_map] at hχ
  obtain ⟨ψ, hψ, rfl⟩ := hχ
  exact Prf.iffMp (iff_toFm_ofFm ψ) (.hyp hψ)

end Teq

end LeanProofs.ConciseIPRA
