import IPRADerivations.Geometry.LocalizationWitness
import IPRADerivations.Core.Pairing

/-!
# The power-cover constructor for every exponent

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (`thm:power-cover`, for two
generators): from a cover certificate `c₀ f₀ + c₁ f₁ = 1` there are coefficients, given by a
primitive-recursive construction uniform in `N`, with `d₀ f₀^N + d₁ f₁^N = 1`.

The generators `f₀, f₁` are natural numbers and the coefficients are integers. The data are read
from one parameter code `x`: `c₀ = C0 x`, `c₁ = C1 x` (pairs of natural numbers), `f₀ = F0 x`,
`f₁ = F1 x`. The coefficient pair is a state `st k x`, defined by primitive recursion on `k`:
`st 0 x = (c₀, c₁)`, and `st (k + 1) x` is the update of `cover_step`
(`Geometry/LocalizationWitness`) applied to `st k x` with `P = f₀^k`, `Q = f₁^k`.

* `st_zero`, `st_succ`: the defining equations;
* `power_cover`: if `c₀ f₀ + c₁ f₁ = 1`, then for every `k`
  `d₀ f₀^(k+1) + d₁ f₁^(k+1) = 1` with `(d₀, d₁) = st k x`. The invariant is an equation between
  primitive-recursive terms, and the induction on `k` is quantifier-free.

More than two generators and the gluing theorems are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PowerCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.LocalizationWitness (cover_step)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Reading a state and a parameter code -/

/-- First coefficient of a state `⟨⟨a, b⟩, ⟨c, e⟩⟩`: `a − b`. -/
def D0 {n : ℕ} (s : PTm n) : ZT n := ⟨fstT (fstT s), sndT (fstT s)⟩
/-- Second coefficient: `c − e`. -/
def D1 {n : ℕ} (s : PTm n) : ZT n := ⟨fstT (sndT s), sndT (sndT s)⟩
/-- The cover coefficients, read from `x = ⟨⟨⟨c₀⁺, c₀⁻⟩, ⟨c₁⁺, c₁⁻⟩⟩, ⟨f₀, f₁⟩⟩`. -/
def C0 {n : ℕ} (x : PTm n) : ZT n := D0 (fstT x)
def C1 {n : ℕ} (x : PTm n) : ZT n := D1 (fstT x)
/-- The generators. -/
def F0 {n : ℕ} (x : PTm n) : ZT n := ZT.ofNat (fstT (sndT x))
def F1 {n : ℕ} (x : PTm n) : ZT n := ZT.ofNat (sndT (sndT x))
/-- `f₀^k`, `f₁^k`. -/
def Pk {n : ℕ} (x k : PTm n) : ZT n := ZT.ofNat (pw (fstT (sndT x)) k)
def Qk {n : ℕ} (x k : PTm n) : ZT n := ZT.ofNat (pw (sndT (sndT x)) k)

/-- The update of `cover_step`. -/
def NX0 {n : ℕ} (s x k : PTm n) : ZT n :=
  D0 s * C0 x + D0 s * D0 s * C1 x * Pk x k * F1 x + D0 s * D1 s * C0 x * (F1 x * Qk x k)
def NX1 {n : ℕ} (s x k : PTm n) : ZT n :=
  D1 s * C1 x + D0 s * D1 s * C1 x * (F0 x * Pk x k) + D1 s * D1 s * C0 x * F0 x * Qk x k

section Subst

variable {m : ℕ} (σ : Fin n → PTm m)

@[simp] theorem D0_subst (s : PTm n) : (D0 s).subst σ = D0 (Syn.subst σ s) := by simp [D0, ZT.subst]
@[simp] theorem D1_subst (s : PTm n) : (D1 s).subst σ = D1 (Syn.subst σ s) := by simp [D1, ZT.subst]
@[simp] theorem C0_subst (x : PTm n) : (C0 x).subst σ = C0 (Syn.subst σ x) := by simp [C0]
@[simp] theorem C1_subst (x : PTm n) : (C1 x).subst σ = C1 (Syn.subst σ x) := by simp [C1]
@[simp] theorem F0_subst (x : PTm n) : (F0 x).subst σ = F0 (Syn.subst σ x) := by simp [F0]
@[simp] theorem F1_subst (x : PTm n) : (F1 x).subst σ = F1 (Syn.subst σ x) := by simp [F1]
@[simp] theorem Pk_subst (x k : PTm n) : (Pk x k).subst σ = Pk (Syn.subst σ x) (Syn.subst σ k) := by
  simp [Pk]
@[simp] theorem Qk_subst (x k : PTm n) : (Qk x k).subst σ = Qk (Syn.subst σ x) (Syn.subst σ k) := by
  simp [Qk]
@[simp] theorem NX0_subst (s x k : PTm n) :
    (NX0 s x k).subst σ = NX0 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [NX0]
@[simp] theorem NX1_subst (s x k : PTm n) :
    (NX1 s x k).subst σ = NX1 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [NX1]

end Subst

/-! ## The coefficient sequence -/

/-- The step; variables `0 = k`, `1 = st k`, `2 = x`. -/
def stepT : PTm 3 :=
  pairT (pairT (NX0 (var 1) (var 2) (var 0)).pos (NX0 (var 1) (var 2) (var 0)).neg)
    (pairT (NX1 (var 1) (var 2) (var 0)).pos (NX1 (var 1) (var 2) (var 0)).neg)

abbrev stF : PR 2 := rec2 (fstT (var 0)) stepT

/-- The coefficient state after `k` steps. -/
abbrev st {n : ℕ} (k x : PTm n) : PTm n := ap2 stF k x

theorem st_zero (x : PTm n) : Γ ⊢[PRAAx] st zero x ≐ fstT x := by
  have h := rec2_zero (Γ := Γ) (fstT (var 0)) stepT x
  simpa using h

theorem stepT_subst (k s x : PTm n) :
    Syn.subst ![k, s, x] stepT =
      pairT (pairT (NX0 s x k).pos (NX0 s x k).neg) (pairT (NX1 s x k).pos (NX1 s x k).neg) := by
  have e₀ : (NX0 (var 1) (var 2) (var 0) : ZT 3).subst ![k, s, x] = NX0 s x k := by simp
  have e₁ : (NX1 (var 1) (var 2) (var 0) : ZT 3).subst ![k, s, x] = NX1 s x k := by simp
  simp only [stepT, subst_pairT]
  rw [← e₀, ← e₁]
  rfl

theorem st_succ (k x : PTm n) :
    Γ ⊢[PRAAx] st (succ k) x ≐
      pairT (pairT (NX0 (st k x) x k).pos (NX0 (st k x) x k).neg)
        (pairT (NX1 (st k x) x k).pos (NX1 (st k x) x k).neg) := by
  have h := rec2_succ (Γ := Γ) (fstT (var 0)) stepT k x
  rw [stepT_subst] at h
  exact h

/-! ## Evaluations of the state -/

theorem toZ_D0_of {s a b c e : PTm n} (h : Γ ⊢[PRAAx] s ≐ pairT (pairT a b) (pairT c e)) :
    ZT.toZ Γ (D0 s) = Groth.ι (Q.mk Γ a) - Groth.ι (Q.mk Γ b) := by
  have ha := natEq ((congrFst (congrFst h)).eqTrans ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)))
  have hb := natEq ((congrSnd (congrFst h)).eqTrans ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)))
  show Groth.ι (Q.mk Γ (fstT (fstT s))) - Groth.ι (Q.mk Γ (sndT (fstT s))) = _
  rw [ha, hb]

theorem toZ_D1_of {s a b c e : PTm n} (h : Γ ⊢[PRAAx] s ≐ pairT (pairT a b) (pairT c e)) :
    ZT.toZ Γ (D1 s) = Groth.ι (Q.mk Γ c) - Groth.ι (Q.mk Γ e) := by
  have hc := natEq ((congrFst (congrSnd h)).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))
  have he := natEq ((congrSnd (congrSnd h)).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
  show Groth.ι (Q.mk Γ (fstT (sndT s))) - Groth.ι (Q.mk Γ (sndT (sndT s))) = _
  rw [hc, he]

theorem toZ_D0_succ (k x : PTm n) :
    ZT.toZ Γ (D0 (st (succ k) x)) = ZT.toZ Γ (NX0 (st k x) x k) := toZ_D0_of (st_succ k x)

theorem toZ_D1_succ (k x : PTm n) :
    ZT.toZ Γ (D1 (st (succ k) x)) = ZT.toZ Γ (NX1 (st k x) x k) := toZ_D1_of (st_succ k x)

theorem toZ_D0_zero (x : PTm n) : ZT.toZ Γ (D0 (st zero x)) = ZT.toZ Γ (C0 x) := by
  have ha := natEq (congrFst (congrFst (st_zero (Γ := Γ) x)))
  have hb := natEq (congrSnd (congrFst (st_zero (Γ := Γ) x)))
  show Groth.ι (Q.mk Γ (fstT (fstT (st zero x)))) - Groth.ι (Q.mk Γ (sndT (fstT (st zero x)))) =
    Groth.ι (Q.mk Γ (fstT (fstT (fstT x)))) - Groth.ι (Q.mk Γ (sndT (fstT (fstT x))))
  rw [ha, hb]

theorem toZ_D1_zero (x : PTm n) : ZT.toZ Γ (D1 (st zero x)) = ZT.toZ Γ (C1 x) := by
  have hc := natEq (congrFst (congrSnd (st_zero (Γ := Γ) x)))
  have he := natEq (congrSnd (congrSnd (st_zero (Γ := Γ) x)))
  show Groth.ι (Q.mk Γ (fstT (sndT (st zero x)))) - Groth.ι (Q.mk Γ (sndT (sndT (st zero x)))) =
    Groth.ι (Q.mk Γ (fstT (sndT (fstT x)))) - Groth.ι (Q.mk Γ (sndT (sndT (fstT x))))
  rw [hc, he]

/-! ## The invariant -/

/-- `d₀ f₀^(k+1) + d₁ f₁^(k+1) = 1` for the state `s`. -/
def Inv {n : ℕ} (s x k : PTm n) : Fm PTm n :=
  ZT.eq (D0 s * (F0 x * Pk x k) + D1 s * (F1 x * Qk x k)) (ZT.natLit 1)

/-- The cover certificate `c₀ f₀ + c₁ f₁ = 1`. -/
def Cover {n : ℕ} (x : PTm n) : Fm PTm n := ZT.eq (C0 x * F0 x + C1 x * F1 x) (ZT.natLit 1)

theorem inv_base {x : PTm n} (hu : Γ ⊢[PRAAx] Cover x) : Γ ⊢[PRAAx] Inv (st zero x) x zero := by
  have eu := ZT.toZ_eq hu
  have p₀ := natEq (pw_zero (Γ := Γ) (fstT (sndT x))); have q₀ := natEq (pw_zero (Γ := Γ) (sndT (sndT x)))
  unfold Inv
  apply ZT.derive
  simp only [F0, F1, Pk, Qk] at eu ⊢
  ipra_simps
  rw [toZ_D0_zero, toZ_D1_zero, p₀, q₀]
  linear_combination eu

theorem inv_step {x k : PTm n} (hu : Γ ⊢[PRAAx] Cover x) (ih : Γ ⊢[PRAAx] Inv (st k x) x k) :
    Γ ⊢[PRAAx] Inv (st (succ k) x) x (succ k) := by
  have e := ZT.toZ_eq (cover_step (P := Pk x k) (Q := Qk x k) hu ih)
  have p₁ := natEq (pw_succ (Γ := Γ) (fstT (sndT x)) k)
  have q₁ := natEq (pw_succ (Γ := Γ) (sndT (sndT x)) k)
  unfold Inv
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_mul, toZ_D0_succ, toZ_D1_succ]
  simp only [NX0, NX1, F0, F1, Pk, Qk] at e ⊢
  ipra_simps
  rw [p₁, q₁]
  linear_combination e

/-- Variables: `0 = k` (induction), `1 = x`. -/
private abbrev covF : Fm PTm 2 := Cover (var 1) ⟶ Inv (st (var 0) (var 1)) (var 1) (var 0)

theorem Cover_subst {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    (Cover x).subst σ = Cover (Syn.subst σ x) := by simp [Cover]

theorem Inv_subst {m : ℕ} (σ : Fin n → PTm m) (s x k : PTm n) :
    (Inv s x k).subst σ = Inv (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [Inv]

private theorem cov₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] covF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Cover_subst, Inv_subst, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_base Prf.hyp0)
  · simp only [Fm.subst_imp, Cover_subst, Inv_subst, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `thm:power-cover` for two generators and every exponent: with `(d₀, d₁) = st k x`,
`d₀ f₀^(k+1) + d₁ f₁^(k+1) = 1`. -/
theorem power_cover {x : PTm n} (hu : Γ ⊢[PRAAx] Cover x) (k : PTm n) :
    Γ ⊢[PRAAx] Inv (st k x) x k := by
  have h := inst (Γ := Γ) cov₀ (![k, x] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Cover_subst, Inv_subst, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h
  exact .impE h hu

end LeanProofs.IPRA.Geometry.PowerCover
