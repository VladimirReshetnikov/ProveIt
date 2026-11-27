import IPRADerivations.Geometry.LocalizationWitness

/-!
# The power-cover constructor for three generators and every exponent

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (`thm:power-cover`, three
generators). As in `Geometry/PowerCover`: the generators `f₀, f₁, f₂` are natural numbers, the
coefficients are integers, and everything is read from one parameter code
`x = ⟨⟨c₀, ⟨c₁, c₂⟩⟩, ⟨f₀, ⟨f₁, f₂⟩⟩⟩`, each `cᵢ` a pair of natural numbers. The coefficient
triple is a state `st k x` with `st 0 x = (c₀, c₁, c₂)`, updated by `cover_step₃`.

* `power_cover₃`: if `c₀ f₀ + c₁ f₁ + c₂ f₂ = 1`, then for every `k`
  `d₀ f₀^(k+1) + d₁ f₁^(k+1) + d₂ f₂^(k+1) = 1` with `(d₀, d₁, d₂) = st k x`, by quantifier-free
  induction on `k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PowerCover3

open_ipra
open LeanProofs.IPRA.Geometry.LocalizationWitness (bucket cover_step₃)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Reading a state and a parameter code -/

/-- Coefficients of a state `⟨⟨a, b⟩, ⟨⟨c, e⟩, ⟨g, h⟩⟩⟩`: `a − b`, `c − e`, `g − h`. -/
def D0 {n : ℕ} (s : PTm n) : ZT n := ⟨fstT (fstT s), sndT (fstT s)⟩
def D1 {n : ℕ} (s : PTm n) : ZT n := ⟨fstT (fstT (sndT s)), sndT (fstT (sndT s))⟩
def D2 {n : ℕ} (s : PTm n) : ZT n := ⟨fstT (sndT (sndT s)), sndT (sndT (sndT s))⟩
def C0 {n : ℕ} (x : PTm n) : ZT n := D0 (fstT x)
def C1 {n : ℕ} (x : PTm n) : ZT n := D1 (fstT x)
def C2 {n : ℕ} (x : PTm n) : ZT n := D2 (fstT x)
/-- The generators, as natural-number terms. -/
def g0 {n : ℕ} (x : PTm n) : PTm n := fstT (sndT x)
def g1 {n : ℕ} (x : PTm n) : PTm n := fstT (sndT (sndT x))
def g2 {n : ℕ} (x : PTm n) : PTm n := sndT (sndT (sndT x))

/-- `Xᵢ = dᵢ fᵢ fᵢ^k`. -/
def X0 {n : ℕ} (s x k : PTm n) : ZT n := D0 s * (ZT.ofNat (g0 x) * ZT.ofNat (pw (g0 x) k))
def X1 {n : ℕ} (s x k : PTm n) : ZT n := D1 s * (ZT.ofNat (g1 x) * ZT.ofNat (pw (g1 x) k))
def X2 {n : ℕ} (s x k : PTm n) : ZT n := D2 s * (ZT.ofNat (g2 x) * ZT.ofNat (pw (g2 x) k))
/-- `u = ∑ cᵢ fᵢ`. -/
def U {n : ℕ} (x : PTm n) : ZT n :=
  C0 x * ZT.ofNat (g0 x) + C1 x * ZT.ofNat (g1 x) + C2 x * ZT.ofNat (g2 x)

/-- The update of `cover_step₃`. -/
def NX0 {n : ℕ} (s x k : PTm n) : ZT n :=
  bucket (D0 s) (C0 x) (ZT.ofNat (pw (g0 x) k)) (X0 s x k) (X1 s x k) (X2 s x k) (U x)
def NX1 {n : ℕ} (s x k : PTm n) : ZT n :=
  bucket (D1 s) (C1 x) (ZT.ofNat (pw (g1 x) k)) (X1 s x k) (X0 s x k) (X2 s x k) (U x)
def NX2 {n : ℕ} (s x k : PTm n) : ZT n :=
  bucket (D2 s) (C2 x) (ZT.ofNat (pw (g2 x) k)) (X2 s x k) (X0 s x k) (X1 s x k) (U x)

section Subst

variable {m : ℕ} (σ : Fin n → PTm m)

@[simp] theorem D0_subst (s : PTm n) : (D0 s).subst σ = D0 (Syn.subst σ s) := by simp [D0, ZT.subst]
@[simp] theorem D1_subst (s : PTm n) : (D1 s).subst σ = D1 (Syn.subst σ s) := by simp [D1, ZT.subst]
@[simp] theorem D2_subst (s : PTm n) : (D2 s).subst σ = D2 (Syn.subst σ s) := by simp [D2, ZT.subst]
@[simp] theorem C0_subst (x : PTm n) : (C0 x).subst σ = C0 (Syn.subst σ x) := by simp [C0]
@[simp] theorem C1_subst (x : PTm n) : (C1 x).subst σ = C1 (Syn.subst σ x) := by simp [C1]
@[simp] theorem C2_subst (x : PTm n) : (C2 x).subst σ = C2 (Syn.subst σ x) := by simp [C2]
@[simp] theorem g0_subst (x : PTm n) : Syn.subst σ (g0 x) = g0 (Syn.subst σ x) := by simp [g0]
@[simp] theorem g1_subst (x : PTm n) : Syn.subst σ (g1 x) = g1 (Syn.subst σ x) := by simp [g1]
@[simp] theorem g2_subst (x : PTm n) : Syn.subst σ (g2 x) = g2 (Syn.subst σ x) := by simp [g2]
@[simp] theorem X0_subst (s x k : PTm n) :
    (X0 s x k).subst σ = X0 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [X0]
@[simp] theorem X1_subst (s x k : PTm n) :
    (X1 s x k).subst σ = X1 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [X1]
@[simp] theorem X2_subst (s x k : PTm n) :
    (X2 s x k).subst σ = X2 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [X2]
@[simp] theorem U_subst (x : PTm n) : (U x).subst σ = U (Syn.subst σ x) := by simp [U]
@[simp] theorem bucket_subst (d c P X Xa Xb u : ZT n) :
    (bucket d c P X Xa Xb u).subst σ =
      bucket (d.subst σ) (c.subst σ) (P.subst σ) (X.subst σ) (Xa.subst σ) (Xb.subst σ) (u.subst σ) := by
  simp [bucket]
@[simp] theorem NX0_subst (s x k : PTm n) :
    (NX0 s x k).subst σ = NX0 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [NX0]
@[simp] theorem NX1_subst (s x k : PTm n) :
    (NX1 s x k).subst σ = NX1 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [NX1]
@[simp] theorem NX2_subst (s x k : PTm n) :
    (NX2 s x k).subst σ = NX2 (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [NX2]

end Subst

/-! ## The coefficient sequence -/

/-- The step; variables `0 = k`, `1 = st k`, `2 = x`. -/
def stepT : PTm 3 :=
  pairT (pairT (NX0 (var 1) (var 2) (var 0)).pos (NX0 (var 1) (var 2) (var 0)).neg)
    (pairT (pairT (NX1 (var 1) (var 2) (var 0)).pos (NX1 (var 1) (var 2) (var 0)).neg)
      (pairT (NX2 (var 1) (var 2) (var 0)).pos (NX2 (var 1) (var 2) (var 0)).neg))

abbrev stF : PR 2 := rec2 (fstT (var 0)) stepT

/-- The coefficient state after `k` steps. -/
abbrev st {n : ℕ} (k x : PTm n) : PTm n := ap2 stF k x

theorem st_zero (x : PTm n) : Γ ⊢[PRAAx] st zero x ≐ fstT x := by
  have h := rec2_zero (Γ := Γ) (fstT (var 0)) stepT x
  simpa using h

theorem stepT_subst (k s x : PTm n) :
    Syn.subst ![k, s, x] stepT =
      pairT (pairT (NX0 s x k).pos (NX0 s x k).neg)
        (pairT (pairT (NX1 s x k).pos (NX1 s x k).neg) (pairT (NX2 s x k).pos (NX2 s x k).neg)) := by
  have e₀ : (NX0 (var 1) (var 2) (var 0) : ZT 3).subst ![k, s, x] = NX0 s x k := by simp
  have e₁ : (NX1 (var 1) (var 2) (var 0) : ZT 3).subst ![k, s, x] = NX1 s x k := by simp
  have e₂ : (NX2 (var 1) (var 2) (var 0) : ZT 3).subst ![k, s, x] = NX2 s x k := by simp
  simp only [stepT, subst_pairT]
  rw [← e₀, ← e₁, ← e₂]
  rfl

theorem st_succ (k x : PTm n) :
    Γ ⊢[PRAAx] st (succ k) x ≐
      pairT (pairT (NX0 (st k x) x k).pos (NX0 (st k x) x k).neg)
        (pairT (pairT (NX1 (st k x) x k).pos (NX1 (st k x) x k).neg)
          (pairT (NX2 (st k x) x k).pos (NX2 (st k x) x k).neg)) := by
  have h := rec2_succ (Γ := Γ) (fstT (var 0)) stepT k x
  rw [stepT_subst] at h
  exact h

/-! ## Evaluations of the state -/

section Eval

variable {s a b c e g h : PTm n}

theorem toZ_D0_of (hs : Γ ⊢[PRAAx] s ≐ pairT (pairT a b) (pairT (pairT c e) (pairT g h))) :
    ZT.toZ Γ (D0 s) = Groth.ι (Q.mk Γ a) - Groth.ι (Q.mk Γ b) := by
  have ha := natEq ((congrFst (congrFst hs)).eqTrans (fst_pair _ _).fstE)
  have hb := natEq ((congrSnd (congrFst hs)).eqTrans (fst_pair _ _).sndE)
  show Groth.ι (Q.mk Γ (fstT (fstT s))) - Groth.ι (Q.mk Γ (sndT (fstT s))) = _
  rw [ha, hb]

theorem toZ_D1_of (hs : Γ ⊢[PRAAx] s ≐ pairT (pairT a b) (pairT (pairT c e) (pairT g h))) :
    ZT.toZ Γ (D1 s) = Groth.ι (Q.mk Γ c) - Groth.ι (Q.mk Γ e) := by
  have m : Γ ⊢[PRAAx] fstT (sndT s) ≐ pairT c e :=
    (congrFst (congrSnd hs)).eqTrans (snd_pair _ _).fstE
  have hc := natEq m.fstE
  have he := natEq m.sndE
  show Groth.ι (Q.mk Γ (fstT (fstT (sndT s)))) - Groth.ι (Q.mk Γ (sndT (fstT (sndT s)))) = _
  rw [hc, he]

theorem toZ_D2_of (hs : Γ ⊢[PRAAx] s ≐ pairT (pairT a b) (pairT (pairT c e) (pairT g h))) :
    ZT.toZ Γ (D2 s) = Groth.ι (Q.mk Γ g) - Groth.ι (Q.mk Γ h) := by
  have m : Γ ⊢[PRAAx] sndT (sndT s) ≐ pairT g h :=
    (congrSnd (congrSnd hs)).eqTrans (snd_pair _ _).sndE
  show Groth.ι (Q.mk Γ (fstT (sndT (sndT s)))) - Groth.ι (Q.mk Γ (sndT (sndT (sndT s)))) = _
  rw [natEq m.fstE, natEq m.sndE]

end Eval

theorem toZ_D0_succ (k x : PTm n) :
    ZT.toZ Γ (D0 (st (succ k) x)) = ZT.toZ Γ (NX0 (st k x) x k) := toZ_D0_of (st_succ k x)
theorem toZ_D1_succ (k x : PTm n) :
    ZT.toZ Γ (D1 (st (succ k) x)) = ZT.toZ Γ (NX1 (st k x) x k) := toZ_D1_of (st_succ k x)
theorem toZ_D2_succ (k x : PTm n) :
    ZT.toZ Γ (D2 (st (succ k) x)) = ZT.toZ Γ (NX2 (st k x) x k) := toZ_D2_of (st_succ k x)

theorem toZ_D0_zero (x : PTm n) : ZT.toZ Γ (D0 (st zero x)) = ZT.toZ Γ (C0 x) := by
  have z := st_zero (Γ := Γ) x
  have ha := natEq (congrFst (congrFst z)); have hb := natEq (congrSnd (congrFst z))
  show Groth.ι (Q.mk Γ (fstT (fstT (st zero x)))) - Groth.ι (Q.mk Γ (sndT (fstT (st zero x)))) =
    Groth.ι (Q.mk Γ (fstT (fstT (fstT x)))) - Groth.ι (Q.mk Γ (sndT (fstT (fstT x))))
  rw [ha, hb]

theorem toZ_D1_zero (x : PTm n) : ZT.toZ Γ (D1 (st zero x)) = ZT.toZ Γ (C1 x) := by
  have z := st_zero (Γ := Γ) x
  have ha := natEq (congrFst (congrFst (congrSnd z))); have hb := natEq (congrSnd (congrFst (congrSnd z)))
  show Groth.ι (Q.mk Γ (fstT (fstT (sndT (st zero x))))) - Groth.ι (Q.mk Γ (sndT (fstT (sndT (st zero x))))) =
    Groth.ι (Q.mk Γ (fstT (fstT (sndT (fstT x))))) - Groth.ι (Q.mk Γ (sndT (fstT (sndT (fstT x)))))
  rw [ha, hb]

theorem toZ_D2_zero (x : PTm n) : ZT.toZ Γ (D2 (st zero x)) = ZT.toZ Γ (C2 x) := by
  have z := st_zero (Γ := Γ) x
  have ha := natEq (congrFst (congrSnd (congrSnd z))); have hb := natEq (congrSnd (congrSnd (congrSnd z)))
  show Groth.ι (Q.mk Γ (fstT (sndT (sndT (st zero x))))) - Groth.ι (Q.mk Γ (sndT (sndT (sndT (st zero x))))) =
    Groth.ι (Q.mk Γ (fstT (sndT (sndT (fstT x))))) - Groth.ι (Q.mk Γ (sndT (sndT (sndT (fstT x)))))
  rw [ha, hb]

/-! ## The invariant -/

/-- `d₀ f₀^(k+1) + d₁ f₁^(k+1) + d₂ f₂^(k+1) = 1` for the state `s`. -/
def Inv {n : ℕ} (s x k : PTm n) : Fm PTm n :=
  ZT.eq (X0 s x k + X1 s x k + X2 s x k) (ZT.natLit 1)

/-- The cover certificate `c₀ f₀ + c₁ f₁ + c₂ f₂ = 1`. -/
def Cover {n : ℕ} (x : PTm n) : Fm PTm n := ZT.eq (U x) (ZT.natLit 1)

theorem inv_base {x : PTm n} (hu : Γ ⊢[PRAAx] Cover x) : Γ ⊢[PRAAx] Inv (st zero x) x zero := by
  have eu := ZT.toZ_eq hu
  have p₀ := natEq (pw_zero (Γ := Γ) (g0 x)); have p₁ := natEq (pw_zero (Γ := Γ) (g1 x))
  have p₂ := natEq (pw_zero (Γ := Γ) (g2 x))
  unfold Inv
  apply ZT.derive
  simp only [U, X0, X1, X2] at eu ⊢
  ipra_simps
  rw [toZ_D0_zero, toZ_D1_zero, toZ_D2_zero, p₀, p₁, p₂]
  linear_combination eu

theorem inv_step {x k : PTm n} (hu : Γ ⊢[PRAAx] Cover x) (ih : Γ ⊢[PRAAx] Inv (st k x) x k) :
    Γ ⊢[PRAAx] Inv (st (succ k) x) x (succ k) := by
  have e := ZT.toZ_eq (cover_step₃ (P₀ := ZT.ofNat (pw (g0 x) k)) (P₁ := ZT.ofNat (pw (g1 x) k))
    (P₂ := ZT.ofNat (pw (g2 x) k)) (d₀ := D0 (st k x)) (d₁ := D1 (st k x)) (d₂ := D2 (st k x)) hu ih)
  have p₀ := natEq (pw_succ (Γ := Γ) (g0 x) k); have p₁ := natEq (pw_succ (Γ := Γ) (g1 x) k)
  have p₂ := natEq (pw_succ (Γ := Γ) (g2 x) k)
  unfold Inv
  apply ZT.derive
  simp only [X0, X1, X2, ZT.toZ_add, ZT.toZ_mul, toZ_D0_succ, toZ_D1_succ, toZ_D2_succ]
  simp only [NX0, NX1, NX2, X0, X1, X2, U, bucket] at e ⊢
  ipra_simps
  rw [p₀, p₁, p₂]
  linear_combination e

/-- Variables: `0 = k` (induction), `1 = x`. -/
private abbrev covF : Fm PTm 2 := Cover (var 1) ⟶ Inv (st (var 0) (var 1)) (var 1) (var 0)

theorem Cover_subst {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    (Cover x).subst σ = Cover (Syn.subst σ x) := by simp [Cover]

theorem Inv_subst {m : ℕ} (σ : Fin n → PTm m) (s x k : PTm n) :
    (Inv s x k).subst σ = Inv (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ k) := by simp [Inv]

private theorem cov₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] covF := by
  ipra_ind (⟨trivial, trivial⟩) [Cover_subst, Inv_subst, subst_ap2]
  · exact .impI (inv_base Prf.hyp0)
  · exact .impI (inv_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `thm:power-cover` for three generators and every exponent. -/
theorem power_cover₃ {x : PTm n} (hu : Γ ⊢[PRAAx] Cover x) (k : PTm n) :
    Γ ⊢[PRAAx] Inv (st k x) x k := by
  have h := inst (Γ := Γ) cov₀ (![k, x] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Cover_subst, Inv_subst, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h
  exact .impE h hu

end LeanProofs.IPRA.Geometry.PowerCover3
