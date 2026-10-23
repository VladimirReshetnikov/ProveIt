import DiophantineConsistency.RatioReparameterization

/-! # Package 52's exact numerical ratio interface -/

namespace DiophantineConsistency.NativeNineRatio52

open Jones1982

/-- The six remaining ratio witnesses; the new j may be zero. -/
structure NewVars where
  h : ℕ
  s : ℕ
  w : ℕ
  phi : ℕ
  i : ℕ
  j : ℕ
  deriving DecidableEq, Repr

namespace NewVars

def old (v : NewVars) (R N b g cap jOld : ℕ) : Nine.Vars :=
  Nine.Vars.ofNat R N b g cap v.h v.s v.w v.phi v.i jOld

/-- Every non-j register is taken literally from the existing ratio interface. -/
def base (v : NewVars) (R N b g cap : ℕ) : Nine.Vars := v.old R N b g cap 0

def Hnew (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  RatioReparameterization.newH u.B' u.C u.F v.j

def Inew (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  (u.Gp ^ 2 - 1) * (v.Hnew R N b g cap) ^ 2 + 1

def margin (v : NewVars) (R N b g cap : ℕ) : ℤ :=
  let u := v.base R N b g cap
  u.K ^ 2 * u.G - 4 * (u.C - u.K * u.Y) ^ 2 * u.G - 8 * u.g * u.K ^ 2

/-- The four conditions after the exact H reparameterization. -/
def Conditions (v : NewVars) (R N b g cap : ℕ) : Prop :=
  let u := v.base R N b g cap
  IsSquare ((u.P ^ 2 - 1) * u.K ^ 2 + 1) ∧
    IsSquare (u.D * u.F * v.Inew R N b g cap) ∧ u.J ∣ u.Q ∧
      0 < v.margin R N b g cap

/-- Explicit old positive index, not a selected existential witness. -/
def toOldIndex (v : NewVars) (R N b g cap : ℕ) : ℕ :=
  let u := v.base R N b g cap
  RatioReparameterization.oldIndex u.B' u.C u.F v.j

end NewVars

theorem register_bounds {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hs : 0 < v.s) (hw : 0 < v.w) :
    let u := v.base R N b g cap
    0 < u.B' ∧ u.B' < u.C ∧ 0 < u.F := by
  let u := v.base R N b g cap
  change 0 < u.B' ∧ u.B' < u.C ∧ 0 < u.F
  have hB : 0 < u.B' := by
    change 0 < 2 * (R : ℤ) + 1
    positivity
  have hBC : u.B' < u.C := by
    change 2 * (R : ℤ) + 1 < 2 * (R : ℤ) + 1 + (b : ℤ) * v.w + v.phi
    have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb
    have hwZ : 0 < (v.w : ℤ) := by exact_mod_cast hw
    nlinarith only [mul_pos hbZ hwZ, Int.natCast_nonneg v.phi]
  have hA : 2 ≤ u.A := by
    have hsz := (Nine.sizes_nat hR hN hs hw).2
    change 2 ≤ (Nine.Vars.ofNat R N b g cap v.h v.s v.w v.phi v.i 0).A
    rw [Nine.cA]
    exact_mod_cast hsz
  have hF : 0 < u.F := by
    change 0 < (u.A ^ 2 - 1) * u.E ^ 2 + 1
    have hAm : 0 ≤ u.A ^ 2 - 1 := by nlinarith only [hA]
    nlinarith only [mul_nonneg hAm (sq_nonneg u.E)]
  exact ⟨hB, hBC, hF⟩

/-- The old and new j parametrizations preserve all four ratio conditions. -/
theorem exists_conditions_iff {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hs : 0 < v.s) (hw : 0 < v.w) :
    (∃ jOld : ℕ, 0 < jOld ∧ (v.old R N b g cap jOld).Conds) ↔
      ∃ jNew : ℕ, ({v with j := jNew}).Conditions R N b g cap := by
  let u := v.base R N b g cap
  let sq0 := IsSquare ((u.P ^ 2 - 1) * u.K ^ 2 + 1)
  let p : ℤ → Prop := fun H => IsSquare (u.D * u.F * ((u.Gp ^ 2 - 1) * H ^ 2 + 1))
  let m := v.margin R N b g cap
  obtain ⟨hB, hBC, hF⟩ := register_bounds v hR hN hb hs hw
  obtain ⟨hJF, hCF⟩ := RatioReparameterization.vars_F_congruences u
  have hequiv := RatioReparameterization.exists_old_iff_new (Q := u.Q) p hB hBC hF hJF hCF
  constructor
  · rintro ⟨jOld, hj, hc⟩
    change sq0 ∧ p (RatioReparameterization.oldH u.B' u.C jOld) ∧
      u.J * u.F ∣ u.Q * u.F + u.J * (RatioReparameterization.oldH u.B' u.C jOld - u.C) ∧
        0 < m at hc
    obtain ⟨ha, hp, hd, hm⟩ := hc
    obtain ⟨hJQ, jNew, hpNew⟩ := hequiv.mp ⟨jOld, by omega, hp, hd⟩
    refine ⟨jNew, ?_⟩
    change sq0 ∧ p (RatioReparameterization.newH u.B' u.C u.F jNew) ∧ u.J ∣ u.Q ∧ 0 < m
    exact ⟨ha, hpNew, hJQ, hm⟩
  · rintro ⟨jNew, hc⟩
    change sq0 ∧ p (RatioReparameterization.newH u.B' u.C u.F jNew) ∧ u.J ∣ u.Q ∧
      0 < m at hc
    obtain ⟨ha, hp, hd, hm⟩ := hc
    obtain ⟨jOld, hj, hpOld, hdOld⟩ := hequiv.mpr ⟨hd, jNew, hp⟩
    refine ⟨jOld, by omega, ?_⟩
    change sq0 ∧ p (RatioReparameterization.oldH u.B' u.C jOld) ∧
      u.J * u.F ∣ u.Q * u.F + u.J * (RatioReparameterization.oldH u.B' u.C jOld - u.C) ∧
        0 < m
    exact ⟨ha, hpOld, hdOld, hm⟩

/-- The explicit reverse index is positive and preserves the actual H register. -/
theorem toOldIndex_correct {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hs : 0 < v.s) (hw : 0 < v.w) :
    0 < v.toOldIndex R N b g cap ∧
      (v.old R N b g cap (v.toOldIndex R N b g cap)).H = v.Hnew R N b g cap := by
  obtain ⟨hB, hBC, hF⟩ := register_bounds v hR hN hb hs hw
  have hCF := (RatioReparameterization.vars_F_congruences (v.base R N b g cap)).2
  obtain ⟨hj, heq⟩ := RatioReparameterization.oldIndex_correct hB (by omega) hF hCF v.j
  have hj' : 0 < RatioReparameterization.oldIndex (v.base R N b g cap).B'
      (v.base R N b g cap).C (v.base R N b g cap).F v.j := by omega
  exact ⟨hj', heq.symm⟩

/-- Sufficiency with a genuinely nonnegative new j and the existing numerical
ratio conclusion. No source-compiler premise is assumed. -/
theorem ratio_sound_new {R N b g cap : ℕ} (v : NewVars)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hcap : 0 < cap) (hh : 0 < v.h) (hs : 0 < v.s) (hw : 0 < v.w) (hi : 0 < v.i)
    (hc : v.Conditions R N b g cap) :
    N ^ 2 ∣ (2 * R).choose R ∧ (∃ k, b = 2 ^ k) ∧ 8 * g < cap := by
  have hnew : ∃ jNew : ℕ, ({v with j := jNew}).Conditions R N b g cap :=
    ⟨v.j, by simpa using hc⟩
  obtain ⟨jOld, hjOld, hcOld⟩ := (exists_conditions_iff v hR hN hb hs hw).mpr hnew
  exact Nine.ratio_sound hR hN hbR hb hbN hcap hh hs hw hi hjOld hcOld

/-- Necessity supplies all six natural witnesses with no positivity condition
on the new j. The completeness margin remains the exact `32*g<cap`. -/
theorem ratio_complete_new {R N b g cap : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hgcap : 32 * g < cap) (hdvd : N ^ 2 ∣ (2 * R).choose R)
    (hpow : ∃ k, b = 2 ^ k) :
    ∃ v : NewVars, 0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.i ∧ v.Conditions R N b g cap := by
  obtain ⟨h, s, w, phi, i, jOld, hh, hs, hw, hi, hjOld, hcOld⟩ :=
    Nine.ratio_complete hR hN hbR hb hbN hgcap hdvd hpow
  let v : NewVars := ⟨h, s, w, phi, i, 0⟩
  have hold : ∃ jOld : ℕ, 0 < jOld ∧ (v.old R N b g cap jOld).Conds :=
    ⟨jOld, hjOld, hcOld⟩
  obtain ⟨jNew, hcNew⟩ := (exists_conditions_iff v hR hN hb hs hw).mp hold
  exact ⟨{v with j := jNew}, hh, hs, hw, hi, hcNew⟩

end DiophantineConsistency.NativeNineRatio52
