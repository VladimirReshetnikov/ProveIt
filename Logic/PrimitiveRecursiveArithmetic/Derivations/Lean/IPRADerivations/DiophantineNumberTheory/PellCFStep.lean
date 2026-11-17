import IPRADerivations.DiophantineNumberTheory.SquareArea
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Combinatorics.Binomial
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Combinatorics.Bell
import IPRADerivations.Core.BlockSum

/-!
# Reduced states of the continued fraction of `√D`

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Section "A finite continued-fraction theory",
Lemma `lem:reduced` (closure). Let `a = ⌊√D⌋` with `D` not a square, i.e. `a² < D < (a + 1)²`. A reduced
state is a pair `(m, d)` with (all comparisons with the irrational `s = √D` cleared into integer squares)
  `m ≤ a`, `1 ≤ d ≤ 2a`, `m² ≤ D`, `d ∣ D − m²`, `D < (d + m)²` (`s − m < d`), `(d ∸ m)² < D` (`d < s + m`).
Its digit and successor are `c = ⌊(a + m)/d⌋`, `m' = dc − m`, `d' = (D − m'²)/d` (`eq:cfstep`).

* `step_closure` (`lem:reduced`, closure): the successor of a reduced state is reduced, and the step is
  exact: `d c = m' + m` and `D = m'² + d d'` (no truncation occurs);
* `start_reduced`: from `(m₀, d₀) = (0, 1)` the step gives `c₀ = a`, `(m₁, d₁) = (a, D − a²)`, which is
  reduced, again with exact step equations.
* `pred_recover`, `step_injective` (`lem:reduced`, injectivity): a reduced state is recovered from its
  successor, `m = a − ((a + m') mod d)` and `d = (D − m'²)/d'`, so the step is injective on reduced states.

The proof follows the packet with `t = (a + m) mod d`: `c ≥ 1` (since `d ≤ a + m`), `t ≤ a`,
`m' = a − t ≤ a`, `d ∣ D − m'²` with quotient `e + 2cm − dc²`, and the two new boundary inequalities
are `d < d' + 2m'` and `d' < d + 2m'`, obtained from `d ∸ m' ≤ m` and `d + m' ≥ a + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellCFStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.SquareArea (le_add_mono)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (quo_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Order helpers -/

theorem lt_of_sq_lt {x y : PTm n} (h : Γ ⊢[PRAAx] lt (x * x) (y * y)) : Γ ⊢[PRAAx] lt x y := by
  refine .orE (lt_or_le x y) Prf.hyp0 ?_
  exact not_succ_le_self _ _ (le_trans h.wk (le_mul_mono Prf.hyp0 Prf.hyp0))

theorem le_of_lt_succ' {x y : PTm n} (h : Γ ⊢[PRAAx] lt x (succ y)) : Γ ⊢[PRAAx] le x y :=
  (succ_monus_succ _ _).eqSymm.eqTrans h

theorem pos_of_le_one {d : PTm n} (h : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] d ≐ succ (pred d) := by
  refine .orE (zero_or_succ d) ?_ Prf.hyp0
  exact not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 h.wk)

theorem one_le_of_pos {d : PTm n} (h : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] le one d :=
  le_of_eq_add (d := pred d) (by have e := natEq h; apply deriveNat; ipra_simps; linear_combination e)

/-- `a ≤ b + (a ∸ b)`. -/
theorem le_add_monus_l (a b : PTm n) : Γ ⊢[PRAAx] le a (b + monus a b) := by
  have m := natEq (monus_max (Γ := Γ) a b)
  refine le_of_eq_add (d := monus b a) ?_
  apply deriveNat; ipra_simps
  linear_combination m

/-- `x ≤ a` gives `x² < D` when `a² < D`. -/
theorem sq_lt_of_le {x a D : PTm n} (hA : Γ ⊢[PRAAx] lt (a * a) D) (h : Γ ⊢[PRAAx] le x a) :
    Γ ⊢[PRAAx] lt (x * x) D :=
  lt_of_le_of_lt (le_mul_mono h h) hA

/-- `D < (a + 1)²` and `y² < D` give `y ≤ a`. -/
theorem le_of_sq_lt {y a D : PTm n} (hB : Γ ⊢[PRAAx] lt D (succ a * succ a)) (h : Γ ⊢[PRAAx] lt (y * y) D) :
    Γ ⊢[PRAAx] le y a :=
  le_of_lt_succ' (lt_of_sq_lt (lt_of_lt_of_le h (le_of_lt hB)))

/-- `a + 1 ≤ y` gives `D < y²` when `D < (a + 1)²`. -/
theorem lt_sq_of_ge {y a D : PTm n} (hB : Γ ⊢[PRAAx] lt D (succ a * succ a)) (h : Γ ⊢[PRAAx] le (succ a) y) :
    Γ ⊢[PRAAx] lt D (y * y) :=
  lt_of_lt_of_le hB (le_mul_mono h h)

/-- The quotient and remainder by a positive `d`: `a = c d + t`, `t < d`. -/
theorem div_split (x : PTm n) {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] (quo x d * d + rem x d ≐ x) ⋏ lt (rem x d) d := by
  have dm := div_mod (Γ := Γ) x (pred d)
  have q : Γ ⊢[PRAAx] quo x d ≐ quo x (succ (pred d)) := congrAp2 quoF (.eqRefl _) hd
  have r : Γ ⊢[PRAAx] rem x d ≐ rem x (succ (pred d)) := congrAp2 remF (.eqRefl _) hd
  refine .andI ?_ (lt_congr r.eqSymm hd.eqSymm (Prf.andE₂ dm))
  have a := natEq (Prf.andE₁ dm); have b := natEq q; have c := natEq r; have k := natEq hd
  apply deriveNat; ipra_simps
  linear_combination -a + 𝔞 (quo x (succ (pred d))) * k + 𝔞 d * b + c

/-! ## Reduced states -/

/-- `(m, d)` is reduced for `D`, `a`. -/
abbrev Red (D a m d : PTm n) : Fm PTm n :=
  le m a ⋏ (le one d ⋏ (le d (two * a) ⋏ (le (m * m) D ⋏ (dvd d (monus D (m * m)) ⋏
    (lt D ((d + m) * (d + m)) ⋏ lt (monus d m * monus d m) D)))))

/-- The digit `c = ⌊(a + m)/d⌋`. -/
abbrev cD (a m d : PTm n) : PTm n := quo (a + m) d
/-- `m' = d c − m`. -/
abbrev mS (a m d : PTm n) : PTm n := monus (d * cD a m d) m
/-- `d' = (D − m'²)/d`. -/
abbrev dS (D a m d : PTm n) : PTm n := quo (monus D (mS a m d * mS a m d)) d

section Closure

variable {D a m d : PTm n}

/-- `lem:reduced` (closure): the successor of a reduced state is reduced, with exact step equations. -/
theorem step_closure (hA : Γ ⊢[PRAAx] lt (a * a) D) (hB : Γ ⊢[PRAAx] lt D (succ a * succ a))
    (hR : Γ ⊢[PRAAx] Red D a m d) :
    Γ ⊢[PRAAx] Red D a (mS a m d) (dS D a m d) ⋏
      ((d * cD a m d ≐ mS a m d + m) ⋏ (D ≐ mS a m d * mS a m d + d * dS D a m d)) := by
  have hm := Prf.andE₁ hR
  have hd1 := Prf.andE₁ (Prf.andE₂ hR)
  have hmD := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hR)))
  have hdv := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hR))))
  have hR2 := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hR)))))
  have hd := pos_of_le_one hd1
  -- `D = m² + d e`.
  have De : Γ ⊢[PRAAx] D ≐ m * m + d * quo (monus D (m * m)) d :=
    (eq_add_of_le hmD).eqTrans (congrAdd (.eqRefl _) (DiophantineNumberTheory.Coprime.eq_of_dvd' hd hdv))
  -- `a + m = c d + t`, `t < d`.
  have dv := div_split (a + m) hd
  have eDiv := Prf.andE₁ dv
  have htd := Prf.andE₂ dv
  -- `d ≤ a + m`.
  have hdam : Γ ⊢[PRAAx] le d (a + m) := by
    have u : Γ ⊢[PRAAx] le (monus d m) a := le_of_sq_lt hB hR2
    refine le_trans (le_add_monus_l d m) ?_
    exact le_congr (add_comm _ _) (.eqRefl _) (add_le_add_right m u)
  -- `c ≥ 1`.
  have hc : Γ ⊢[PRAAx] cD a m d ≐ succ (pred (cD a m d)) := by
    refine .orE (zero_or_succ (cD a m d)) ?_ Prf.hyp0
    let C := (cD a m d ≐ zero) :: Γ
    have e : C ⊢[PRAAx] rem (a + m) d ≐ a + m := by
      have x := natEq (eDiv.wk : C ⊢[PRAAx] _); have z := natEq (Prf.hyp0 : C ⊢[PRAAx] _)
      apply deriveNat; ipra_simps; linear_combination x - 𝔞 d * z
    exact le_lt_absurd _ hdam.wk (lt_congr e (.eqRefl _) htd.wk)
  -- `d + t ≤ a + m`.
  have hdt : Γ ⊢[PRAAx] le (rem (a + m) d + d) (a + m) := by
    refine le_of_eq_add (d := pred (cD a m d) * d) ?_
    have x := natEq eDiv; have z := natEq hc
    apply deriveNat; ipra_simps; linear_combination -x + 𝔞 d * z
  -- `t ≤ a`.
  have hta : Γ ⊢[PRAAx] le (rem (a + m) d) a := by
    refine .orE (le_total d m) ?_ ?_
    · exact le_trans (le_of_lt htd.wk) (le_trans Prf.hyp0 hm.wk)
    · refine le_of_add_le_add_right (c := d) (le_trans hdt.wk ?_)
      exact le_congr (.eqRefl _) (.eqRefl _) (le_add_mono (le_refl a) Prf.hyp0)
  -- `m' = a − t` and `d c = m' + m`.
  have eA := eq_add_of_le hta
  have hdc : Γ ⊢[PRAAx] d * cD a m d ≐ monus a (rem (a + m) d) + m := by
    have x := natEq eDiv; have y := natEq eA
    apply deriveNat; ipra_simps; linear_combination x + y
  have hmS : Γ ⊢[PRAAx] mS a m d ≐ monus a (rem (a + m) d) :=
    (congrMonus hdc (.eqRefl _)).eqTrans (add_monus _ _)
  have ex1 : Γ ⊢[PRAAx] d * cD a m d ≐ mS a m d + m := hdc.eqTrans (congrAdd hmS.eqSymm (.eqRefl _))
  have hmSa : Γ ⊢[PRAAx] le (mS a m d) a :=
    le_congr hmS.eqSymm (.eqRefl _) (le_of_eq_add (d := rem (a + m) d) (eA.eqTrans (add_comm _ _)))
  have hmSD : Γ ⊢[PRAAx] lt (mS a m d * mS a m d) D := sq_lt_of_le hA hmSa
  -- `D = m'² + d k'` with `k' = (e + 2cm) − d c²`.
  have hle : Γ ⊢[PRAAx] le (d * cD a m d * cD a m d)
      (quo (monus D (m * m)) d + two * cD a m d * m) := by
    refine le_cancel_pos hd ?_
    have base : Γ ⊢[PRAAx] le (mS a m d * mS a m d + (two * (mS a m d * m) + m * m))
        (D + (two * (mS a m d * m) + m * m)) := add_le_add_right _ (le_of_lt hmSD)
    refine le_congr ?_ ?_ base
    · have x := natEq ex1
      apply deriveNat; ipra_simps
      linear_combination -(𝔞 d * 𝔞 (cD a m d) + 𝔞 (mS a m d) + 𝔞 m) * x
    · have x := natEq ex1; have y := natEq De
      apply deriveNat; ipra_simps
      linear_combination y - 2 * 𝔞 m * x
  have eK := eq_add_of_le hle
  have Dk : Γ ⊢[PRAAx] D ≐ mS a m d * mS a m d + d * monus (quo (monus D (m * m)) d + two * cD a m d * m)
      (d * cD a m d * cD a m d) := by
    have x := natEq ex1; have y := natEq De; have z := natEq eK
    apply deriveNat; ipra_simps
    linear_combination y + 𝔞 d * z + (𝔞 d * 𝔞 (cD a m d) + 𝔞 (mS a m d) + 𝔞 m - 2 * 𝔞 m) * x
  have hdS : Γ ⊢[PRAAx] dS D a m d ≐ monus (quo (monus D (m * m)) d + two * cD a m d * m) (d * cD a m d * cD a m d) :=
    quo_of_eq hd ((congrMonus Dk (.eqRefl _)).eqTrans (add_monus' _ _))
  have ex2 : Γ ⊢[PRAAx] D ≐ mS a m d * mS a m d + d * dS D a m d := Dk.eqTrans (congrAdd (.eqRefl _) (congrMul (.eqRefl _) hdS.eqSymm))
  -- `d' ≥ 1`.
  have hdSp : Γ ⊢[PRAAx] dS D a m d ≐ succ (pred (dS D a m d)) := by
    refine .orE (zero_or_succ (dS D a m d)) ?_ Prf.hyp0
    let C := (dS D a m d ≐ zero) :: Γ
    have e : C ⊢[PRAAx] D ≐ mS a m d * mS a m d := by
      have x := natEq (ex2.wk : C ⊢[PRAAx] _); have z := natEq (Prf.hyp0 : C ⊢[PRAAx] _)
      apply deriveNat; ipra_simps; linear_combination x + 𝔞 d * z
    exact not_succ_le_self _ _ (le_congr (.eqRefl _) e hmSD.wk)
  -- New `R1`: `d < d' + 2 m'`, hence `D < (d' + m')²`.
  have hR1' : Γ ⊢[PRAAx] lt D ((dS D a m d + mS a m d) * (dS D a m d + mS a m d)) := by
    have key : Γ ⊢[PRAAx] lt d (dS D a m d + two * mS a m d) := by
      refine .orE (le_total d (mS a m d)) ?_ ?_
      · refine lt_of_le_of_lt Prf.hyp0 (le_of_eq_add (d := pred (dS D a m d) + mS a m d) ?_)
        have z := natEq (hdSp.wk : (le d (mS a m d) :: Γ) ⊢[PRAAx] _)
        apply deriveNat; ipra_simps; linear_combination z
      · let C := le (mS a m d) d :: Γ
        have eu := eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le (mS a m d) d)
        -- `u = d ∸ m' ≤ m`, so `u² < D`.
        have hu : C ⊢[PRAAx] le (monus d (mS a m d)) m := by
          refine le_of_add_le_add_right (c := mS a m d) ?_
          refine le_congr (a := d) (b := d * cD a m d) ?_ ?_ (le_of_eq_add (d := pred (cD a m d) * d) ?_)
          · have x := natEq eu; apply deriveNat; ipra_simps; linear_combination x
          · exact (ex1.wk : C ⊢[PRAAx] _).eqTrans (add_comm _ _)
          · have z := natEq (hc.wk : C ⊢[PRAAx] _)
            apply deriveNat; ipra_simps; linear_combination 𝔞 d * z
        have huD : C ⊢[PRAAx] lt (monus d (mS a m d) * monus d (mS a m d)) D := sq_lt_of_le hA.wk (le_trans hu hm.wk)
        refine .orE (lt_or_le (monus d (mS a m d)) (mS a m d + dS D a m d)) ?_ ?_
        · refine le_congr ?_ ?_ (add_le_add_right (mS a m d) Prf.hyp0)
          · have x := natEq (eu.wk : (lt (monus d (mS a m d)) (mS a m d + dS D a m d) :: C) ⊢[PRAAx] _)
            apply deriveNat; ipra_simps; linear_combination -x
          · apply deriveNat; ipra_simps; ring
        · let C' := le (mS a m d + dS D a m d) (monus d (mS a m d)) :: C
          have h₁ : C' ⊢[PRAAx] le (mS a m d * (mS a m d + dS D a m d)) (mS a m d * monus d (mS a m d)) :=
            le_mul_mono (le_refl _) Prf.hyp0
          have h₂ : C' ⊢[PRAAx] le (monus d (mS a m d) * (mS a m d + dS D a m d))
              (monus d (mS a m d) * monus d (mS a m d)) := le_mul_mono (le_refl _) Prf.hyp0
          have tot := le_trans (le_add_mono h₁ (le_refl (monus d (mS a m d) * dS D a m d))) (le_congr ?_ (.eqRefl _) h₂)
          · refine le_lt_absurd _ (le_congr ?_ (.eqRefl _) tot) huD.wk
            have x := natEq (ex2.wk.wk : C' ⊢[PRAAx] _); have y := natEq (eu.wk : C' ⊢[PRAAx] _)
            apply deriveNat; ipra_simps
            linear_combination -x - 𝔞 (dS D a m d) * y
          · apply deriveNat; ipra_simps; ring
    refine lt_of_lt_of_le (b := D + dS D a m d) ?_ ?_
    · exact le_of_eq_add (d := pred (dS D a m d)) (by have z := natEq hdSp; apply deriveNat; ipra_simps; linear_combination z)
    · refine le_congr ?_ ?_ (add_le_add_right (mS a m d * mS a m d) (le_mul_mono (le_refl (dS D a m d)) key))
      · have x := natEq ex2; apply deriveNat; ipra_simps; linear_combination -x
      · apply deriveNat; ipra_simps; ring
  -- New `R2`: `d' < d + 2 m'` (from `D < (d + m')²`), hence `(d' ∸ m')² < D`.
  have hdm1 : Γ ⊢[PRAAx] le (succ a) (d + mS a m d) := by
    refine le_of_eq_add (d := monus d (succ (rem (a + m) d))) ?_
    have x := natEq (eq_add_of_le htd); have y := natEq hmS; have z := natEq eA
    apply deriveNat; ipra_simps; linear_combination x + y - z
  have hDdm : Γ ⊢[PRAAx] lt D ((d + mS a m d) * (d + mS a m d)) := lt_sq_of_ge hB hdm1
  have key2 : Γ ⊢[PRAAx] lt (dS D a m d) (d + two * mS a m d) := by
    refine .orE (lt_or_le (dS D a m d) (d + two * mS a m d)) Prf.hyp0 ?_
    let C := le (d + two * mS a m d) (dS D a m d) :: Γ
    have m1 : C ⊢[PRAAx] le (d * (d + two * mS a m d)) (d * dS D a m d) := le_mul_mono (le_refl _) Prf.hyp0
    have m2 := add_le_add_right (mS a m d * mS a m d) m1
    refine le_lt_absurd _ (le_congr ?_ ?_ m2) hDdm.wk
    · apply deriveNat; ipra_simps; ring
    · have x := natEq (ex2.wk : C ⊢[PRAAx] _); apply deriveNat; ipra_simps; linear_combination -x
  have hR2' : Γ ⊢[PRAAx] lt (monus (dS D a m d) (mS a m d) * monus (dS D a m d) (mS a m d)) D := by
    refine .orE (le_total (dS D a m d) (mS a m d)) ?_ ?_
    · let C := le (dS D a m d) (mS a m d) :: Γ
      have z : C ⊢[PRAAx] monus (dS D a m d) (mS a m d) ≐ zero := Prf.hyp0
      refine lt_congr ((zero_mul _).eqSymm.eqTrans (congrMul z.eqSymm z.eqSymm)) (.eqRefl _) ?_
      exact lt_of_le_of_lt (zero_le _) (sq_lt_of_le hA.wk (zero_le a))
    · let C := le (mS a m d) (dS D a m d) :: Γ
      have ev := eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le (mS a m d) (dS D a m d))
      have x := natEq ev
      -- `v = d' ∸ m' < d + m'`.
      have hv : C ⊢[PRAAx] le (succ (monus (dS D a m d) (mS a m d))) (d + mS a m d) := by
        refine le_of_add_le_add_right (c := mS a m d) (le_congr ?_ ?_ key2.wk)
        · apply deriveNat; ipra_simps; linear_combination x
        · apply deriveNat; ipra_simps; ring
      -- `v² + v ≤ (d + m') v ≤ D`.
      have hmv : C ⊢[PRAAx] le (mS a m d * monus (dS D a m d) (mS a m d)) (mS a m d * (d + mS a m d)) :=
        le_mul_mono (le_refl _) (le_of_lt hv)
      have hsum : C ⊢[PRAAx] le (monus (dS D a m d) (mS a m d) * monus (dS D a m d) (mS a m d) +
          monus (dS D a m d) (mS a m d)) D := by
        have h₁ : C ⊢[PRAAx] le (succ (monus (dS D a m d) (mS a m d)) * monus (dS D a m d) (mS a m d))
            ((d + mS a m d) * monus (dS D a m d) (mS a m d)) := mul_le_mul_right _ hv
        refine le_trans (le_congr ?_ (.eqRefl _) h₁) (le_congr ?_ ?_
          (add_le_add_right (d * monus (dS D a m d) (mS a m d)) hmv))
        · apply deriveNat; ipra_simps; ring
        · apply deriveNat; ipra_simps; ring
        · have y := natEq (ex2.wk : C ⊢[PRAAx] _); apply deriveNat; ipra_simps; linear_combination -y - 𝔞 d * x
      refine .orE (zero_or_succ (monus (dS D a m d) (mS a m d))) ?_ ?_
      · let C' := (monus (dS D a m d) (mS a m d) ≐ zero) :: C
        have z : C' ⊢[PRAAx] monus (dS D a m d) (mS a m d) ≐ zero := Prf.hyp0
        refine lt_congr ((zero_mul _).eqSymm.eqTrans (congrMul z.eqSymm z.eqSymm)) (.eqRefl _) ?_
        exact lt_of_le_of_lt (zero_le _) (sq_lt_of_le hA.wk.wk (zero_le a))
      · refine lt_of_lt_of_le (b := monus (dS D a m d) (mS a m d) * monus (dS D a m d) (mS a m d) +
          monus (dS D a m d) (mS a m d)) ?_ hsum.wk
        refine le_of_eq_add (d := pred (monus (dS D a m d) (mS a m d))) ?_
        have z := natEq (Prf.hyp0 : ((monus (dS D a m d) (mS a m d) ≐ succ (pred (monus (dS D a m d) (mS a m d)))) :: C) ⊢[PRAAx] _)
        apply deriveNat; ipra_simps; linear_combination z
  -- Assembly.
  have hdS2 : Γ ⊢[PRAAx] le (dS D a m d) (two * a) := by
    have u := le_of_sq_lt hB hR2'
    refine le_trans (le_add_monus_l (dS D a m d) (mS a m d)) ?_
    exact le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; ring) (le_add_mono hmSa u)
  have hdvS : Γ ⊢[PRAAx] dvd (dS D a m d) (monus D (mS a m d * mS a m d)) := by
    refine DiophantineNumberTheory.Coprime.dvd_of_eq' hdSp (w := d) ?_
    exact (congrMonus ex2 (.eqRefl _)).eqTrans ((add_monus' _ _).eqTrans (mul_comm _ _))
  exact .andI (.andI hmSa (.andI (one_le_of_pos hdSp) (.andI hdS2 (.andI (le_of_lt hmSD) (.andI hdvS
    (.andI hR1' hR2')))))) (.andI ex1 ex2)

/-- `x ≤ y + z` gives `x ∸ y ≤ z`. -/
theorem monus_le_of_le_add {x y z : PTm n} (h : Γ ⊢[PRAAx] le x (y + z)) : Γ ⊢[PRAAx] le (monus x y) z := by
  refine .orE (le_total x y) ?_ ?_
  · exact le_congr (show (le x y :: Γ) ⊢[PRAAx] monus x y ≐ zero from Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · let C := le y x :: Γ
    have e1 := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le y x))
    have e2 := natEq (eq_add_of_le (h.wk : C ⊢[PRAAx] le x (y + z)))
    refine le_of_eq_add (d := monus (y + z) x) ?_
    apply deriveNat; ipra_simps
    linear_combination e2 + e1

/-- Reducedness is invariant under provable equality of the state. -/
theorem Red_congr {m m' d d' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d')
    (h : Γ ⊢[PRAAx] Red D a m d) : Γ ⊢[PRAAx] Red D a m' d' := by
  have mm := congrMul hm hm
  refine .andI (le_congr hm (.eqRefl _) (Prf.andE₁ h)) (.andI (le_congr (.eqRefl _) hd (Prf.andE₁ (Prf.andE₂ h)))
    (.andI (le_congr hd (.eqRefl _) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))))
    (.andI (le_congr mm (.eqRefl _) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
    (.andI ?_ (.andI ?_ ?_)))))
  · exact (congrAp2 remF (congrMonus (.eqRefl _) mm) hd).eqSymm.eqTrans
      (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
  · have s := congrAdd hd hm
    exact lt_congr (.eqRefl _) (congrMul s s) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))
  · have s := congrMonus hd hm
    exact lt_congr (congrMul s s) (.eqRefl _) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))

/-- The start: from `(m₀, d₀) = (0, 1)` the step gives `c₀ = a`, `m₁ = a`, `d₁ = D − a²`, exactly, and
`(a, D − a²)` is reduced. -/
theorem start_reduced (hA : Γ ⊢[PRAAx] lt (a * a) D) (hB : Γ ⊢[PRAAx] lt D (succ a * succ a)) :
    Γ ⊢[PRAAx] Red D a (mS a zero one) (dS D a zero one) ⋏
      ((one * cD a zero one ≐ mS a zero one + zero) ⋏ (D ≐ mS a zero one * mS a zero one + one * dS D a zero one)) := by
  have one_pos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have hc : Γ ⊢[PRAAx] cD a zero one ≐ a :=
    quo_of_eq one_pos (by apply deriveNat; ipra_simps; ring)
  have hm : Γ ⊢[PRAAx] mS a zero one ≐ a :=
    (congrMonus (congrMul (.eqRefl _) hc) (.eqRefl _)).eqTrans ((monus_zero _).eqTrans (by apply deriveNat; ipra_simps; ring))
  have eD := eq_add_of_le (le_of_lt hA)
  have hd : Γ ⊢[PRAAx] dS D a zero one ≐ monus D (a * a) :=
    quo_of_eq one_pos ((congrMonus (.eqRefl _) (congrMul hm hm)).eqTrans (by apply deriveNat; ipra_simps; ring))
  have e1 := natEq (eq_add_of_le hA)
  have hd1 : Γ ⊢[PRAAx] le one (monus D (a * a)) :=
    le_of_eq_add (d := monus D (succ (a * a))) (by
      have y := natEq eD; apply deriveNat; ipra_simps; linear_combination -y + e1)
  have hd2 : Γ ⊢[PRAAx] le (monus D (a * a)) (two * a) := by
    have hB' : Γ ⊢[PRAAx] le D (a * a + two * a) :=
      le_of_lt_succ' (lt_congr (.eqRefl _) (by apply deriveNat; ipra_simps; ring) hB)
    refine le_of_add_le_add_right (c := a * a) (le_congr ?_ ?_ hB')
    · have y := natEq eD; apply deriveNat; ipra_simps; linear_combination y
    · apply deriveNat; ipra_simps; ring
  have R : Γ ⊢[PRAAx] Red D a a (monus D (a * a)) := by
    refine .andI (le_refl _) (.andI hd1 (.andI hd2 (.andI (le_of_lt hA) (.andI ?_ (.andI ?_ ?_)))))
    · exact DiophantineNumberTheory.Coprime.dvd_self' (pos_of_le_one hd1)
    · exact lt_sq_of_ge hB (le_congr (by apply deriveNat; ipra_simps; ring) (.eqRefl _) (add_le_add_right a hd1))
    · have u : Γ ⊢[PRAAx] le (monus (monus D (a * a)) a) a :=
        monus_le_of_le_add (le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; ring) hd2)
      exact sq_lt_of_le hA u
  refine .andI (Red_congr hm.eqSymm hd.eqSymm R) (.andI ?_ ?_)
  · exact (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] one * cD a zero one ≐ cD a zero one + zero).eqTrans
      (congrAdd (hc.eqTrans hm.eqSymm) (.eqRefl _))
  · have x := natEq eD; have y := natEq hm; have z := natEq hd
    apply deriveNat; ipra_simps
    linear_combination x - (𝔞 (mS a zero one) + 𝔞 a) * y - z

/-- A reduced state is recovered from its successor: `m = a − ((a + m') mod d)`. -/
theorem pred_recover (hA : Γ ⊢[PRAAx] lt (a * a) D) (hB : Γ ⊢[PRAAx] lt D (succ a * succ a))
    (hR : Γ ⊢[PRAAx] Red D a m d) : Γ ⊢[PRAAx] m ≐ monus a (rem (a + mS a m d) d) := by
  have hm := Prf.andE₁ hR
  have hd := pos_of_le_one (Prf.andE₁ (Prf.andE₂ hR))
  have hR1 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hR)))))
  have ex1 := Prf.andE₁ (Prf.andE₂ (step_closure hA hB hR))
  -- `a < d + m`, so `a ∸ m < d`.
  have had : Γ ⊢[PRAAx] lt a (d + m) := by
    refine .orE (lt_or_le a (d + m)) Prf.hyp0 ?_
    exact le_lt_absurd _ (le_of_lt (lt_of_le_of_lt (le_mul_mono Prf.hyp0 Prf.hyp0) hA.wk)) hR1.wk
  have eA := eq_add_of_le hm
  have hlt : Γ ⊢[PRAAx] lt (monus a m) d := by
    refine le_of_add_le_add_right (c := m) (le_congr ?_ (.eqRefl _) had)
    have x := natEq eA; apply deriveNat; ipra_simps; linear_combination x
  have q := Prf.andE₂ (BlockSum.qr_block (i := cD a m d) hd hlt)
  have e : Γ ⊢[PRAAx] a + mS a m d ≐ cD a m d * d + monus a m := by
    have x := natEq ex1; have y := natEq eA
    apply deriveNat; ipra_simps; linear_combination -x + y
  have r : Γ ⊢[PRAAx] rem (a + mS a m d) d ≐ monus a m := (congrAp2 remF e (.eqRefl _)).eqTrans q
  exact (Combinatorics.Bell.monus_monus hm).eqSymm.eqTrans (congrMonus (.eqRefl _) r.eqSymm)

/-- `lem:reduced` (injectivity): two reduced states with the same successor are equal. -/
theorem step_injective {m₁ d₁ m₂ d₂ : PTm n} (hA : Γ ⊢[PRAAx] lt (a * a) D) (hB : Γ ⊢[PRAAx] lt D (succ a * succ a))
    (h₁ : Γ ⊢[PRAAx] Red D a m₁ d₁) (h₂ : Γ ⊢[PRAAx] Red D a m₂ d₂)
    (em : Γ ⊢[PRAAx] mS a m₁ d₁ ≐ mS a m₂ d₂) (ed : Γ ⊢[PRAAx] dS D a m₁ d₁ ≐ dS D a m₂ d₂) :
    Γ ⊢[PRAAx] (m₁ ≐ m₂) ⋏ (d₁ ≐ d₂) := by
  have c₁ := step_closure hA hB h₁; have c₂ := step_closure hA hB h₂
  have hd' := pos_of_le_one (Prf.andE₁ (Prf.andE₂ (Prf.andE₁ c₁)))
  have hd : Γ ⊢[PRAAx] d₁ ≐ d₂ := by
    refine Combinatorics.BinomialIdentities.mul_cancel hd' ?_
    have x := natEq (Prf.andE₂ (Prf.andE₂ c₁)); have y := natEq (Prf.andE₂ (Prf.andE₂ c₂))
    have u := natEq em; have v := natEq ed
    apply deriveNat; ipra_simps
    linear_combination y - x - (𝔞 (mS a m₁ d₁) + 𝔞 (mS a m₂ d₂)) * u - 𝔞 d₂ * v
  refine .andI ?_ hd
  exact (pred_recover hA hB h₁).eqTrans ((congrMonus (.eqRefl _) (congrAp2 remF (congrAdd (.eqRefl _) em) hd)).eqTrans
    (pred_recover hA hB h₂).eqSymm)

end Closure

end LeanProofs.IPRA.DiophantineNumberTheory.PellCFStep
