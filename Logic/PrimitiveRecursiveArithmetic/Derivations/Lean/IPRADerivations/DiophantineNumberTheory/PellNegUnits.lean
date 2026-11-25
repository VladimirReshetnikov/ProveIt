import IPRADerivations.DiophantineNumberTheory.PellAll
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.LinearCombination

/-!
# Negative units square to the fundamental unit

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:negativeunits` (first part).

Let `u = (A, B)` be fundamental (`A² = 1 + DB²`, `B ≥ 1`, minimal) and `v = (R, T)` a positive
solution of `R² + 1 = DT²` with `T ≤ B`. Then `v² = u`:

  `A = R² + DT² = 2R² + 1`,  `B = 2RT`.

Hence `R` is determined by `A` and then `T` by `B`: there is at most one such `v`.

`v² = (X, Y) = (R² + DT², 2RT)` has norm one and `Y ≥ 1`, so `Y ≥ B` and one unit descent
(`PellDescent.unit_descent`) writes `(X, Y) = u (r, t)`. If `t = 0` then `r = 1` and `(X, Y) = u`.
If `t ≥ 1`, minimality gives `t ≥ B` and then `r² = 1 + Dt² ≥ A²`, so
`Y = Br + At ≥ 2AB`; but `R < A` (from `R² + 2 ≤ A²`) and `T ≤ B` give `RT < AB`, i.e. `Y < 2AB`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellNegUnits

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (lt_of_sq_lt unit_descent rr tt)
open LeanProofs.IPRA.DiophantineNumberTheory.PellAll (minimal minimal_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `r² = 1 → r = 1`. -/
theorem eq_one_of_sq {r : PTm n} (h : Γ ⊢[PRAAx] r * r ≐ one) : Γ ⊢[PRAAx] r ≐ one := by
  have e : Γ ⊢[PRAAx] one ≐ one * one := by ipra_ring
  exact le_antisymm (le_of_sq_le (le_congr h.eqSymm e (le_refl _))) (le_of_sq_le (le_congr e h.eqSymm (le_refl _)))

/-- `R < A`. -/
theorem R_lt_A {A B D R T : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T)) (hTB : Γ ⊢[PRAAx] le T B) : Γ ⊢[PRAAx] lt R A := by
  refine lt_of_sq_lt (le_of_eq_add (d := succ (D * (monus B T * (two * T + monus B T)))) ?_)
  ipra_lc natEq hA - natEq hR +
    Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ B) + Groth.ι (IPRA.Q.mk Γ T) + Groth.ι (IPRA.Q.mk Γ (monus B T))) * natEq (eq_add_of_le hTB)

/-- `RT < AB`. -/
theorem RT_lt_AB {A B R T : PTm n} (hRA : Γ ⊢[PRAAx] lt R A) (hT : Γ ⊢[PRAAx] T ≐ succ (pred T))
    (hTB : Γ ⊢[PRAAx] le T B) : Γ ⊢[PRAAx] lt (R * T) (A * B) := by
  have h₁ : Γ ⊢[PRAAx] le (succ (R * T)) (succ R * T) := by
    refine le_of_eq_add (d := pred T) ?_
    ipra_lc natEq hT
  exact le_trans h₁ (le_trans (le_mul_mono hRA (le_refl T)) (le_mul_mono (le_refl A) hTB))

/-- `thm:negativeunits`: `v² = u`. -/
theorem neg_square {A B D R T : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hmin : Γ ⊢[PRAAx] minimal D B)
    (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T)) (hRp : Γ ⊢[PRAAx] R ≐ succ (pred R))
    (hTp : Γ ⊢[PRAAx] T ≐ succ (pred T)) (hTB : Γ ⊢[PRAAx] le T B) :
    Γ ⊢[PRAAx] (A ≐ R * R + D * (T * T)) ⋏ (B ≐ two * (R * T)) := by
  have hX : Γ ⊢[PRAAx] (R * R + D * (T * T)) * (R * R + D * (T * T)) ≐
      one + D * (two * (R * T) * (two * (R * T))) := by
    ipra_lc (Groth.ι (IPRA.Q.mk Γ R) ^ 2 - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ T) ^ 2 - 1) * natEq hR
  have hYp : Γ ⊢[PRAAx] two * (R * T) ≐ succ (pred (two * (R * T))) :=
    pos_mul (congrSucc (pred_succ _).eqSymm) (pos_mul hRp hTp)
  have hBY := Prf.impE (Prf.impE (minimal_at hmin _ _) hX) hYp
  have d := unit_descent hA hB hX hBY
  have dN := Prf.andE₁ d
  have dX := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ d))
  have dY := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ d))
  refine .orE (zero_or_succ (tt A B D (R * R + D * (T * T)) (two * (R * T)))) ?_ ?_
  · -- `t = 0`: `r = 1`.
    have hr := eq_one_of_sq (dN.wk.eqTrans (by
      ipra_lc Groth.ι (IPRA.Q.mk _ D) * (Groth.ι (IPRA.Q.mk _ (tt A B D (R * R + D * (T * T)) (two * (R * T))))) * natEq (Prf.hyp0 : ((tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ zero) :: Γ) ⊢[PRAAx] _)))
    have e₁ := natEq hr; have e₂ := natEq (dX.wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ zero))); have e₃ := natEq (dY.wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ zero)))
    refine .andI ?_ ?_
    · ipra_lc -e₂ - Groth.ι (IPRA.Q.mk _ A) * e₁ -
        Groth.ι (IPRA.Q.mk _ D) * Groth.ι (IPRA.Q.mk _ B) * natEq (Prf.hyp0 : ((tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ zero) :: Γ) ⊢[PRAAx] _)
    · ipra_lc -e₃ - Groth.ι (IPRA.Q.mk _ B) * e₁ -
        Groth.ι (IPRA.Q.mk _ A) * natEq (Prf.hyp0 : ((tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ zero) :: Γ) ⊢[PRAAx] _)
  · -- `t ≥ 1` is impossible.
    refine .botE _ ?_
    have hBt := Prf.impE (Prf.impE (minimal_at hmin.wk _ _) dN.wk) Prf.hyp0
    have hAr : ((tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐
        succ (pred (tt A B D (R * R + D * (T * T)) (two * (R * T))))) :: Γ) ⊢[PRAAx]
        le A (rr A B D (R * R + D * (T * T)) (two * (R * T))) := by
      refine le_of_sq_le (le_of_eq_add (d := D * (monus (tt A B D (R * R + D * (T * T)) (two * (R * T))) B *
        (two * B + monus (tt A B D (R * R + D * (T * T)) (two * (R * T))) B))) ?_)
      ipra_lc natEq (dN.wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ succ (pred (tt A B D (R * R + D * (T * T)) (two * (R * T))))))) -
        natEq (hA.wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ succ (pred (tt A B D (R * R + D * (T * T)) (two * (R * T))))))) +
        Groth.ι (IPRA.Q.mk _ D) * (Groth.ι (IPRA.Q.mk _ (tt A B D (R * R + D * (T * T)) (two * (R * T)))) + Groth.ι (IPRA.Q.mk _ B) + Groth.ι (IPRA.Q.mk _ (monus (tt A B D (R * R + D * (T * T)) (two * (R * T))) B))) * natEq (eq_add_of_le hBt)
    have hlt := RT_lt_AB (R_lt_A hA hR hTB) hTp hTB
    have e₁ := natEq (dY.wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ succ (pred (tt A B D (R * R + D * (T * T)) (two * (R * T))))))); have e₂ := natEq (eq_add_of_le hAr); have e₃ := natEq (eq_add_of_le hBt)
    refine succ_ne_zero' _ (a := one + two * monus (A * B) (succ (R * T)) +
      B * monus (rr A B D (R * R + D * (T * T)) (two * (R * T))) A +
      A * monus (tt A B D (R * R + D * (T * T)) (two * (R * T))) B) ?_
    ipra_lc -e₁ - Groth.ι (IPRA.Q.mk _ B) * e₂ - Groth.ι (IPRA.Q.mk _ A) * e₃ -
      2 * natEq ((eq_add_of_le hlt).wk (ψ := (tt A B D (R * R + D * (T * T)) (two * (R * T)) ≐ succ (pred (tt A B D (R * R + D * (T * T)) (two * (R * T)))))))

/-- `A = 2R² + 1` for the seed. -/
theorem A_eq {A B D R T : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hmin : Γ ⊢[PRAAx] minimal D B)
    (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T)) (hRp : Γ ⊢[PRAAx] R ≐ succ (pred R))
    (hTp : Γ ⊢[PRAAx] T ≐ succ (pred T)) (hTB : Γ ⊢[PRAAx] le T B) : Γ ⊢[PRAAx] A ≐ two * (R * R) + one := by
  ipra_lc natEq (Prf.andE₁ (neg_square hA hB hmin hR hRp hTp hTB)) - natEq hR

/-- Uniqueness of the bounded negative seed: two seeds `(R, T)`, `(R', T')` with `T, T' ≤ B` agree. -/
theorem seed_unique {A B D R T R' T' : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hmin : Γ ⊢[PRAAx] minimal D B)
    (hR : Γ ⊢[PRAAx] R * R + one ≐ D * (T * T)) (hRp : Γ ⊢[PRAAx] R ≐ succ (pred R))
    (hTp : Γ ⊢[PRAAx] T ≐ succ (pred T)) (hTB : Γ ⊢[PRAAx] le T B)
    (hR' : Γ ⊢[PRAAx] R' * R' + one ≐ D * (T' * T')) (hRp' : Γ ⊢[PRAAx] R' ≐ succ (pred R'))
    (hTp' : Γ ⊢[PRAAx] T' ≐ succ (pred T')) (hTB' : Γ ⊢[PRAAx] le T' B) :
    Γ ⊢[PRAAx] (R ≐ R') ⋏ (T ≐ T') := by
  have a₁ := A_eq hA hB hmin hR hRp hTp hTB
  have a₂ := A_eq hA hB hmin hR' hRp' hTp' hTB'
  have two' : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm
  have hsq : Γ ⊢[PRAAx] R * R ≐ R' * R' := by
    refine mul_cancel two' ?_
    ipra_lc natEq a₂ - natEq a₁
  have hRR : Γ ⊢[PRAAx] R ≐ R' :=
    le_antisymm (le_of_sq_le (le_congr (.eqRefl _) hsq (le_refl _)))
      (le_of_sq_le (le_congr hsq (.eqRefl _) (le_refl _)))
  refine .andI hRR (mul_cancel hRp (mul_cancel two' ?_))
  ipra_lc natEq (Prf.andE₂ (neg_square hA hB hmin hR' hRp' hTp' hTB')) -
    natEq (Prf.andE₂ (neg_square hA hB hmin hR hRp hTp hTB)) - 2 * Groth.ι (IPRA.Q.mk Γ T') * natEq hRR

end LeanProofs.IPRA.DiophantineNumberTheory.PellNegUnits
