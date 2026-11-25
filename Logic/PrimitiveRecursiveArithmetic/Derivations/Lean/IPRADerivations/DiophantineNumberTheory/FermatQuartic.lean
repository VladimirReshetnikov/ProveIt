import IPRADerivations.DiophantineNumberTheory.QuarticStep
import IPRADerivations.Core.DescentEx
import IPRADerivations.Algebra.CubeRootTwo
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Fermat's quartic theorem

Packet: `diophantine-number-theory/flt_ipra`, Theorem `thm:four`:

`∀ x y z. x > 0 ∧ y > 0 → x⁴ + y⁴ ≠ z²`, and hence `FLT(4)`.

* `smaller`: every solution yields one with a smaller last coordinate. If `g = gcd(x, y) ≥ 2`,
  then `g² ∣ z` (`dvd_of_sq_dvd_sq`) and `(x/g, y/g, z/g²)` is one. If `g = 1`, two even legs
  contradict coprimality, two odd legs make `z²` an odd square plus an odd square, and
  otherwise `QuarticStep.primitive_step` applies, after exchanging the legs if necessary.
* The descent (`DescentEx`) runs over pairs `(⟨x, y⟩, z)`, with a 0/1 indicator `χ` and
  the bound `⟨x, y⟩ < (2z)² + z + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The non-primitive step -/

theorem alg_np {x y z g x₁ y₁ : PTm n} (hE : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z) (ex : Γ ⊢[PRAAx] x ≐ g * x₁)
    (ey : Γ ⊢[PRAAx] y ≐ g * y₁) : Γ ⊢[PRAAx] z * z ≐ ((g * g) * (g * g)) * (q4 x₁ + q4 y₁) := by
  refine withEq hE fun e₁ => withEq ex fun e₂ => withEq ey fun e₃ => ?_
  apply deriveNat; ipra_simps; rw [← e₁, e₂, e₃]; ring

theorem alg_np₂ {z G K z₁ : PTm n} (hzz : Γ ⊢[PRAAx] z * z ≐ (G * G) * K) (ez : Γ ⊢[PRAAx] z ≐ G * z₁) :
    Γ ⊢[PRAAx] (G * G) * K ≐ (G * G) * (z₁ * z₁) := by
  ipra_lc -natEq hzz + (Groth.ι (IPRA.Q.mk Γ z) + Groth.ι (IPRA.Q.mk Γ G) * Groth.ι (IPRA.Q.mk Γ z₁)) * natEq ez

theorem alg_lt {z g c z₁ : PTm n} (ez : Γ ⊢[PRAAx] z ≐ (g * g) * z₁) (hg : Γ ⊢[PRAAx] g ≐ succ (succ c))
    (hz₁ : Γ ⊢[PRAAx] z₁ ≐ succ (pred z₁)) :
    Γ ⊢[PRAAx] z ≐ succ z₁ + ((c * c + two * two * c + succ two) * pred z₁ + (c * c + two * two * c + two)) := by
  ipra_lc natEq ez + Groth.ι (IPRA.Q.mk Γ z₁) * (Groth.ι (IPRA.Q.mk Γ g) + Groth.ι (IPRA.Q.mk Γ c) + 2) * natEq hg +
    (Groth.ι (IPRA.Q.mk Γ c) * Groth.ι (IPRA.Q.mk Γ c) + 4 * Groth.ι (IPRA.Q.mk Γ c) + 3) * natEq hz₁

theorem z_pos {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hE : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z) :
    Γ ⊢[PRAAx] z ≐ succ (pred z) := by
  refine .orE (zero_or_succ z) ?_ Prf.hyp0
  have h4 := pos_mul (pos_mul hx hx) (pos_mul hx hx)
  have h0 := add_eq_zero_left ((hE.wk.eqTrans (congrMul Prf.hyp0 Prf.hyp0)).eqTrans (mul_zero _))
  exact succ_ne_zero' _ (h4.wk.eqSymm.eqTrans h0)

/-- If `gcd(x, y) = c + 2`, divide by it. -/
theorem nonprim_step {x y z c : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y))
    (hE : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z) (hg2 : Γ ⊢[PRAAx] gcd x y ≐ succ (succ c)) : Γ ⊢[PRAAx] φ := by
  have hgp := gcd_pos (B := y) hx
  have hgd := gcd_dvd' (b := y) hx
  have ex := eq_of_dvd' hgp (Prf.andE₁ hgd)
  have ey := eq_of_dvd' hgp (Prf.andE₂ hgd)
  have hx₁ := pos_of_eq_mul hx ex
  have hy₁ := pos_of_eq_mul hy ey
  have hG := pos_mul hgp hgp
  have hz := z_pos hx hE
  have hzz := alg_np hE ex ey
  have dz := dvd_of_sq_dvd_sq hG hz (dvd_of_eq' (pos_mul hG hG) hzz)
  have ez := eq_of_dvd' hG dz
  have hz₁ := pos_of_eq_mul hz ez
  have eq₁ := mul_cancel (pos_mul hG hG) (alg_np₂ hzz ez)
  exact k.apply (.andI hx₁ (.andI hy₁ eq₁)) (le_of_eq_add (alg_lt ez hg2 hz₁))

/-! ## The step for every solution -/

theorem smaller {x y z : PTm n} {φ : Fm PTm n} (k : Cont Γ z φ) (hs : Γ ⊢[PRAAx] sol x y z) :
    Γ ⊢[PRAAx] φ := by
  have hx := Prf.andE₁ hs
  have hy := Prf.andE₁ (Prf.andE₂ hs)
  have hE := Prf.andE₂ (Prf.andE₂ hs)
  have hgp := gcd_pos (B := y) hx
  refine .orE (zero_or_succ (pred (gcd x y))) ?_ ?_
  · have hg1 : ((pred (gcd x y) ≐ zero) :: Γ) ⊢[PRAAx] gcd x y ≐ one := hgp.wk.eqTrans (congrSucc Prf.hyp0)
    have hE' : Γ ⊢[PRAAx] q4 y + q4 x ≐ z * z := (add_comm _ _).eqTrans hE
    refine .orE (even_or_odd x) ?_ ?_
    · refine .orE (even_or_odd y) (not_both_even _ hg1.wk.wk Prf.hyp1 Prf.hyp0) ?_
      exact primitive_step ((k.wk _).wk _ |>.wk _) hy.wk.wk.wk hx.wk.wk.wk Prf.hyp0 Prf.hyp1
        (gcd_comm_one hy.wk.wk.wk hg1.wk.wk) hE'.wk.wk.wk
    · refine .orE (even_or_odd y) ?_ ?_
      · exact primitive_step ((k.wk _).wk _ |>.wk _) hx.wk.wk.wk hy.wk.wk.wk Prf.hyp1 Prf.hyp0
          hg1.wk.wk hE.wk.wk.wk
      · exact odd_sq_sum _ (odd_sq Prf.hyp1) (odd_sq Prf.hyp0) hE.wk.wk.wk
  · exact nonprim_step (k.wk _) hx.wk hy.wk hE.wk (hgp.wk.eqTrans (congrSucc Prf.hyp0))

/-! ## The indicator -/

/-- `χ(a, b) = [a = ⟨fst a, snd a⟩] · sg(fst a) · sg(snd a) · [fst⁴ + snd⁴ = b²]`. -/
abbrev chiF : PTm 2 :=
  eqb (var 0) (pairT (fstT (var 0)) (sndT (var 0))) * (sg (fstT (var 0)) * (sg (sndT (var 0)) *
    eqb (q4 (fstT (var 0)) + q4 (sndT (var 0))) (var 1 * var 1)))

/-- The bound `β(b) = (2b)² + b + 1`. -/
abbrev betaF : PTm 1 := succ ((two * var 0) * (two * var 0) + var 0)

theorem inst2_chi (a b : PTm n) : inst2 chiF a b = eqb a (pairT (fstT a) (sndT a)) * (sg (fstT a) *
    (sg (sndT a) * eqb (q4 (fstT a) + q4 (sndT a)) (b * b))) := by
  simp [inst2]

theorem inst1_beta (b : PTm n) : inst1 betaF b = succ ((two * b) * (two * b) + b) := by
  simp [inst1]

alias congrSg := Common.congrSg

alias congrPair := Common.congrPairT

alias zo_eqb := Common.eqb_zero_or_one

alias zo_sg := Common.sg_zero_or_one

theorem zo_mul {u v : PTm n} (hu : Γ ⊢[PRAAx] (u ≐ zero) ⋎ (u ≐ one)) (hv : Γ ⊢[PRAAx] (v ≐ zero) ⋎ (v ≐ one)) :
    Γ ⊢[PRAAx] (u * v ≐ zero) ⋎ (u * v ≐ one) := by
  refine .orE hu (.orI₁ ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))) ?_
  refine .orE hv.wk (.orI₁ ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))) ?_
  exact .orI₂ ((congrMul Prf.hyp1 Prf.hyp0).eqTrans (one_mul _))

theorem mul_one_split {u v : PTm n} (hu : Γ ⊢[PRAAx] (u ≐ zero) ⋎ (u ≐ one)) (h : Γ ⊢[PRAAx] u * v ≐ one) :
    Γ ⊢[PRAAx] (u ≐ one) ⋏ (v ≐ one) := by
  refine .orE hu ?_ ?_
  · exact succ_ne_zero' _ (h.wk.eqSymm.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))
  · exact .andI Prf.hyp0 ((one_mul _).eqSymm.eqTrans ((congrMul Prf.hyp0.eqSymm (.eqRefl _)).eqTrans h.wk))

alias eq_of_eqb := Common.eq_of_eqb

theorem pos_of_sg {x : PTm n} (h : Γ ⊢[PRAAx] sg x ≐ one) : Γ ⊢[PRAAx] x ≐ succ (pred x) :=
  .orE (zero_or_succ x) (succ_ne_zero' _ (h.wk.eqSymm.eqTrans ((congrSg Prf.hyp0).eqTrans sg_zero)))
    Prf.hyp0

theorem chi_spec {a b : PTm n} (h : Γ ⊢[PRAAx] inst2 chiF a b ≐ one) :
    Γ ⊢[PRAAx] (a ≐ pairT (fstT a) (sndT a)) ⋏ sol (fstT a) (sndT a) b := by
  rw [inst2_chi] at h
  have s₁ := mul_one_split (zo_eqb _ _) h
  have s₂ := mul_one_split (zo_sg _) (Prf.andE₂ s₁)
  have s₃ := mul_one_split (zo_sg _) (Prf.andE₂ s₂)
  exact .andI (eq_of_eqb (Prf.andE₁ s₁)) (.andI (pos_of_sg (Prf.andE₁ s₂))
    (.andI (pos_of_sg (Prf.andE₁ s₃)) (eq_of_eqb (Prf.andE₂ s₃))))

theorem chi_of_sol {x y z : PTm n} (hs : Γ ⊢[PRAAx] sol x y z) : Γ ⊢[PRAAx] inst2 chiF (pairT x y) z ≐ one := by
  rw [inst2_chi]
  have f := fst_pair (Γ := Γ) x y
  have s := snd_pair (Γ := Γ) x y
  have e₁ := eqb_of_eq (congrPair (Γ := Γ) f.eqSymm s.eqSymm)
  have e₂ := (congrSg f).eqTrans ((congrSg (Prf.andE₁ hs)).eqTrans (sg_succ _))
  have e₃ := (congrSg s).eqTrans ((congrSg (Prf.andE₁ (Prf.andE₂ hs))).eqTrans (sg_succ _))
  have e₄ := eqb_of_eq ((congrAdd (congrMul (congrMul f f) (congrMul f f))
    (congrMul (congrMul s s) (congrMul s s))).eqTrans (Prf.andE₂ (Prf.andE₂ hs)))
  refine withEq e₁ fun h₁ => withEq e₂ fun h₂ => withEq e₃ fun h₃ => withEq e₄ fun h₄ => ?_
  apply deriveNat; ipra_simps; rw [h₁, h₂, h₃, h₄]; ring

/-! ## The descent hypotheses -/

theorem h01 : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    (inst2 chiF (var 0) (var 1) ≐ zero) ⋎ (inst2 chiF (var 0) (var 1) ≐ one) := by
  rw [inst2_chi]
  exact zo_mul (zo_eqb _ _) (zo_mul (zo_sg _) (zo_mul (zo_sg _) (zo_eqb _ _)))

theorem h0 : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst2 chiF (var 0) zero ≐ zero := by
  rw [inst2_chi]
  refine .orE (zero_or_succ (fstT (var 0 : PTm 2))) ?_ ?_
  · have e : ([fstT (var 0 : PTm 2) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] sg (fstT (var 0)) ≐ zero :=
      (congrSg Prf.hyp0).eqTrans sg_zero
    refine withEq e fun h => ?_
    apply deriveNat; ipra_simps; rw [h]; ring
  · have hf : ([fstT (var 0 : PTm 2) ≐ succ (pred (fstT (var 0)))] : List (Fm PTm 2)) ⊢[PRAAx]
        fstT (var 0) ≐ succ (pred (fstT (var 0))) := Prf.hyp0
    have h4 := pos_mul (pos_mul hf hf) (pos_mul hf hf)
    have hne : ((fstT (var 0 : PTm 2) ≐ succ (pred (fstT (var 0)))) :: []) ⊢[PRAAx]
        neg (q4 (fstT (var 0)) + q4 (sndT (var 0)) ≐ zero * zero) := by
      refine .impI ?_
      exact succ_ne_zero' _ (h4.wk.eqSymm.eqTrans (add_eq_zero_left (Prf.hyp0.eqTrans (mul_zero _))))
    have e := eqb_of_ne hne
    refine withEq e fun h => ?_
    apply deriveNat; ipra_simps; rw [h]; ring

theorem hb : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    lt (var 0) (inst1 betaF (var 1)) := by
  rw [inst1_beta]
  have sp := chi_spec (Γ := ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2))) (a := (var 0 : PTm 2)) (b := var 1) Prf.hyp0
  have ea := Prf.andE₁ sp
  have hx := Prf.andE₁ (Prf.andE₂ sp)
  have hy := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sp))
  have hE := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp))
  have lx := le_trans (le_sq hx) (le_of_sq_le (le_of_eq_add (d := q4 (sndT (var 0))) hE.eqSymm))
  have ly := le_trans (le_sq hy) (le_of_sq_le (le_of_eq_add (d := q4 (fstT (var 0)))
    (hE.eqSymm.eqTrans (add_comm _ _))))
  have wx := eq_add_of_le lx
  have wy := eq_add_of_le ly
  have hs : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
      le (fstT (var 0) + sndT (var 0)) (two * var 1) := by
    refine le_of_eq_add (d := monus (var 1) (fstT (var 0)) + monus (var 1) (sndT (var 0))) ?_
    refine withEq wx fun e₁ => withEq wy fun e₂ => ?_
    ipra_lc e₁ + e₂
  have hsq := sq_le_sq hs
  have wq := eq_add_of_le hsq
  refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := monus ((two * var 1) * (two * var 1))
    ((fstT (var 0) + sndT (var 0)) * (fstT (var 0) + sndT (var 0))) + monus (var 1) (fstT (var 0))) ?_)
  have ea' : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
      var 0 ≐ (fstT (var 0) + sndT (var 0)) * (fstT (var 0) + sndT (var 0)) + fstT (var 0) := ea
  refine withEq ea' fun e₁ => withEq wq fun e₂ => withEq wx fun e₃ => ?_
  ipra_lc e₂ + e₃ - e₁

theorem hstep : ([var 1 ≐ succ (pred (var 1)), inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    Fm.ex (Fm.ex ((inst2 chiF (var 1) (var 0) ≐ one) ⋏ lt (var 0) (var 3))) := by
  have sp := Prf.andE₂ (chi_spec (Γ := ([var 1 ≐ succ (pred (var 1)), inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)))
    (a := (var 0 : PTm 2)) (b := var 1) Prf.hyp1)
  refine smaller (z := var 1) ?_ sp
  intro Δ _ a b c hs hlt
  refine .exI (pairT a b) (.exI c ?_)
  simpa [Syn.up] using (Prf.andI (chi_of_sol hs) hlt)

theorem hyps : DescentEx.Hyps chiF betaF := ⟨h01, h0, hb, hstep⟩

/-! ## The theorem -/

/-- `x, y ≥ 1 → x⁴ + y⁴ ≠ z²`; variables `0 = x - 1`, `1 = y - 1`, `2 = z`. -/
abbrev quarticFormula : Fm PTm 3 := neg (q4 (succ (var 0)) + q4 (succ (var 1)) ≐ var 2 * var 2)

theorem fermat_quartic : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 quarticFormula := by
  refine closeUniv 3 (.impI ?_)
  have hs : ([q4 (succ (var 0)) + q4 (succ (var 1)) ≐ var 2 * var 2] : List (Fm PTm 3)) ⊢[PRAAx]
      sol (succ (var 0)) (succ (var 1)) (var 2) :=
    .andI (congrSucc (pred_succ _).eqSymm) (.andI (congrSucc (pred_succ _).eqSymm) Prf.hyp0)
  have d := inst (Γ := [q4 (succ (var 0)) + q4 (succ (var 1)) ≐ var 2 * var 2])
    (.impI (DescentEx.descent hyps)) (![pairT (succ (var 0)) (succ (var 1)), var 2] : Fin 2 → PTm 3)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Fm.subst_bot] at d
  exact .impE d (chi_of_sol hs)

/-- `FLT(4)`: `x, y ≥ 1 → x⁴ + y⁴ ≠ z⁴`. -/
abbrev flt4Formula : Fm PTm 3 := neg (q4 (succ (var 0)) + q4 (succ (var 1)) ≐ q4 (var 2))

theorem flt4 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 flt4Formula := by
  refine closeUniv 3 ?_
  have h := inst (Γ := ([] : List (Fm PTm 3))) (Prf.allOpen (Prf.allOpen (Prf.allOpen
    (fermat_quartic : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 quarticFormula))))
    (![var 0, var 1, var 2 * var 2] : Fin 3 → PTm 3)
  simpa using h

end LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic
