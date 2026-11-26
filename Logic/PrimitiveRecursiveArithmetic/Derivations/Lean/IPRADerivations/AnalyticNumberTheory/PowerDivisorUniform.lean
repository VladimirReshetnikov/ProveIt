import IPRADerivations.AnalyticNumberTheory.PowerDivisorGrowth
import IPRADerivations.Core.Header

/-!
# One witness for every exponent (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, Theorem
`thm:powerdivisor`: "It is also equivalent to the single sentence in which the same output constant works for every
`h ≥ 2`" and, in the proof, "The same `C_r(c)` works for every `h`. Conversely a uniform-power hypothesis can be
specialized to `h = 2` before applying inversion."

`GrowthU` is the uniform sentence `∀k ∃c ∀z ∀N |B_{z+2}(N)|^{2(k+1)} ≤ c N^{k+2}` (the exponent `h = z + 2` is placed
after the constant).

* `forward_allU`, `growth_forwardU`: `PowerDivisorGrowth.forward_all` under one more binder `∀z`, with `h = z + 2`; the
  witness `C_r(c)` does not depend on `h`;
* `spec_all`, `uniform_spec`: specializing `z = 0` gives the growth statement of `B_2`;
* `growth_uniform_iff`: `GrowthS A ↔ GrowthU`, using `PowerDivisorGrowth.growth_backward` at `h = 2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorUniform

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem upf_three {a b : ℕ} (σ : Fin (a + 3) → PTm b) : (up σ : Fin (a + 4) → PTm (b + 1)) 3 = Syn.shift (σ 2) := rfl

/-- The uniform sentence `∀k ∃c ∀z ∀N |B_{z+2}(N)|^{2(k+1)} ≤ c N^{k+2}`. -/
abbrev GrowthU (aP aN : PTm 2) (y : PTm n) : Fm PTm n :=
  Fm.all (Fm.ex (Fm.all (Fm.all (Mat (BB aP) (BB aN)
    (pairT (succ (succ (var 1))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift y))))) (var 3) (var 2) (var 0)))))

/-- `forward_all` under `∀z`, with `h = z + 2`. -/
theorem forward_allU (aP aN : PTm 2) {y k c : PTm n} {K C : PTm (n + 1)} {X K' C' : PTm (n + 2)}
    (hK : K = Syn.shift (succ (two * k))) (hC : C = Syn.shift c) (hX : X = Syn.shift (Syn.shift y))
    (hK' : K' = Syn.shift (Syn.shift k)) (hC' : C' = Syn.shift (Syn.shift (Cout k c)))
    (H : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) (Syn.shift y) K C (var 0))) :
    Γ ⊢[PRAAx] Fm.all (Fm.all (Mat (BB aP) (BB aN) (pairT (succ (succ (var 1))) X) K' C' (var 0))) := by
  subst hK hC hX hK' hC'
  refine .allI ?_
  have H1 := H.shift
  simp only [GrowthS, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three] at H1
  exact forward_all aP aN (y := Syn.shift y) (h := succ (succ (var 0))) (k := Syn.shift k) (c := Syn.shift c)
    (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1])
    (by ipra_le 𝔞 (var 0)) H1

/-- `A ⇒ uniform B`. -/
theorem growth_forwardU (aP aN : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthS (AB aP) (AB aN) y ⟶ GrowthU aP aN y := by
  refine .impI (.allI ?_)
  have hG : ((GrowthS (AB aP) (AB aN) y :: Γ).map Fm.shift) ⊢[PRAAx] Fm.shift (GrowthS (AB aP) (AB aN) y) :=
    (Prf.hyp0 : (GrowthS (AB aP) (AB aN) y :: Γ) ⊢[PRAAx] _).shift
  have hk := Prf.allE (succ (two * var 0)) hG
  simp only [GrowthS, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three] at hk
  refine .exE hk ?_
  simp only [GrowthU, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three, subst_pairT,
    ConciseIPRA.PTm.subst_succ]
  refine .exI (Cout (var 1) (var 0)) ?_
  simp only [Fm.subst_all, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three, subst_pairT,
    ConciseIPRA.PTm.subst_succ]
  exact forward_allU aP aN (y := Syn.shift (Syn.shift y)) (k := var 1) (c := var 0)
    (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1])
    Prf.hyp0

/-- Specializing the exponent to `h = 2`. -/
theorem spec_all (aP aN : PTm 2) {Y K0 C0 : PTm n} {X0 K0' C0' : PTm (n + 2)} {X K C : PTm (n + 1)}
    (hX0 : X0 = Syn.shift (Syn.shift Y)) (hK0 : K0' = Syn.shift (Syn.shift K0)) (hC0 : C0' = Syn.shift (Syn.shift C0))
    (hX : X = Syn.shift (pairT two Y)) (hK : K = Syn.shift K0) (hC : C = Syn.shift C0)
    (H : Γ ⊢[PRAAx] Fm.all (Fm.all (Mat (BB aP) (BB aN) (pairT (succ (succ (var 1))) X0) K0' C0' (var 0)))) :
    Γ ⊢[PRAAx] Fm.all (Mat (BB aP) (BB aN) X K C (var 0)) := by
  subst hX0 hK0 hC0 hX hK hC
  have b := Prf.allE zero H
  simp only [Fm.subst_all, subst_Mat, up1_v0, up1_v1, inst_v0, subst_up_shift_pal, Syn.subst_inst_shift, subst_pairT,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero] at b
  have e : Syn.shift (pairT two Y) = pairT (succ (succ (Syn.shift zero))) (Syn.shift Y) := by simp [Syn.shift]
  rw [e]
  exact b

/-- `uniform B ⇒ B_2`. -/
theorem uniform_spec (aP aN : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthU aP aN y ⟶ GrowthS (BB aP) (BB aN) (pairT two y) := by
  refine .impI (.allI ?_)
  have hk := (Prf.hyp0 : (GrowthU aP aN y :: Γ) ⊢[PRAAx] GrowthU aP aN y).allOpen
  refine .exE hk ?_
  simp only [GrowthS, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three]
  refine .exI (var 0) ?_
  simp only [Fm.subst_all, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, upf_three]
  exact spec_all aP aN (Y := Syn.shift (Syn.shift y)) (K0 := var 1) (C0 := var 0)
    (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1])
    (by simp [Syn.shift, upf_one, upf_two, upf_three, inst_v0, inst_v1]) Prf.hyp0

/-- `thm:powerdivisor`, the uniform form: `(∀k ∃c ∀N |A(N)|^{2(k+1)} ≤ cN^{k+2}) ↔
(∀k ∃c ∀z ∀N |B_{z+2}(N)|^{2(k+1)} ≤ cN^{k+2})`, one witness `C_r(c)` for every exponent. -/
theorem growth_uniform_iff (aP aN : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (GrowthS (AB aP) (AB aN) y) (GrowthU aP aN y) :=
  .andI (growth_forwardU aP aN y)
    (Prf.impTrans (uniform_spec aP aN y) (growth_backward aP aN (le_refl two) y))

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorUniform
