import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Core.Fubini
import IPRADerivations.Probability.Independence

/-!
# Möbius inversion and the Möbius formula for `φ`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Lemma `lem:mobius-cancel`
(the inversion consequence) and Corollary `cor:phi-mobius`.

* `dv_prod`, `dv_symm`: `[d ∣ N][e ∣ N/d] = [d e ∣ N] = [e ∣ N][d ∣ N/e]` for `d, e ≥ 1`;
* `col_pt`: after exchanging the double sum (`fubini`), the column of `e` is
  `[e ∣ N] f(e) ∑_{d ∣ N/e} μ^±(d)`, and Möbius cancellation (`MobiusBounds.cancel_gen`) leaves
  `[N = e] f(e)`;
* `mobius_inversion`: for every body `f` and `N ≥ 1`,
  `∑_{d ∣ N} μ⁺(d) ∑_{e ∣ N/d} f(e) = ∑_{d ∣ N} μ⁻(d) ∑_{e ∣ N/d} f(e) + f(N)`, i.e.
  `F(n) = ∑_{d ∣ n} f(d)` implies `f(n) = ∑_{d ∣ n} μ(d) F(n/d)`;
* `phi_mobius` (`cor:phi-mobius`): with `f = φ` and `∑_{e ∣ k} φ(e) = k` (`SumPhi.sum_phi_at`),
  `φ(N) = ∑_{d ∣ N} μ(d) N/d`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' pos_of_eq_mul)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Divisibility of a product -/

/-- `[i ∣ N][j ∣ N/i] = [i j ∣ N]` for `i, j ≥ 1`. -/
theorem dv_prod {N i j : PTm n} (hi : Γ ⊢[PRAAx] i ≐ succ (pred i)) (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) :
    Γ ⊢[PRAAx] eqb (rem N i) zero * eqb (rem (quo N i) j) zero ≐ eqb (rem N (i * j)) zero := by
  have hij := pos_mul hi hj
  refine .orE (eq_or_ne (rem N i) zero) ?_ ?_
  · let C : List (Fm PTm n) := (rem N i ≐ zero) :: Γ
    have hd : C ⊢[PRAAx] dvd i N := Prf.hyp0
    have eN := eq_of_dvd' hi.wk hd
    have one_l : C ⊢[PRAAx] eqb (rem N i) zero ≐ one := eqb_of_eq Prf.hyp0
    refine (congrMul one_l (.eqRefl _)).eqTrans ((one_mul _).eqTrans ?_)
    refine .orE (eq_or_ne (rem (quo N i) j) zero) ?_ ?_
    · let D : List (Fm PTm n) := (rem (quo N i) j ≐ zero) :: C
      have eq := eq_of_dvd' hj.wk.wk (Prf.hyp0 : D ⊢[PRAAx] dvd j (quo N i))
      have e₁ := natEq (eN.wk : D ⊢[PRAAx] _); have e₂ := natEq eq
      have hd2 : D ⊢[PRAAx] dvd (i * j) N := by
        refine dvd_of_eq' hij.wk.wk (w := quo (quo N i) j) ?_
        apply deriveNat; ipra_simps
        linear_combination e₁ + 𝔞 i * e₂
      exact (eqb_of_eq Prf.hyp0).eqTrans (eqb_of_eq hd2).eqSymm
    · let D : List (Fm PTm n) := neg (rem (quo N i) j ≐ zero) :: C
      have ne : D ⊢[PRAAx] neg (dvd (i * j) N) := by
        refine .impI ?_
        let D' : List (Fm PTm n) := dvd (i * j) N :: D
        have e := natEq (eq_of_dvd' hij.wk.wk.wk (Prf.hyp0 : D' ⊢[PRAAx] _))
        -- `N/i = j (N/(ij))`
        have q : D' ⊢[PRAAx] quo N i ≐ j * quo N (i * j) := by
          refine quo_eq hi.wk.wk.wk (z := N) (q := j * quo N (i * j)) (r := zero) ?_ (zero_lt' hi.wk.wk.wk)
          apply deriveNat; ipra_simps; linear_combination e
        have hdj : D' ⊢[PRAAx] dvd j (quo N i) := dvd_of_eq' hj.wk.wk.wk q
        exact Prf.impE Prf.hyp1 hdj
      exact (eqb_of_ne Prf.hyp0).eqTrans (eqb_of_ne ne).eqSymm
  · let C : List (Fm PTm n) := neg (rem N i ≐ zero) :: Γ
    have ne : C ⊢[PRAAx] neg (dvd (i * j) N) := by
      refine .impI ?_
      let D : List (Fm PTm n) := dvd (i * j) N :: C
      have e := natEq (eq_of_dvd' hij.wk.wk (Prf.hyp0 : D ⊢[PRAAx] _))
      have hdi : D ⊢[PRAAx] dvd i N := by
        refine dvd_of_eq' hi.wk.wk (w := j * quo N (i * j)) ?_
        apply deriveNat; ipra_simps; linear_combination e
      exact Prf.impE Prf.hyp1 hdi
    exact (zero_mul_l (eqb_of_ne Prf.hyp0) _).eqTrans (eqb_of_ne ne).eqSymm

/-- The symmetric form: `sg i [i ∣ N] sg j [j ∣ N/i] = sg j [j ∣ N] sg i [i ∣ N/j]`. -/
theorem dv_symm (N i j : PTm n) :
    Γ ⊢[PRAAx] (sg i * eqb (rem N i) zero) * (sg j * eqb (rem (quo N i) j) zero) ≐
      (sg j * eqb (rem N j) zero) * (sg i * eqb (rem (quo N j) i) zero) := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have s : ((i ≐ zero) :: Γ) ⊢[PRAAx] sg i ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have a := natEq s
    apply deriveNat; ipra_simps; linear_combination
      (𝔞 (eqb (rem N i) zero) * 𝔞 (sg j) * 𝔞 (eqb (rem (quo N i) j) zero) -
        𝔞 (sg j) * 𝔞 (eqb (rem N j) zero) * 𝔞 (eqb (rem (quo N j) i) zero)) * a
  · refine .orE (zero_or_succ j) ?_ ?_
    · have s : ((j ≐ zero) :: (i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] sg j ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      have a := natEq s
      apply deriveNat; ipra_simps; linear_combination
        (𝔞 (sg i) * 𝔞 (eqb (rem N i) zero) * 𝔞 (eqb (rem (quo N i) j) zero) -
          𝔞 (eqb (rem N j) zero) * 𝔞 (sg i) * 𝔞 (eqb (rem (quo N j) i) zero)) * a
    · let C : List (Fm PTm n) := (j ≐ succ (pred j)) :: (i ≐ succ (pred i)) :: Γ
      have hj : C ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
      have hi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp1
      have p₁ := natEq (dv_prod (N := N) hi hj)
      have p₂ := natEq (dv_prod (N := N) hj hi)
      have c := natEq (congrEqb' (congrAp2 remF (.eqRefl N) (mul_comm (Γ := C) i j)) (.eqRefl zero))
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (sg i) * 𝔞 (sg j) * (p₁ - p₂ + c)

/-! ## The double sum -/

section Inversion

variable (f : PTm 2)

/-- `[d ∣ N] μ⁺_{N+1}(d) [e ∣ N/d] f(e, N)`, over `0 = d`, `1 = e`, `2 = N`. -/
def aP : PTm 3 := ((sg (var 0) * eqb (rem (var 2) (var 0)) zero) * muP (succ (var 2)) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (var 2) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)
/-- `[d ∣ N] μ⁻_{N+1}(d) [e ∣ N/d] f(e, N)`. -/
def aN : PTm 3 := ((sg (var 0) * eqb (rem (var 2) (var 0)) zero) * muN (succ (var 2)) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (var 2) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)

theorem inst3_aP (d e N : PTm n) : inst3 (aP f) d e N =
    ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ((sg e * eqb (rem (quo N d) e) zero) * inst2 f e N) := by
  have hf : Syn.subst ![d, e, N] (Syn.subst ![var 1, var 2] f) = inst2 f e N := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, aP, PTm.subst_mul, hf]
  simp
theorem inst3_aN (d e N : PTm n) : inst3 (aN f) d e N =
    ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ((sg e * eqb (rem (quo N d) e) zero) * inst2 f e N) := by
  have hf : Syn.subst ![d, e, N] (Syn.subst ![var 1, var 2] f) = inst2 f e N := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, aN, PTm.subst_mul, hf]
  simp

/-- The pointwise rearrangement `[d ∣ N][e ∣ N/d] = [e ∣ N][d ∣ N/e]`. -/
theorem a_pt (d e N : PTm n) :
    Γ ⊢[PRAAx] (inst3 (aP f) d e N ≐ ((sg e * eqb (rem N e) zero) * inst2 f e N) *
        inst2 GP d (pairT (succ N) (quo N e))) ⋏
      (inst3 (aN f) d e N ≐ ((sg e * eqb (rem N e) zero) * inst2 f e N) *
        inst2 GN d (pairT (succ N) (quo N e))) := by
  rw [inst3_aP, inst3_aN]
  have g := G_at (Γ := Γ) d (succ N) (quo N e)
  have s := natEq (dv_symm (Γ := Γ) N d e)
  have g₁ := natEq (Prf.andE₁ g); have g₂ := natEq (Prf.andE₂ g)
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    linear_combination 𝔞 (eqb (sq (succ N) d) zero) * 𝔞 (eqb (rem (om (succ N) d) two) zero) * 𝔞 (inst2 f e N) * s -
      𝔞 (sg e) * 𝔞 (eqb (rem N e) zero) * 𝔞 (inst2 f e N) * g₁
  · apply deriveNat; ipra_simps
    linear_combination 𝔞 (eqb (sq (succ N) d) zero) * 𝔞 (eqb (rem (om (succ N) d) two) one) * 𝔞 (inst2 f e N) * s -
      𝔞 (sg e) * 𝔞 (eqb (rem N e) zero) * 𝔞 (inst2 f e N) * g₂

theorem shift_inst2 (g : PTm 2) (a b : PTm n) : Syn.shift (inst2 g a b) = inst2 g (Syn.shift a) (Syn.shift b) := by
  simp only [inst2, Syn.shift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- A column `∑_{d ≤ N} a^±(d, e, N)` is the constant `[e ∣ N] f(e, N)` times a Möbius divisor sum of `N/e`. -/
theorem col_scale (e N : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (colB (aP f))) (succ N) (pairT e N) ≐
        ((sg e * eqb (rem N e) zero) * inst2 f e N) * ap2 (sumF GP) (succ N) (pairT (succ N) (quo N e))) ⋏
      (ap2 (sumF (colB (aN f))) (succ N) (pairT e N) ≐
        ((sg e * eqb (rem N e) zero) * inst2 f e N) * ap2 (sumF GN) (succ N) (pairT (succ N) (quo N e))) := by
  have hc : Syn.shift ((sg e * eqb (rem N e) zero) * inst2 f e N) =
      (sg (Syn.shift e) * eqb (rem (Syn.shift N) (Syn.shift e)) zero) * inst2 f (Syn.shift e) (Syn.shift N) := by
    rw [shift_mul', shift_mul', shift_inst2]; simp [Syn.shift]
  have hp : Syn.shift (pairT (succ N) (quo N e)) = pairT (succ (Syn.shift N)) (quo (Syn.shift N) (Syn.shift e)) := by
    simp [Syn.shift]
  refine .andI (sum_scale _ _ _ _ _ _ (.allI (.impI ?_))) (sum_scale _ _ _ _ _ _ (.allI (.impI ?_)))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₁ (a_pt f _ _ _))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₂ (a_pt f _ _ _))

/-- `[N/e = 1] = [N = e]` when `N = e k`, `e ≥ 1`. -/
theorem eqb_quo {N e k : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] N ≐ e * k) :
    Γ ⊢[PRAAx] eqb k one ≐ eqb N e := by
  refine .orE (eq_or_ne k one) ?_ ?_
  · have k1 : ((k ≐ one) :: Γ) ⊢[PRAAx] k ≐ one := Prf.hyp0
    have Ne : ((k ≐ one) :: Γ) ⊢[PRAAx] N ≐ e :=
      h.wk.eqTrans ((congrMul (.eqRefl _) k1).eqTrans (by apply deriveNat; ipra_simps; ring))
    exact (eqb_of_eq k1).eqTrans (eqb_of_eq Ne).eqSymm
  · have ne : (neg (k ≐ one) :: Γ) ⊢[PRAAx] neg (N ≐ e) := by
      refine .impI ?_
      have e₁ := natEq (h.wk.wk : (N ≐ e) :: neg (k ≐ one) :: Γ ⊢[PRAAx] _)
      have e₂ := natEq (Prf.hyp0 : (N ≐ e) :: neg (k ≐ one) :: Γ ⊢[PRAAx] _)
      have c : ((N ≐ e) :: neg (k ≐ one) :: Γ) ⊢[PRAAx] k ≐ one := by
        refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel he.wk.wk ?_
        apply deriveNat; ipra_simps; linear_combination -e₁ + e₂
      exact Prf.impE Prf.hyp1 c
    exact (eqb_of_ne Prf.hyp0).eqTrans (eqb_of_ne ne).eqSymm

end Inversion

/-! ## Columns and the inversion theorem -/

section Inversion2

variable (f : PTm 2)

/-- A column of the swapped double sum: `C⁺(e) = C⁻(e) + [N = e] f(e, N)` for `N ≥ 1`. -/
theorem col_pt {e N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ N) (pairT e N) ≐
      ap2 (sumF (colB (aN f))) (succ N) (pairT e N) + eqb N e * inst2 f e N := by
  have cs := col_scale (Γ := Γ) f e N
  -- the vanishing case, from a vanishing constant and `[N = e] = 0`
  have van : ∀ (Δ : List (Fm PTm n)), Γ ⊆ Δ → (Δ ⊢[PRAAx] sg e * eqb (rem N e) zero ≐ zero) →
      (Δ ⊢[PRAAx] eqb N e ≐ zero) → (Δ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ N) (pairT e N) ≐
        ap2 (sumF (colB (aN f))) (succ N) (pairT e N) + eqb N e * inst2 f e N) := by
    intro Δ hs hc hq
    have z₁ := ((Prf.andE₁ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    have z₂ := ((Prf.andE₂ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    exact z₁.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd z₂.eqSymm (zero_mul_l hq _).eqSymm))
  refine .orE (zero_or_succ e) ?_ ?_
  · let C : List (Fm PTm n) := (e ≐ zero) :: Γ
    have hc : C ⊢[PRAAx] sg e * eqb (rem N e) zero ≐ zero := zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
    have hq : C ⊢[PRAAx] eqb N e ≐ zero :=
      eqb_of_ne (.impI (succ_ne_zero' _ (hN.wk.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans Prf.hyp1))))
    exact van _ (List.subset_cons_of_subset _ (List.Subset.refl _)) hc hq
  · refine .orE (eq_or_ne (rem N e) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem N e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hd : C ⊢[PRAAx] dvd e N := Prf.hyp0
      have eN := eq_of_dvd' he hd
      have hk := pos_of_eq_mul hN.wk.wk eN
      have w := natEq eN; have wp := natEq he
      have hkN : C ⊢[PRAAx] le (succ (quo N e)) (succ N) := by
        refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred e * quo N e) ?_)
        apply deriveNat; ipra_simps; linear_combination w + 𝔞 (quo N e) * wp
      have cg := natEq (cancel_gen hk hkN hkN)
      have eq := natEq (eqb_quo he eN)
      have one₁ : C ⊢[PRAAx] sg e * eqb (rem N e) zero ≐ one :=
        (congrMul ((congrSg he).eqTrans (sg_succ _)) (eqb_of_eq hd)).eqTrans (by apply deriveNat; ipra_simps; ring)
      have o₁ := natEq one₁
      have cP := natEq ((Prf.andE₁ cs).wk.wk : C ⊢[PRAAx] _)
      have cN := natEq ((Prf.andE₂ cs).wk.wk : C ⊢[PRAAx] _)
      apply deriveNat; ipra_simps
      linear_combination cP - cN + 𝔞 (sg e) * 𝔞 (eqb (rem N e) zero) * 𝔞 (inst2 f e N) * cg +
        𝔞 (sg e) * 𝔞 (eqb (rem N e) zero) * 𝔞 (inst2 f e N) * eq + 𝔞 (inst2 f e N) * 𝔞 (eqb N e) * o₁
    · let C : List (Fm PTm n) := neg (rem N e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hc : C ⊢[PRAAx] sg e * eqb (rem N e) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by apply deriveNat; ipra_simps; ring)
      have hq : C ⊢[PRAAx] eqb N e ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have r : ((N ≐ e) :: C) ⊢[PRAAx] rem N e ≐ zero :=
          (congrAp2 remF Prf.hyp0 (.eqRefl e)).eqTrans
            (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.dvd_self' he.wk)
        exact Prf.impE Prf.hyp1 r
      exact van _ (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hc hq

end Inversion2

/-! ## Möbius inversion -/

section Inversion3

variable (f : PTm 2)

/-- `[snd y = e] f(e, snd y)`, over `0 = e`, `1 = y`. -/
def δB : PTm 2 := eqb (sndT (var 1)) (var 0) * Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_δ (e y : PTm n) : inst2 (δB f) e y = eqb (sndT y) e * inst2 f e (sndT y) := by
  have hf : Syn.subst ![e, y] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f e (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, δB, PTm.subst_mul, hf]
  simp

/-- Möbius inversion: for `N ≥ 1`,
`∑_{d ∣ N} μ⁺(d) ∑_{e ∣ N/d} f(e) = ∑_{d ∣ N} μ⁻(d) ∑_{e ∣ N/d} f(e) + f(N)`,
i.e. `∑_{d ∣ N} μ(d) F(N/d) = f(N)` for `F(k) = ∑_{e ∣ k} f(e)`. -/
theorem mobius_inversion {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ N) (pairT (succ N) N) ≐
      ap2 (sumF (oB (aN f))) (succ N) (pairT (succ N) N) + inst2 f N N := by
  have fP := natEq (fubini (Γ := Γ) (aP f) (succ N) (succ N) N)
  have fN := natEq (fubini (Γ := Γ) (aN f) (succ N) (succ N) N)
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cs : Γ ⊢[PRAAx] ap2 (sumF (pB (aP f))) (succ N) (pairT (succ N) N) ≐
      ap2 (sumF (addBody (pB (aN f)) (δB f))) (succ N) (pairT (succ N) N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_pB, inst2_pB, inst2_δ, shift_pairT, hs]
    let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
    have f₁ : Δ ⊢[PRAAx] fstT (pairT (succ (Syn.shift N)) (Syn.shift N)) ≐ succ (Syn.shift N) := fst_pair _ _
    have s₁ : Δ ⊢[PRAAx] sndT (pairT (succ (Syn.shift N)) (Syn.shift N)) ≐ Syn.shift N := snd_pair _ _
    have c := col_pt (Γ := Δ) f (e := var 0) hN'.wk
    refine (congrAp2 (sumF (colB (aP f))) f₁ (congrPairT (.eqRefl _) s₁)).eqTrans (c.eqTrans ?_)
    exact congrAdd (congrAp2 (sumF (colB (aN f))) f₁ (congrPairT (.eqRefl _) s₁)).eqSymm
      (congrMul (congrEqb' s₁.eqSymm (.eqRefl _)) (congrInst2 f (.eqRefl _) s₁.eqSymm))
  have sa := natEq (sum_add (Γ := Γ) (pB (aN f)) (δB f) (succ N) (pairT (succ N) N))
  have dl : Γ ⊢[PRAAx] ap2 (sumF (δB f)) (succ N) (pairT (succ N) N) ≐ inst2 f N N := by
    refine (sum_congr_bounded (δB f) (dB f) _ (pairT N N) (succ N) (.allI (.impI ?_))).eqTrans
      (sum_delta f (monus_self _))
    rw [inst2_δ, inst2_dB, shift_pairT, shift_pairT]
    exact congrMul (congrEqb' ((snd_pair _ _).eqTrans (fst_pair _ _).eqSymm) (.eqRefl _))
      (congrInst2 f (.eqRefl _) ((snd_pair _ _).eqTrans (snd_pair _ _).eqSymm))
  have e₁ := natEq cs; have e₂ := natEq dl
  apply deriveNat; ipra_simps
  linear_combination fP + e₁ + sa + e₂ - fN

end Inversion3


/-! ## The Möbius formula for `φ` -/

/-- `φ(e)`, over `0 = e`. -/
abbrev phiB : PTm 2 := ap2 (sumF Totient.totBody) (var 0) (var 0)
/-- `[e ≥ 1][e ∣ k] φ(e)`, over `0 = e`, `1 = k`. -/
abbrev innerB : PTm 2 := (sg (var 0) * eqb (rem (var 1) (var 0)) zero) * ap2 (sumF Totient.totBody) (var 0) (var 0)
/-- `[d ∣ N] μ^±(d) (N/d)`. -/
abbrev QP : PTm 2 := PB * quo (var 1) (var 0)
abbrev QN : PTm 2 := NB * quo (var 1) (var 0)

theorem inst2_phiB (e N : PTm n) : inst2 phiB e N = Totient.phi e := by simp [inst2]
theorem inst2_inner (e k : PTm n) :
    inst2 innerB e k = (sg e * eqb (rem k e) zero) * Totient.phi e := by simp [inst2]
theorem inst2_QP (d N : PTm n) : inst2 QP d N = ((sg d * eqb (rem N d) zero) * muP (succ N) d) * quo N d := by
  simp [inst2]
theorem inst2_QN (d N : PTm n) : inst2 QN d N = ((sg d * eqb (rem N d) zero) * muN (succ N) d) * quo N d := by
  simp [inst2]

/-- `[a ∣ k] = 0` for `a > k ≥ 1`. -/
theorem eqb_rem_big {k a : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (h : Γ ⊢[PRAAx] lt k a) :
    Γ ⊢[PRAAx] eqb (rem k a) zero ≐ zero := by
  have w := natEq (eq_add_of_le h)
  have ha : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
    LeanProofs.IPRA.AnalyticNumberTheory.Primes.eq_succ_pred (y := k + monus a (succ k))
      (by apply deriveNat; ipra_simps; linear_combination w)
  have r : Γ ⊢[PRAAx] rem k a ≐ k := rem_eq' ha (q := zero) (by apply deriveNat; ipra_simps; ring) h
  exact (congrEqb' r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hk.wk.eqSymm.eqTrans Prf.hyp0))))

/-- `∑_{e ≤ N} [e ≥ 1][e ∣ k] φ(e) = k` for `1 ≤ k ≤ N`. -/
theorem inner_sum {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF innerB) (succ N) k ≐ k := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF innerB) (succ N) k ≐ ap2 (sumF innerB) (succ k) k := by
    refine sum_ext innerB (fun Δ a hs hl => ?_) hkN
    rw [inst2_inner]
    exact zero_mul_l ((congrMul (.eqRefl _) (eqb_rem_big (hk'.weaken hs) hl)).eqTrans
      (by apply deriveNat; ipra_simps; ring)) _
  refine cut.eqTrans ((sum_congr_bounded innerB SumPhi.dpB _ _ _ (.allI (.impI ?_))).eqTrans
    (SumPhi.sum_phi_at hk))
  rw [inst2_inner, SumPhi.inst2_dp]
  let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ k)) :: Γ.map Fm.shift
  refine .orE (zero_or_succ (var 0 : PTm (n + 1))) ?_ ?_
  · have h0 : ((var 0 ≐ zero) :: Δ) ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ zero := Prf.hyp0
    have p0 : ((var 0 ≐ zero) :: Δ) ⊢[PRAAx] Totient.phi (var 0 : PTm (n + 1)) ≐ zero :=
      (congrAp2 (sumF Totient.totBody) h0 h0).eqTrans (sum_zero _ _)
    exact ((congrMul (.eqRefl _) p0).eqTrans (mul_zero _)).eqTrans ((congrMul (.eqRefl _) p0).eqTrans (mul_zero _)).eqSymm
  · have h1 : ((var 0 ≐ succ (pred (var 0))) :: Δ) ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ succ (pred (var 0)) :=
      Prf.hyp0
    have s1 := (congrSg h1).eqTrans (sg_succ _)
    exact (congrMul (congrMul s1 (.eqRefl _)) (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; ring)

/-- A row of the double sum for `f = φ`: `[d ∣ N] μ^±(d) ∑_{e ∣ N/d} φ(e) = [d ∣ N] μ^±(d) (N/d)`. -/
theorem row_phi {d N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP phiB)) d (pairT (succ N) N) ≐ inst2 QP d N) ⋏
      (inst2 (oB (aN phiB)) d (pairT (succ N) N) ≐ inst2 QN d N) := by
  rw [inst2_oB, inst2_oB, inst2_QP, inst2_QN]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ N) N) ≐ succ N := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ N) N) ≐ N := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP phiB))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN phiB))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem N d) zero) * muP (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muP (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem N d) zero) * muN (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muN (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (quo N d) = quo (Syn.shift N) (Syn.shift d) := by simp [Syn.shift]
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP phiB))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ap2 (sumF innerB) (succ N) (quo N d) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcP, hq, inst2_inner]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP, inst2_phiB]
    exact .eqRefl _
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN phiB))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ap2 (sumF innerB) (succ N) (quo N d) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcN, hq, inst2_inner]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN, inst2_phiB]
    exact .eqRefl _
  -- the sum `∑_{e ≤ N} [e ∣ N/d] φ(e)` is `N/d` when the prefactor is nonzero
  have key : ∀ (X : PTm n), Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * ap2 (sumF innerB) (succ N) (quo N d) ≐
      ((sg d * eqb (rem N d) zero) * X) * quo N d := by
    intro X
    refine .orE (zero_or_succ d) ?_ ?_
    · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · refine .orE (eq_or_ne (rem N d) zero) ?_ ?_
      · let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
        have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N)
        have hk := pos_of_eq_mul hN.wk.wk eN
        have w := natEq eN; have wp := natEq hd
        have hkN : C ⊢[PRAAx] le (succ (quo N d)) (succ N) := by
          refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo N d) ?_)
          apply deriveNat; ipra_simps; linear_combination w + 𝔞 (quo N d) * wp
        exact congrMul (.eqRefl _) (inner_sum hk hkN)
      · have z : (neg (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d * eqb (rem N d) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by apply deriveNat; ipra_simps; ring)
        exact (zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm
  exact .andI (cR.eqTrans (scP.eqTrans (key _))) (cR'.eqTrans (scN.eqTrans (key _)))

/-- `cor:phi-mobius`: `φ(N) = ∑_{d ∣ N} μ(d) N/d` for `N ≥ 1`, as
`∑_{d ∣ N} μ⁺(d) N/d = φ(N) + ∑_{d ∣ N} μ⁻(d) N/d`. -/
theorem phi_mobius {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF QP) (succ N) N ≐ Totient.phi N + ap2 (sumF QN) (succ N) N := by
  have inv := mobius_inversion (Γ := Γ) phiB hN
  rw [inst2_phiB] at inv
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP phiB))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF QP) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_phi hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN phiB))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF QN) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_phi hN'.wk)
  have a := natEq inv; have b := natEq cP; have c := natEq cN
  apply deriveNat; ipra_simps
  linear_combination -b + a + c

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion
