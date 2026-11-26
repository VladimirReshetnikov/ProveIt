import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Core.Fubini
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination
import IPRADerivations.AnalyticNumberTheory.DivisorCases
import IPRADerivations.Core.Reindex

/-!
# Möbius inversion and the Möbius formula for `φ`

Packets: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Lemma `lem:mobius-cancel` (the inversion
consequence) and Corollary `cor:phi-mobius`; `pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry` (the inversion
with a parameter).

* `dv_prod`, `dv_symm`: `[d ∣ N][e ∣ N/d] = [d e ∣ N] = [e ∣ N][d ∣ N/e]` for `d, e ≥ 1`;
* `MobiusInversionP.mobius_inversion_p`: for every body `f(e, Z)` with a packed parameter `Z = (N, y)` (the
  arithmetic reads `N = fst Z`, the body receives `Z`, so it can carry data that are the same for every `n ≤ x`) and
  `N ≥ 1`, `Σ_{d ∣ N} μ⁺(d) Σ_{e ∣ N/d} f(e, Z) = Σ_{d ∣ N} μ⁻(d) Σ_{e ∣ N/d} f(e, Z) + f(N, Z)`. After
  exchanging the double sum (`fubini`), the column of `e` is `[e ∣ N] f(e) Σ_{d ∣ N/e} μ^±(d)` (`col_pt`), and Möbius
  cancellation (`MobiusBounds.cancel_gen`) leaves `[N = e] f(e)`;
* `mobius_inversion`: the same for a body `f(e, N)` whose second variable is the modulus itself,
  `∑_{d ∣ N} μ⁺(d) ∑_{e ∣ N/d} f(e) = ∑_{d ∣ N} μ⁻(d) ∑_{e ∣ N/d} f(e) + f(N)`, i.e. `F(n) = ∑_{d ∣ n} f(d)` implies
  `f(n) = ∑_{d ∣ n} μ(d) F(n/d)`. It is the instance `Z = ⟨N, 0⟩` of the parameterized theorem (`a_lift`,
  `oB_sum_congr`);
* `row_closed`, `inversion_of_rows` and their `_p` forms: the scaffold shared by the instances;
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
        ipra_lc e₁ + 𝔞 i * e₂
      exact (eqb_of_eq Prf.hyp0).eqTrans (eqb_of_eq hd2).eqSymm
    · let D : List (Fm PTm n) := neg (rem (quo N i) j ≐ zero) :: C
      have ne : D ⊢[PRAAx] neg (dvd (i * j) N) := by
        refine .impI ?_
        let D' : List (Fm PTm n) := dvd (i * j) N :: D
        have e := natEq (eq_of_dvd' hij.wk.wk.wk (Prf.hyp0 : D' ⊢[PRAAx] _))
        -- `N/i = j (N/(ij))`
        have q : D' ⊢[PRAAx] quo N i ≐ j * quo N (i * j) := by
          refine quo_eq hi.wk.wk.wk (z := N) (q := j * quo N (i * j)) (r := zero) ?_ (zero_lt' hi.wk.wk.wk)
          ipra_lc e
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
        ipra_lc e
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
      ipra_lc 𝔞 (sg i) * 𝔞 (sg j) * (natEq (dv_prod (N := N) hi hj) - natEq (dv_prod (N := N) hj hi) + natEq (congrEqb' (congrAp2 remF (.eqRefl N) (mul_comm (Γ := C) i j)) (.eqRefl zero)))

theorem shift_inst2 (g : PTm 2) (a b : PTm n) : Syn.shift (inst2 g a b) = inst2 g (Syn.shift a) (Syn.shift b) := by
  simp only [inst2, Syn.shift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- `[N/e = 1] = [N = e]` when `N = e k`, `e ≥ 1`. -/
theorem eqb_quo {N e k : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] N ≐ e * k) :
    Γ ⊢[PRAAx] eqb k one ≐ eqb N e := by
  refine .orE (eq_or_ne k one) ?_ ?_
  · have k1 : ((k ≐ one) :: Γ) ⊢[PRAAx] k ≐ one := Prf.hyp0
    have Ne : ((k ≐ one) :: Γ) ⊢[PRAAx] N ≐ e :=
      h.wk.eqTrans ((congrMul (.eqRefl _) k1).eqTrans (by ipra_ring))
    exact (eqb_of_eq k1).eqTrans (eqb_of_eq Ne).eqSymm
  · have ne : (neg (k ≐ one) :: Γ) ⊢[PRAAx] neg (N ≐ e) := by
      refine .impI ?_
      have c : ((N ≐ e) :: neg (k ≐ one) :: Γ) ⊢[PRAAx] k ≐ one := by
        refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel he.wk.wk ?_
        ipra_lc -natEq (h.wk.wk : (N ≐ e) :: neg (k ≐ one) :: Γ ⊢[PRAAx] _) +
          natEq (Prf.hyp0 : (N ≐ e) :: neg (k ≐ one) :: Γ ⊢[PRAAx] _)
      exact Prf.impE Prf.hyp1 c
    exact (eqb_of_ne Prf.hyp0).eqTrans (eqb_of_ne ne).eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (dv_symm eqb_quo shift_inst2)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Inversion

variable (f : PTm 2)

/-- `[d ∣ N] μ⁺_{N+1}(d) [e ∣ N/d] f(e, Z)` with `N = fst Z`, over `0 = d`, `1 = e`, `2 = Z`. -/
def aP : PTm 3 := ((sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) * muP (succ (fstT (var 2))) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (fstT (var 2)) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)
/-- `[d ∣ N] μ⁻_{N+1}(d) [e ∣ N/d] f(e, Z)`. -/
def aN : PTm 3 := ((sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) * muN (succ (fstT (var 2))) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (fstT (var 2)) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)

theorem inst3_aP (d e Z : PTm n) : inst3 (aP f) d e Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) *
      ((sg e * eqb (rem (quo (fstT Z) d) e) zero) * inst2 f e Z) := by
  simp only [inst3, aP, PTm.subst_mul, subst_reindex2]
  simp
theorem inst3_aN (d e Z : PTm n) : inst3 (aN f) d e Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) *
      ((sg e * eqb (rem (quo (fstT Z) d) e) zero) * inst2 f e Z) := by
  simp only [inst3, aN, PTm.subst_mul, subst_reindex2]
  simp

theorem a_pt (d e Z : PTm n) :
    Γ ⊢[PRAAx] (inst3 (aP f) d e Z ≐ ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
        inst2 GP d (pairT (succ (fstT Z)) (quo (fstT Z) e))) ⋏
      (inst3 (aN f) d e Z ≐ ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
        inst2 GN d (pairT (succ (fstT Z)) (quo (fstT Z) e))) := by
  rw [inst3_aP, inst3_aN]
  have g := G_at (Γ := Γ) d (succ (fstT Z)) (quo (fstT Z) e)
  have g₁ := natEq (Prf.andE₁ g); have g₂ := natEq (Prf.andE₂ g)
  refine .andI ?_ ?_
  · ipra_lc 𝔞 (eqb (sq (succ (fstT Z)) d) zero) * 𝔞 (eqb (rem (om (succ (fstT Z)) d) two) zero) * 𝔞 (inst2 f e Z) * natEq (dv_symm (Γ := Γ) (fstT Z) d e) -
      𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * g₁
  · ipra_lc 𝔞 (eqb (sq (succ (fstT Z)) d) zero) * 𝔞 (eqb (rem (om (succ (fstT Z)) d) two) one) * 𝔞 (inst2 f e Z) * natEq (dv_symm (Γ := Γ) (fstT Z) d e) -
      𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * g₂

theorem col_scale (e Z : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
        ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
          ap2 (sumF GP) (succ (fstT Z)) (pairT (succ (fstT Z)) (quo (fstT Z) e))) ⋏
      (ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) ≐
        ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
          ap2 (sumF GN) (succ (fstT Z)) (pairT (succ (fstT Z)) (quo (fstT Z) e))) := by
  have hc : Syn.shift ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) =
      (sg (Syn.shift e) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift e)) zero) * inst2 f (Syn.shift e) (Syn.shift Z) := by
    rw [Mobius.shift_mul', Mobius.shift_mul', shift_inst2]; simp [Syn.shift]
  have hp : Syn.shift (pairT (succ (fstT Z)) (quo (fstT Z) e)) =
      pairT (succ (fstT (Syn.shift Z))) (quo (fstT (Syn.shift Z)) (Syn.shift e)) := by
    simp [Syn.shift]
  refine .andI (sum_scale _ _ _ _ _ _ (.allI (.impI ?_))) (sum_scale _ _ _ _ _ _ (.allI (.impI ?_)))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₁ (a_pt f _ _ _))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₂ (a_pt f _ _ _))

/-- A column: `C⁺(e) = C⁻(e) + [N = e] f(e, Z)` for `N = fst Z ≥ 1`. -/
theorem col_pt {e Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
      ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) + eqb (fstT Z) e * inst2 f e Z := by
  have cs := col_scale (Γ := Γ) f e Z
  have van : ∀ (Δ : List (Fm PTm n)), Γ ⊆ Δ → (Δ ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero) →
      (Δ ⊢[PRAAx] eqb (fstT Z) e ≐ zero) → (Δ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
        ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) + eqb (fstT Z) e * inst2 f e Z) := by
    intro Δ hs hc hq
    have z₁ := ((Prf.andE₁ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    have z₂ := ((Prf.andE₂ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    exact z₁.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd z₂.eqSymm (zero_mul_l hq _).eqSymm))
  refine .orE (zero_or_succ e) ?_ ?_
  · let C : List (Fm PTm n) := (e ≐ zero) :: Γ
    have hc : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero := zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
    have hq : C ⊢[PRAAx] eqb (fstT Z) e ≐ zero :=
      eqb_of_ne (.impI (succ_ne_zero' _ (hN.wk.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans Prf.hyp1))))
    exact van _ (List.subset_cons_of_subset _ (List.Subset.refl _)) hc hq
  · refine .orE (eq_or_ne (rem (fstT Z) e) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem (fstT Z) e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hd : C ⊢[PRAAx] dvd e (fstT Z) := Prf.hyp0
      have eN := eq_of_dvd' he hd
      have hk := pos_of_eq_mul hN.wk.wk eN
      have w := natEq eN; have wp := natEq he
      have hkN : C ⊢[PRAAx] le (succ (quo (fstT Z) e)) (succ (fstT Z)) := by
        refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred e * quo (fstT Z) e) ?_)
        ipra_lc w + 𝔞 (quo (fstT Z) e) * wp
      have one₁ : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ one :=
        (congrMul ((congrSg he).eqTrans (sg_succ _)) (eqb_of_eq hd)).eqTrans (by ipra_ring)
      ipra_lc natEq ((Prf.andE₁ cs).wk.wk : C ⊢[PRAAx] _) - natEq ((Prf.andE₂ cs).wk.wk : C ⊢[PRAAx] _) +
        𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * natEq (cancel_gen hk hkN hkN) +
        𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * natEq (eqb_quo he eN) +
        𝔞 (inst2 f e Z) * 𝔞 (eqb (fstT Z) e) * natEq one₁
    · let C : List (Fm PTm n) := neg (rem (fstT Z) e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hc : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
      have hq : C ⊢[PRAAx] eqb (fstT Z) e ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have r : ((fstT Z ≐ e) :: C) ⊢[PRAAx] rem (fstT Z) e ≐ zero :=
          (congrAp2 remF Prf.hyp0 (.eqRefl e)).eqTrans
            (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.dvd_self' he.wk)
        exact Prf.impE Prf.hyp1 r
      exact van _ (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hc hq

/-- `[fst (snd y) = e] f(e, snd y)`, over `0 = e`, `1 = y`. -/
def dltB : PTm 2 := eqb (fstT (sndT (var 1))) (var 0) * Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_dlt (e y : PTm n) : inst2 (dltB f) e y = eqb (fstT (sndT y)) e * inst2 f e (sndT y) := by
  simp only [inst2, dltB, PTm.subst_mul, subst_reindex2]
  simp

/-- Möbius inversion with a parameter: for `N = fst Z ≥ 1`,
`Σ_{d ∣ N} μ⁺(d) Σ_{e ∣ N/d} f(e, Z) = Σ_{d ∣ N} μ⁻(d) Σ_{e ∣ N/d} f(e, Z) + f(N, Z)`. -/
theorem mobius_inversion_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (oB (aN f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) + inst2 f (fstT Z) Z := by
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cs : Γ ⊢[PRAAx] ap2 (sumF (pB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (addBody (pB (aN f)) (dltB f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_pB, inst2_pB, inst2_dlt, shift_pairT, hs]
    refine (congrAp2 (sumF (colB (aP f))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((col_pt f (e := var 0) (Z := Syn.shift Z) hN'.wk).eqTrans ?_)
    exact congrAdd (congrAp2 (sumF (colB (aN f))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
      (congrMul (congrEqb' (congrFst (snd_pair _ _)).eqSymm (.eqRefl _)) (congrInst2 f (.eqRefl _) (snd_pair _ _).eqSymm))
  have dl : Γ ⊢[PRAAx] ap2 (sumF (dltB f)) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐ inst2 f (fstT Z) Z := by
    refine (sum_congr_bounded (dltB f) (dB f) _ (pairT (fstT Z) Z) (succ (fstT Z)) (.allI (.impI ?_))).eqTrans
      (sum_delta f (monus_self _))
    rw [inst2_dlt, inst2_dB, shift_pairT, shift_pairT, hs, show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]]
    exact congrMul (congrEqb' ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _).eqSymm) (.eqRefl _))
      (congrInst2 f (.eqRefl _) ((snd_pair _ _).eqTrans (snd_pair _ _).eqSymm))
  ipra_lc natEq (fubini (Γ := Γ) (aP f) (succ (fstT Z)) (succ (fstT Z)) Z) + natEq cs +
    natEq (sum_add (Γ := Γ) (pB (aN f)) (dltB f) (succ (fstT Z)) (pairT (succ (fstT Z)) Z)) + natEq dl -
    natEq (fubini (Γ := Γ) (aN f) (succ (fstT Z)) (succ (fstT Z)) Z)

/-- A row of the double sum in closed form, with a parameter: if `I(e, P)` is the summand
`[e ≥ 1][e ∣ N/d] f(e, Z)` of the inner sum (`hI`) and that sum is `F` whenever `1 ≤ N/d ≤ N` (`hF`), `N = fst Z`,
then the row of `d` is `[d ∣ N] μ^±(d) F`. -/
theorem row_closed_p (I : PTm 2) (d Z P F : PTm n) (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z)))
    (hI : ∀ {Δ : List (Fm PTm (n + 1))}, Δ ⊢[PRAAx]
      (sg (var 0) * eqb (rem (quo (fstT (Syn.shift Z)) (Syn.shift d)) (var 0)) zero) *
          inst2 f (var 0) (Syn.shift Z) ≐ inst2 I (var 0) (Syn.shift P))
    (hF : ∀ {C : List (Fm PTm n)}, (C ⊢[PRAAx] quo (fstT Z) d ≐ succ (pred (quo (fstT Z) d))) →
      (C ⊢[PRAAx] le (succ (quo (fstT Z) d)) (succ (fstT Z))) → (C ⊢[PRAAx] ap2 (sumF I) (succ (fstT Z)) P ≐ F)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP f)) d (pairT (succ (fstT Z)) Z) ≐
        ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) * F) ⋏
      (inst2 (oB (aN f)) d (pairT (succ (fstT Z)) Z) ≐
        ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) * F) := by
  rw [inst2_oB, inst2_oB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ (fstT Z)) Z) ≐ succ (fstT Z) := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ (fstT Z)) Z) ≐ Z := snd_pair _ _
  have hcP : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muP (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muN (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  refine .andI
    ((congrAp2 (sumF (rowB (aP f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aP f)) I (succ (fstT Z)) ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) P
        (pairT d Z) (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
    ((congrAp2 (sumF (rowB (aN f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aN f)) I (succ (fstT Z)) ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) P
        (pairT d Z) (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
  · rw [inst2_rowB, shift_pairT, hcP]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) hI
  · rw [inst2_rowB, shift_pairT, hcN]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) hI

/-- Möbius inversion with a parameter and the rows in closed form: if the row of `d` is `Q^±(d, Z)` (`row`), then
`∑_{d ≤ N} Q⁺(d, Z) = f(N, Z) + ∑_{d ≤ N} Q⁻(d, Z)` for `N = fst Z ≥ 1`. -/
theorem inversion_of_rows_p (QP QN : PTm 2) {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z)))
    (row : ∀ {Δ : List (Fm PTm (n + 1))},
      (Δ ⊢[PRAAx] fstT (Syn.shift Z) ≐ succ (pred (fstT (Syn.shift Z)))) →
      (Δ ⊢[PRAAx] (inst2 (oB (aP f)) (var 0) (pairT (succ (fstT (Syn.shift Z))) (Syn.shift Z)) ≐
          inst2 QP (var 0) (Syn.shift Z)) ⋏
        (inst2 (oB (aN f)) (var 0) (pairT (succ (fstT (Syn.shift Z))) (Syn.shift Z)) ≐
          inst2 QN (var 0) (Syn.shift Z)))) :
    Γ ⊢[PRAAx] ap2 (sumF QP) (succ (fstT Z)) Z ≐ inst2 f (fstT Z) Z + ap2 (sumF QN) (succ (fstT Z)) Z := by
  have inv := mobius_inversion_p (Γ := Γ) f hN
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF QP) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF QN) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row hN'.wk)
  ipra_lc -natEq cP + natEq inv + natEq cN

end Inversion

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP

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

/-! ## The plain inversion, as the instance `Z = ⟨N, 0⟩` -/

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
  simp only [inst3, aP, PTm.subst_mul, subst_reindex2]
  simp
theorem inst3_aN (d e N : PTm n) : inst3 (aN f) d e N =
    ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ((sg e * eqb (rem (quo N d) e) zero) * inst2 f e N) := by
  simp only [inst3, aN, PTm.subst_mul, subst_reindex2]
  simp

/-- `f` read at a packed parameter `Z` through `N = fst Z`. -/
def liftZ : PTm 2 := Syn.subst ![var 0, fstT (var 1)] f

theorem inst2_liftZ (e Z : PTm n) : inst2 (liftZ f) e Z = inst2 f e (fstT Z) := by
  simp only [inst2, liftZ, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- The summands of the plain and of the parameterized double sum agree at `Z` with `fst Z = N`. -/
theorem a_lift {d e N Z : PTm n} (h : Γ ⊢[PRAAx] fstT Z ≐ N) :
    Γ ⊢[PRAAx] (inst3 (aP f) d e N ≐ inst3 (MobiusInversionP.aP (liftZ f)) d e Z) ⋏
      (inst3 (aN f) d e N ≐ inst3 (MobiusInversionP.aN (liftZ f)) d e Z) := by
  rw [inst3_aP, inst3_aN, MobiusInversionP.inst3_aP, MobiusInversionP.inst3_aN, inst2_liftZ]
  have c := congrMu (Γ := Γ) (d := d) (congrSucc h)
  have r₁ : Γ ⊢[PRAAx] sg d * eqb (rem (fstT Z) d) zero ≐ sg d * eqb (rem N d) zero :=
    congrMul (.eqRefl _) (congrEqb' (congrAp2 remF h (.eqRefl _)) (.eqRefl _))
  have r₂ : Γ ⊢[PRAAx] (sg e * eqb (rem (quo (fstT Z) d) e) zero) * inst2 f e (fstT Z) ≐
      (sg e * eqb (rem (quo N d) e) zero) * inst2 f e N :=
    congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (congrAp2 quoF h (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))
      (congrInst2 f (.eqRefl _) h)
  exact .andI (congrMul (congrMul r₁ (Prf.andE₁ c)) r₂).eqSymm (congrMul (congrMul r₁ (Prf.andE₂ c)) r₂).eqSymm

end Inversion

/-- Double sums of two bodies that agree pointwise, one read at `N` and the other at `Z` with `fst Z = N`. -/
theorem oB_sum_congr (a a' : PTm 3) {N Z : PTm n} (M : PTm n) (hZ : Γ ⊢[PRAAx] fstT Z ≐ N)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} {N Z : PTm m}, (Δ ⊢[PRAAx] fstT Z ≐ N) → ∀ d e : PTm m,
      Δ ⊢[PRAAx] inst3 a d e N ≐ inst3 a' d e Z) :
    Γ ⊢[PRAAx] ap2 (sumF (oB a)) M (pairT M N) ≐ ap2 (sumF (oB a')) M (pairT M Z) := by
  have h1 : Γ.map Fm.shift ⊢[PRAAx] fstT (Syn.shift Z) ≐ Syn.shift N := by simpa [Fm.shift, Syn.shift] using hZ.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, inst2_oB, inst2_oB]
  refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
    (Prf.eqTrans ?_ (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm)
  have h2 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      fstT (Syn.shift (Syn.shift Z)) ≐ Syn.shift (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using (h1.wk (ψ := lt (var 0) (Syn.shift M))).shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, inst2_rowB, inst2_rowB]
  exact (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans
    ((h h2.wk _ _).eqTrans (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqSymm)

section Inversion3

variable (f : PTm 2)

/-- Möbius inversion: for `N ≥ 1`,
`∑_{d ∣ N} μ⁺(d) ∑_{e ∣ N/d} f(e) = ∑_{d ∣ N} μ⁻(d) ∑_{e ∣ N/d} f(e) + f(N)`,
i.e. `∑_{d ∣ N} μ(d) F(N/d) = f(N)` for `F(k) = ∑_{e ∣ k} f(e)`. -/
theorem mobius_inversion {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ N) (pairT (succ N) N) ≐
      ap2 (sumF (oB (aN f))) (succ N) (pairT (succ N) N) + inst2 f N N := by
  let Z : PTm n := pairT N zero
  have hZ : Γ ⊢[PRAAx] fstT Z ≐ N := fst_pair _ _
  have b : Γ ⊢[PRAAx] succ N ≐ succ (fstT Z) := congrSucc hZ.eqSymm
  have p := MobiusInversionP.mobius_inversion_p (Γ := Γ) (liftZ f) (Z := Z)
    (hZ.eqTrans (hN.eqTrans (congrSucc (congrPred hZ.eqSymm))))
  rw [inst2_liftZ] at p
  have cP := (oB_sum_congr (aP f) (MobiusInversionP.aP (liftZ f)) (succ N) hZ
    fun h _ _ => Prf.andE₁ (a_lift f h)).eqTrans (congrAp2 _ b (congrPairT b (.eqRefl _)))
  have cN := (oB_sum_congr (aN f) (MobiusInversionP.aN (liftZ f)) (succ N) hZ
    fun h _ _ => Prf.andE₂ (a_lift f h)).eqTrans (congrAp2 _ b (congrPairT b (.eqRefl _)))
  ipra_lc natEq cP + natEq p + natEq (congrInst2 f hZ hZ) - natEq cN

/-- A row of the double sum in closed form. Let `I(e, P)` be the summand `[e ≥ 1][e ∣ N/d] f(e, N)` of the inner
sum (`hI`, under the binder of `e`), and let that sum be `F` whenever `1 ≤ N/d ≤ N` (`hF`). Then the row of `d` is
`[d ∣ N] μ^±(d) F`. -/
theorem row_closed (I : PTm 2) (d N P F : PTm n) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hI : ∀ {Δ : List (Fm PTm (n + 1))}, Δ ⊢[PRAAx]
      (sg (var 0) * eqb (rem (quo (Syn.shift N) (Syn.shift d)) (var 0)) zero) * inst2 f (var 0) (Syn.shift N) ≐
        inst2 I (var 0) (Syn.shift P))
    (hF : ∀ {C : List (Fm PTm n)}, (C ⊢[PRAAx] quo N d ≐ succ (pred (quo N d))) →
      (C ⊢[PRAAx] le (succ (quo N d)) (succ N)) → (C ⊢[PRAAx] ap2 (sumF I) (succ N) P ≐ F)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP f)) d (pairT (succ N) N) ≐ ((sg d * eqb (rem N d) zero) * muP (succ N) d) * F) ⋏
      (inst2 (oB (aN f)) d (pairT (succ N) N) ≐ ((sg d * eqb (rem N d) zero) * muN (succ N) d) * F) := by
  rw [inst2_oB, inst2_oB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ N) N) ≐ succ N := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ N) N) ≐ N := snd_pair _ _
  have hcP : Syn.shift ((sg d * eqb (rem N d) zero) * muP (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muP (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem N d) zero) * muN (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muN (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  refine .andI
    ((congrAp2 (sumF (rowB (aP f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aP f)) I (succ N) ((sg d * eqb (rem N d) zero) * muP (succ N) d) P (pairT d N)
        (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
    ((congrAp2 (sumF (rowB (aN f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aN f)) I (succ N) ((sg d * eqb (rem N d) zero) * muN (succ N) d) P (pairT d N)
        (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
  · rw [inst2_rowB, shift_pairT, hcP]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) hI
  · rw [inst2_rowB, shift_pairT, hcN]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) hI

/-- Möbius inversion with the rows in closed form: if the row of `d` is `Q^±(d, N)` (`row`), then
`∑_{d ≤ N} Q⁺(d, N) = f(N) + ∑_{d ≤ N} Q⁻(d, N)` for `N ≥ 1`. -/
theorem inversion_of_rows (QP QN : PTm 2) {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (row : ∀ {Δ : List (Fm PTm (n + 1))}, (Δ ⊢[PRAAx] Syn.shift N ≐ succ (pred (Syn.shift N))) →
      (Δ ⊢[PRAAx] (inst2 (oB (aP f)) (var 0) (pairT (succ (Syn.shift N)) (Syn.shift N)) ≐
          inst2 QP (var 0) (Syn.shift N)) ⋏
        (inst2 (oB (aN f)) (var 0) (pairT (succ (Syn.shift N)) (Syn.shift N)) ≐ inst2 QN (var 0) (Syn.shift N)))) :
    Γ ⊢[PRAAx] ap2 (sumF QP) (succ N) N ≐ inst2 f N N + ap2 (sumF QN) (succ N) N := by
  have inv := mobius_inversion (Γ := Γ) f hN
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF QP) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN f))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF QN) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row hN'.wk)
  ipra_lc -natEq cP + natEq inv + natEq cN

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
  have r : Γ ⊢[PRAAx] rem k a ≐ k := rem_eq' ha (q := zero) (by ipra_ring) h
  exact (congrEqb' r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hk.wk.eqSymm.eqTrans Prf.hyp0))))

/-- `∑_{e ≤ N} [e ≥ 1][e ∣ k] φ(e) = k` for `1 ≤ k ≤ N`. -/
theorem inner_sum {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF innerB) (succ N) k ≐ k := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF innerB) (succ N) k ≐ ap2 (sumF innerB) (succ k) k := by
    refine sum_ext innerB (fun Δ a hs hl => ?_) hkN
    rw [inst2_inner]
    exact zero_mul_l ((congrMul (.eqRefl _) (eqb_rem_big (hk'.weaken hs) hl)).eqTrans
      (by ipra_ring)) _
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
    exact (congrMul (congrMul s1 (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)

/-- A row of the double sum for `f = φ`: `[d ∣ N] μ^±(d) ∑_{e ∣ N/d} φ(e) = [d ∣ N] μ^±(d) (N/d)`. -/
theorem row_phi {d N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP phiB)) d (pairT (succ N) N) ≐ inst2 QP d N) ⋏
      (inst2 (oB (aN phiB)) d (pairT (succ N) N) ≐ inst2 QN d N) := by
  rw [inst2_QP, inst2_QN]
  refine row_closed phiB innerB d N (quo N d) (quo N d) hN ?_ fun hk hkN => inner_sum hk hkN
  intro Δ
  rw [show Syn.shift (quo N d) = quo (Syn.shift N) (Syn.shift d) by simp [Syn.shift], inst2_inner, inst2_phiB]
  exact .eqRefl _

/-- `cor:phi-mobius`: `φ(N) = ∑_{d ∣ N} μ(d) N/d` for `N ≥ 1`, as
`∑_{d ∣ N} μ⁺(d) N/d = φ(N) + ∑_{d ∣ N} μ⁻(d) N/d`. -/
theorem phi_mobius {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF QP) (succ N) N ≐ Totient.phi N + ap2 (sumF QN) (succ N) N := by
  have h := inversion_of_rows phiB QP QN hN fun h => row_phi h
  rwa [inst2_phiB] at h

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion
