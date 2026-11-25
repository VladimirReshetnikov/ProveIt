import IPRADerivations.AnalyticNumberTheory.ContractionMain
import IPRADerivations.AnalyticNumberTheory.WeightedAbel
import IPRADerivations.Core.LinearCombination

/-!
# Splitting the weighted sum of the contraction (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of `con:one-step`:
"`∫_0^t (t − u)|r(u)| du ≤ a t²/2 + 4st − …` … The term `4st` bounds the possible excess above the baseline `a`
on `[0, s]`, using (con:global)." In the discrete weighted inequality (`WeightedAbel.weighted_sum`) the integral is
the sum `W(x) = Σ_{1≤d≤x} 2F u_d |R(⌊x/d⌋)|`, `R(m) = ψ(m) − Fm`, `F = L!`. Here it is split at `d = N = M + 1`:

* `body_at`, `body_zero`, `body_one`: the body at `d = j + 2`, and its vanishing at `d = 0, 1` (`u_1 = 0`);
* `head_bound`: if the stage bound `D |R(m)| ≤ A F m` holds for `Y ≤ m ≤ x` and `NY ≤ x`, then
  `D Σ_{d≤N} 2F u_d |R(⌊x/d⌋)| ≤ A F x (u_N² + 2F²)` (`ContractionMain.main_term`): the baseline `a t²/2`;
* `tail_bound`: the global bound `|R(m)| ≤ 4Fm` (`con:global`) gives
  `Σ_{N<d≤x} 2F u_d |R(⌊x/d⌋)| + 4Fx u_N² ≤ 4Fx (u_x² + 2F²)` (half-square identity): the excess `4st`;
* `no_growth`: `D W(x) + 4DFx u_N² ≤ AFx (u_N² + 2F²) + 4DFx (u_x² + 2F²)`.

The stage hypothesis is an iPRA formula `∀m < x + 1. Y ≤ m → D|R(m)| ≤ AFm`, instantiated under the sum binder.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB pos_of_lt_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le adB inst2_adB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB qB inst2_psiB inst2_qB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit (uw uw_at hRB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedAbel (a2 inst2_a2)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (psi_k)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicHalfSquare (udB ddB dlB u2B Dl dl_at u2_at half_square dd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionMain (dl_ge fq_le mtB inst2_mtB main_term)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (shift_succ_x)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The weighted-sum body `[d ≥ 1] 2F u_d |ψ(⌊x/d⌋) − F⌊x/d⌋|` over `0 = d`, `1 = (x, (K, F))`. -/
abbrev wbB : PTm 2 := hRB (adB psiB qB) a2

/-- The body at `d = j + 2`, evaluated. -/
abbrev Bd (j x K L : PTm n) : PTm n :=
  two * (fact L * U (succ (succ j)) K (fact L)) *
    absd (Psi wt (quo x (succ (succ j))) (pairT K (fact L))) (fact L * quo x (succ (succ j)))

theorem body_at (j x K L : PTm n) :
    Γ ⊢[PRAAx] inst2 wbB (succ (succ j)) (pairT x (pairT K (fact L))) ≐ Bd j x K L := by
  refine (hRB_at _ _ _ _ _).eqTrans ?_
  rw [inst2_a2, inst2_adB, inst2_psiB, inst2_qB]
  have e : Γ ⊢[PRAAx] sndT (pairT K (fact L)) * quo x (succ (succ j)) ≐ fact L * quo x (succ (succ j)) :=
    congrMul (snd_pair _ _) (.eqRefl _)
  have l : Γ ⊢[PRAAx] sg (succ (succ j)) *
      (two * (sndT (pairT K (fact L)) * inst2 uw (succ (succ j)) (pairT K (fact L)))) ≐
      two * (fact L * U (succ (succ j)) K (fact L)) :=
    (congrMul (sg_succ _) (congrMul (.eqRefl two) (congrMul (snd_pair _ _) (uw_at _ _ _)))).eqTrans
      (by ipra_ring)
  exact congrMul l (congrAdd (congrMonus (.eqRefl _) e) (congrMonus e (.eqRefl _)))

theorem body_zero (x K L : PTm n) : Γ ⊢[PRAAx] inst2 wbB zero (pairT x (pairT K (fact L))) ≐ zero :=
  (hRB_at _ _ _ _ _).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)

theorem body_one (x K L : PTm n) : Γ ⊢[PRAAx] inst2 wbB (succ zero) (pairT x (pairT K (fact L))) ≐ zero := by
  refine (hRB_at _ _ _ _ _).eqTrans (zero_mul_l ?_ _)
  rw [inst2_a2]
  have k1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
  have u1 : Γ ⊢[PRAAx] U (succ zero) K (fact L) ≐ zero :=
    (congrMonus (congrAp2 (sumF hB) k1 (.eqRefl (fact L))) (.eqRefl _)).eqTrans (le_refl _)
  have u := (uw_at (Γ := Γ) (succ zero) K (fact L)).eqTrans u1
  exact (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) u))).eqTrans
    (by ipra_ring)

/-- `Σ_{d<M+2} body(d) = Σ_{j<M} body(j+2)`. -/
theorem head_eq (M x K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF wbB) (succ (succ M)) (pairT x (pairT K (fact L))) ≐
      ap2 (sumF (shiftBody (shiftBody wbB))) M (pairT x (pairT K (fact L))) := by
  have s1 := sum_shift (Γ := Γ) wbB (succ M) (pairT x (pairT K (fact L)))
  have s2 := sum_shift (Γ := Γ) (shiftBody wbB) M (pairT x (pairT K (fact L)))
  rw [inst2_shiftBody] at s2
  exact s1.eqTrans ((congrAdd (body_zero _ _ _)
    (s2.eqTrans ((congrAdd (body_one _ _ _) (.eqRefl _)).eqTrans (zero_add _)))).eqTrans (zero_add _))

theorem mt_at (j x K L : PTm n) :
    Γ ⊢[PRAAx] inst2 mtB j (pairT x (pairT K (fact L))) ≐
      U (succ (succ j)) K (fact L) * (fact L * quo x (succ (succ j))) := by
  rw [inst2_mtB]
  have e1 : Γ ⊢[PRAAx] inst2 u2B j (sndT (pairT x (pairT K (fact L)))) ≐ U (succ (succ j)) K (fact L) :=
    (congrInst2 u2B (.eqRefl _) (snd_pair _ _)).eqTrans (u2_at _ _ _)
  have e2 : Γ ⊢[PRAAx] sndT (sndT (pairT x (pairT K (fact L)))) ≐ fact L :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have e3 : Γ ⊢[PRAAx] quo (fstT (pairT x (pairT K (fact L)))) (succ (succ j)) ≐ quo x (succ (succ j)) :=
    congrAp2 quoF (fst_pair _ _) (.eqRefl _)
  exact congrMul e1 (congrMul e2 e3)

/-- `D · body(j+2) ≤ 2AF · u_{j+2} F⌊x/(j+2)⌋` from the stage bound at `m = ⌊x/(j+2)⌋`. -/
theorem head_pt {j x K L D A : PTm n}
    (hs : Γ ⊢[PRAAx] le (D * absd (Psi wt (quo x (succ (succ j))) (pairT K (fact L)))
        (fact L * quo x (succ (succ j)))) (A * (fact L * quo x (succ (succ j))))) :
    Γ ⊢[PRAAx] le (D * inst2 wbB (succ (succ j)) (pairT x (pairT K (fact L))))
      (two * (A * fact L) * inst2 mtB j (pairT x (pairT K (fact L)))) := by
  have b := natEq (body_at (Γ := Γ) j x K L)
  have m := natEq (mt_at (Γ := Γ) j x K L)
  have p := le_scale (two * (fact L * U (succ (succ j)) K (fact L))) hs
  ipra_le sl p with 𝔞 D * b - 2 * 𝔞 A * 𝔞 (fact L) * m

/-- The stage hypothesis `∀m < x + 1. Y ≤ m → D|ψ(m) − Fm| ≤ AFm`. -/
abbrev Stage (x Y D A K L : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift (succ x)) ⟶ (le (Syn.shift Y) (var 0) ⟶
    le (Syn.shift D * absd (Psi wt (var 0) (Syn.shift (pairT K (fact L)))) (Syn.shift (fact L) * var 0))
      (Syn.shift A * (Syn.shift (fact L) * var 0))))

/-- The head `d ≤ N = M + 1`: `D Σ_{d≤N} 2F u_d |R(⌊x/d⌋)| ≤ A F x (u_N² + 2F²)` under the stage bound, `NY ≤ x`. -/
theorem head_bound {M x K L D A Y : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ M) L)
    (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hst : Γ ⊢[PRAAx] Stage x Y D A K L) :
    Γ ⊢[PRAAx] le (D * ap2 (sumF wbB) (succ (succ M)) (pairT x (pairT K (fact L))))
      (A * (fact L * (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L))))) := by
  have hY' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift M) * Syn.shift Y) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift] using hY.shift
  have p := sum_le_params (Γ := Γ) (cmB (shiftBody (shiftBody wbB))) (cmB mtB)
    (pairT D (pairT x (pairT K (fact L)))) (pairT (two * (A * fact L)) (pairT x (pairT K (fact L)))) M
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact']
      rw [show Syn.shift (two * (A * fact L)) = two * (Syn.shift A * fact (Syn.shift L)) by simp [Syn.shift]]
      refine le_congr (cm_pt _ _ _ _).eqSymm (cm_pt _ _ _ _).eqSymm ?_
      rw [inst2_shiftBody, inst2_shiftBody]
      have hv : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift M) := Prf.hyp0
      have a := Prf.allE (quo (Syn.shift x) (succ (succ (var 0)))) hst.shift
      simp only [Stage, Fm.shift, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_le, subst_lt, subst_ap2,
        PTm.subst_mul, PTm.subst_add, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.up_zero, Syn.inst_zero, subst_up_shift_pal, Syn.subst_inst_shift] at a
      have h1 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (quo (Syn.shift x) (succ (succ (var 0)))) (succ (Syn.shift x)) :=
        (succ_monus_succ _ _).eqTrans (quo_le_self (succ (var 0)) (Syn.shift x))
      have hvM : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (succ (var 0))) (succ (Syn.shift M)) :=
        (succ_monus_succ _ _).eqTrans hv
      have hk : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          succ (succ (var 0)) ≐ succ (pred (succ (succ (var 0)))) := congrSucc (pred_succ _).eqSymm
      have h2 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift Y) (quo (Syn.shift x) (succ (succ (var 0)))) :=
        le_quo_of_mul_le hk (le_trans (mul_le_mul_right (Syn.shift Y) hvM) hY'.wk)
      have a' : (Γ.map Fm.shift) ⊢[PRAAx] lt (quo (Syn.shift x) (succ (succ (var 0)))) (succ (Syn.shift x)) ⟶
          (le (Syn.shift Y) (quo (Syn.shift x) (succ (succ (var 0)))) ⟶
            le (Syn.shift D * absd (Psi wt (quo (Syn.shift x) (succ (succ (var 0))))
                (pairT (Syn.shift K) (fact (Syn.shift L)))) (fact (Syn.shift L) * quo (Syn.shift x) (succ (succ (var 0)))))
              (Syn.shift A * (fact (Syn.shift L) * quo (Syn.shift x) (succ (succ (var 0)))))) := by
        simpa [Syn.shift] using a
      exact head_pt (Prf.impE (Prf.impE a'.wk h1) h2))))
  have he := natEq (head_eq (Γ := Γ) M x K L)
  have c1 := natEq (sum_const_mul (Γ := Γ) (shiftBody (shiftBody wbB)) M D (pairT x (pairT K (fact L))))
  have c2 := natEq (sum_const_mul (Γ := Γ) mtB M (two * (A * fact L)) (pairT x (pairT K (fact L))))
  have mt := main_term (Γ := Γ) (x := x) hK hL
  ipra_le sl p + 𝔞 A * 𝔞 (fact L) * sl mt with c1 - 𝔞 D * he - c2

/-- One tail term: `body(j+2) ≤ 8Fx u_{j+2} Δ_{j+2}` for `j + 2 ≤ x`, from `|R(m)| ≤ 4Fm` and `F⌊x/m⌋ ≤ xΔ_m`. -/
theorem tail_pt {j x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hj : Γ ⊢[PRAAx] le (succ (succ j)) x) :
    Γ ⊢[PRAAx] le (inst2 wbB (succ (succ j)) (pairT x (pairT K (fact L))))
      (two * (two * (two * (fact L * x))) * (U (succ (succ j)) K (fact L) * Dl j K (fact L))) := by
  have b := natEq (body_at (Γ := Γ) j x K L)
  have qx := quo_le_self (Γ := Γ) (succ j) x
  have ps := psi_k hK hP qx
  have ab : Γ ⊢[PRAAx] le (absd (Psi wt (quo x (succ (succ j))) (pairT K (fact L))) (fact L * quo x (succ (succ j))))
      (two * (two * (fact L * quo x (succ (succ j))))) :=
    absd_le (by ipra_le sl ps + 𝔞 (fact L) * 𝔞 (quo x (succ (succ j))))
      (by ipra_le 𝔞 (Psi wt (quo x (succ (succ j))) (pairT K (fact L))) +
        3 * 𝔞 (fact L) * 𝔞 (quo x (succ (succ j))))
  have hL' : Γ ⊢[PRAAx] le (K * succ (succ j)) L := le_trans (le_scale K hj) hKx
  have hsj : Γ ⊢[PRAAx] succ (succ j) ≐ succ (pred (succ (succ j))) := congrSucc (pred_succ _).eqSymm
  have hjL : Γ ⊢[PRAAx] le (succ (succ j)) L := by
    have h1 : Γ ⊢[PRAAx] le (succ (succ j)) (K * succ (succ j)) :=
      le_of_eq_add (d := pred K * succ (succ j)) (by
        ipra_lc (𝔞 j + 2) * natEq (pos_of_lt_zero hK))
    exact le_trans h1 hL'
  have f := fq_le (x := x) hsj hjL
  have d := le_scale x (dl_ge hK hL')
  have ad := le_trans ab (le_scale two (le_scale two (le_trans f d)))
  have p := le_scale (two * (fact L * U (succ (succ j)) K (fact L))) ad
  ipra_le sl p with b

/-- A tail term in split coordinates: `body(M + 2 + i) ≤ 8Fx · u Δ` at index `M + i` of the half-square sum. -/
theorem tail_off {i M x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) (hi : Γ ⊢[PRAAx] lt i (monus x (succ M))) :
    Γ ⊢[PRAAx] le (inst2 (offB wbB) i (pairT (succ (succ M)) (pairT x (pairT K (fact L)))))
      (inst2 (cmB (offB udB)) i (pairT (two * (two * (two * (fact L * x)))) (pairT M (pairT K (fact L))))) := by
  have e1 : Γ ⊢[PRAAx] inst2 (offB wbB) i (pairT (succ (succ M)) (pairT x (pairT K (fact L)))) ≐
      inst2 wbB (succ (succ (M + i))) (pairT x (pairT K (fact L))) := by
    rw [inst2_offB]
    exact congrInst2 wbB ((congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (by ipra_ring))
      (snd_pair _ _)
  have e2 : Γ ⊢[PRAAx] inst2 (cmB (offB udB)) i (pairT (two * (two * (two * (fact L * x)))) (pairT M (pairT K (fact L)))) ≐
      two * (two * (two * (fact L * x))) * (U (succ (succ (M + i))) K (fact L) * Dl (M + i) K (fact L)) := by
    refine (cm_pt _ _ _ _).eqTrans (congrMul (.eqRefl _) ?_)
    rw [inst2_offB]
    refine (congrInst2 udB (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ?_
    rw [show inst2 udB (M + i) (pairT K (fact L)) =
      inst2 u2B (M + i) (pairT K (fact L)) * inst2 dlB (M + i) (pairT K (fact L)) by simp [inst2]]
    exact congrMul (u2_at _ _ _) (dl_at _ _ _)
  have hj : Γ ⊢[PRAAx] le (succ (succ (M + i))) x :=
    le_of_eq_add (d := monus (monus x (succ M)) (succ i)) (by
      ipra_lc natEq (eq_add_of_le hMx) + natEq (eq_add_of_le hi))
  exact le_congr e1.eqSymm e2.eqSymm (tail_pt hK hP hKx hj)

/-- The tail `N < d ≤ x`, `N = M + 1`: `Σ 2F u_d |R(⌊x/d⌋)| + 4Fx u_N² ≤ 4Fx (u_x² + 2F²)`. -/
theorem tail_bound {M x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) :
    Γ ⊢[PRAAx] le (ap2 (sumF (offB wbB)) (monus x (succ M)) (pairT (succ (succ M)) (pairT x (pairT K (fact L)))) +
        num 4 * (fact L * x) * (U (succ M) K (fact L) * U (succ M) K (fact L)))
      (num 4 * (fact L * x) * (U x K (fact L) * U x K (fact L) + two * (fact L * fact L))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have hMx' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift M)) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift] using hMx.shift
  have p := sum_le_params (Γ := Γ) (offB wbB) (cmB (offB udB)) (pairT (succ (succ M)) (pairT x (pairT K (fact L))))
    (pairT (two * (two * (two * (fact L * x)))) (pairT M (pairT K (fact L)))) (monus x (succ M))
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact', shift_succ_x]
      rw [show Syn.shift (two * (two * (two * (fact L * x)))) =
        two * (two * (two * (fact (Syn.shift L) * Syn.shift x))) by simp [Syn.shift]]
      have hi : (lt (var 0) (Syn.shift (monus x (succ M))) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (var 0) (monus (Syn.shift x) (succ (Syn.shift M))) := by
        have e : Syn.shift (monus x (succ M)) = monus (Syn.shift x) (succ (Syn.shift M)) := by simp [Syn.shift]
        have h0 : (lt (var 0) (Syn.shift (monus x (succ M))) :: Γ.map Fm.shift) ⊢[PRAAx]
            lt (var 0) (Syn.shift (monus x (succ M))) := Prf.hyp0
        rw [e] at h0 ⊢; exact h0
      exact tail_off hK'.wk hP'.wk hKx'.wk hMx'.wk hi)))
  have c := natEq (sum_const_mul (Γ := Γ) (offB udB) (monus x (succ M)) (two * (two * (two * (fact L * x))))
    (pairT M (pairT K (fact L))))
  have spu := natEq (sum_split (Γ := Γ) udB M (monus x (succ M)) (pairT K (fact L)))
  have hsA := natEq (half_square (Γ := Γ) (M + monus x (succ M)) K (fact L))
  have hsM := natEq (half_square (Γ := Γ) M K (fact L))
  have dd := dd_le (Γ := Γ) (M + monus x (succ M)) (fact L) hK
  have ex : Γ ⊢[PRAAx] K * succ (M + monus x (succ M)) ≐ K * x := by
    ipra_lc (-𝔞 K) * natEq (eq_add_of_le hMx)
  have eU := natEq ((congrMonus (congrAp2 (sumF hB) ex (.eqRefl (fact L))) (.eqRefl _) :
    Γ ⊢[PRAAx] U (succ (M + monus x (succ M))) K (fact L) ≐ U x K (fact L)))
  ipra_le sl p + 4 * 𝔞 (fact L) * 𝔞 x * sl dd +
      4 * 𝔞 (fact L) * 𝔞 x * 𝔞 (ap2 (sumF ddB) M (pairT K (fact L))) with
    4 * 𝔞 (fact L) * 𝔞 x * (hsM - hsA + 2 * spu -
      (𝔞 (U (succ (M + monus x (succ M))) K (fact L)) + 𝔞 (U x K (fact L))) * eU) - c

/-- The no-growth bound, `N = M + 1`, `NY ≤ x`, stage bound on `[Y, x]`:
`D W(x) + 4DFx u_N² ≤ AFx (u_N² + 2F²) + 4DFx (u_x² + 2F²)`. -/
theorem no_growth {M x K L D A Y : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hst : Γ ⊢[PRAAx] Stage x Y D A K L) :
    Γ ⊢[PRAAx] le (D * ap2 (sumF wbB) (succ x) (pairT x (pairT K (fact L))) +
        num 4 * D * (fact L * x) * (U (succ M) K (fact L) * U (succ M) K (fact L)))
      (A * (fact L * (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L)))) +
        num 4 * D * (fact L * x) * (U x K (fact L) * U x K (fact L) + two * (fact L * fact L))) := by
  have hL : Γ ⊢[PRAAx] le (K * succ M) L := le_trans (le_scale K hMx) hKx
  have h := head_bound hK hL hY hst
  have t := le_scale D (tail_bound hK hP hKx hMx)
  have ex : Γ ⊢[PRAAx] succ x ≐ succ (succ M) + monus x (succ M) := by
    ipra_lc natEq (eq_add_of_le hMx)
  have sp := natEq ((congrAp2 (sumF wbB) ex (.eqRefl _)).eqTrans
    (sum_split (Γ := Γ) wbB (succ (succ M)) (monus x (succ M)) (pairT x (pairT K (fact L)))))
  ipra_le sl h + sl t with 𝔞 D * sp

end LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit
