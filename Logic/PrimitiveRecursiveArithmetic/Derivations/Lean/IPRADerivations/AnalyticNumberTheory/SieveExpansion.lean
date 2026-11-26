import IPRADerivations.AnalyticNumberTheory.SievePairSum
import IPRADerivations.AnalyticNumberTheory.SieveSquare
import IPRADerivations.Foundations.DoubleSumScale
import IPRADerivations.Core.Header

/-!
# The expanded square over a progression as a double sum of pair counts

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
"Sum `eq:sieve-majorant` over the progression. Expanding its square …" — the sum over the progression of a product of
two weighted divisor sums is the double sum, over the pairs `(d, e)`, of the weights times the number of `n` in the
progression divisible by `[d, e]`.

With the parameter `P` (read as `q = fst P`, `a = fst (snd P)`), natural weight bodies `U(d, P)`, `V(e, P)` and

* `cB`: the indicator `[m ≡ a (mod q)]` over `(m, P)`;
* `lB U`: the weight `λ_d = d · [d ≥ 1][gcd(d, q) = 1] · U(d, P)` (so `U_d` stands for `λ_d / d`),

the module derives, for every `X`, `Z` and `P`,

  `Σ_{d<Z} Σ_{e<Z} Am(d, e) = χ · q · Σ_{m<X} [m ≡ a] (Σ_{e<Z} [e ∣ m] λ'_e) (Σ_{d<Z} [d ∣ m] λ_d)`      (`expansion`),

where `Am` is the body of `SievePairSum` (the pair counts `K = cnt X q (lc d e) a` with their indicator `ind`) and
`χ = [2 ≤ q][gcd(a, q) = 1]`. No hypothesis on `q` and `a` is needed: the indicators make both sides vanish outside
the range of `SieveCount`.

* `kn_cnt`: for `d, e ≥ 1` and `q ≥ 1`, the nested count `Σ_{m<X} [m ≡ a][d ∣ m][e ∣ m]` is `cnt X q (lc d e) a`;
* `eqb_factor_eq`, `sg_factor_eq`: an equation under a hypothesis holds outright with the indicator of the hypothesis;
* `pair_id`: the summand identity, at all terms;
* `row_F`: one row of the double sum is the outer body `SqR` of `SieveSquare`;
* `expansion`: `Foundations/DoubleSumScale.dsum_scale`, `Independence.dsum_rows` and `SieveSquare.square_exchange`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BrunCounting (gB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveCount (fB cnt)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount (lc pair_pt)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum (subst_gcd' subst_lc Am inst3_Am inst3_wB)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (mdB LW RW)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveSquare (SqR SqR_at inR_pt K_pt square_exchange)
open LeanProofs.IPRA.Foundations.DoubleSumScale (at1 dsum_scale)
open LeanProofs.IPRA.Probability.Independence (row_pt sum_scale dsum dsum_rows shift_inst2)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The progression indicator and the weights -/

/-- `[m ≡ a (mod q)]` over `0 = m`, `1 = P`, with `q = fst P`, `a = fst (snd P)`. -/
abbrev cB : PTm 2 := eqb (rem (var 0) (fstT (var 1))) (rem (fstT (sndT (var 1))) (fstT (var 1)))

theorem inst2_cB (m P : PTm n) :
    inst2 cB m P = eqb (rem m (fstT P)) (rem (fstT (sndT P)) (fstT P)) := by simp [inst2]

/-- `d · [d ≥ 1][gcd(d, q) = 1] · U(d, P)` over `0 = d`, `1 = P`. -/
def lB (U : PTm 2) : PTm 2 := var 0 * ((sg (var 0) * eqb (gcd (var 0) (fstT (var 1))) one) * U)

theorem inst2_lB (U : PTm 2) (d P : PTm n) :
    inst2 (lB U) d P = d * ((sg d * eqb (gcd d (fstT P)) one) * inst2 U d P) := by
  simp only [inst2, lB, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, LeanProofs.IPRA.PTm.subst_monus, subst_gcd',
    subst_fstT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-! ## The nested count is the progression count at the least common multiple -/

/-- `Σ_{m<X} [m ≡ a (mod q)][d ∣ m][e ∣ m] = cnt X q (lc d e) a` for `d, e ≥ 1` and `q ≥ 1`. -/
theorem kn_cnt {d e P : PTm n} (X : PTm n) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (mdB (mdB cB))) X (pairT e (pairT d P)) ≐
      cnt X (fstT P) (lc d e) (fstT (sndT P)) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have hd' := MobiusBounds.shift_pos hd
  have he' := MobiusBounds.shift_pos he
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have sh1 : Syn.shift (pairT e (pairT d P)) = pairT (Syn.shift e) (pairT (Syn.shift d) (Syn.shift P)) := by
    simp only [Syn.shift, subst_pairT]
  have sh2 : Syn.shift (pairT (succ (pred (fstT P * lc d e))) (SieveCount.par (fstT P) (lc d e) (fstT (sndT P)))) =
      pairT (succ (pred (fstT (Syn.shift P) * lc (Syn.shift d) (Syn.shift e))))
        (SieveCount.par (fstT (Syn.shift P)) (lc (Syn.shift d) (Syn.shift e)) (fstT (sndT (Syn.shift P)))) := by
    simp only [Syn.shift, SieveCount.par, subst_pairT, subst_fstT, subst_sndT, ConciseIPRA.PTm.subst_succ,
      LeanProofs.IPRA.PTm.subst_pred, LeanProofs.IPRA.PTm.subst_mul, lc, subst_ap2, subst_gcd']
  rw [sh1, sh2]
  refine (K_pt cB (var 0) (Syn.shift e) (Syn.shift d) (Syn.shift P)).eqTrans ?_
  rw [inst2_cB]
  exact (mul_assoc _ _ _).eqTrans (pair_pt hd'.wk he'.wk hq'.wk (var 0))

/-! ## Equations with indicator factors -/

theorem eqb_factor_eq {s t R A B : PTm n} (h : ((s ≐ t) :: Γ) ⊢[PRAAx] R * A ≐ R * B) :
    Γ ⊢[PRAAx] (eqb s t * R) * A ≐ (eqb s t * R) * B := by
  refine .orE (eq_or_ne s t) ?_ ?_
  · have e1 : ((s ≐ t) :: Γ) ⊢[PRAAx] eqb s t ≐ one := eqb_of_eq Prf.hyp0
    have c : ∀ Y : PTm n, ((s ≐ t) :: Γ) ⊢[PRAAx] (eqb s t * R) * Y ≐ R * Y := fun Y =>
      congrMul ((congrMul e1 (.eqRefl _)).eqTrans (one_mul R)) (.eqRefl _)
    exact (c A).eqTrans (h.eqTrans (c B).eqSymm)
  · have e0 : (neg (s ≐ t) :: Γ) ⊢[PRAAx] eqb s t ≐ zero := eqb_of_ne Prf.hyp0
    have z : ∀ Y : PTm n, (neg (s ≐ t) :: Γ) ⊢[PRAAx] (eqb s t * R) * Y ≐ zero := fun Y =>
      zero_mul_l (zero_mul_l e0 R) Y
    exact (z A).eqTrans (z B).eqSymm

theorem sg_factor_eq {d R A B : PTm n} (h : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] R * A ≐ R * B) :
    Γ ⊢[PRAAx] (sg d * R) * A ≐ (sg d * R) * B := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have e0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have z : ∀ Y : PTm n, ((d ≐ zero) :: Γ) ⊢[PRAAx] (sg d * R) * Y ≐ zero := fun Y =>
      zero_mul_l (zero_mul_l e0 R) Y
    exact (z A).eqTrans (z B).eqSymm
  · have e1 : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d ≐ one := sg_pos Prf.hyp0
    have c : ∀ Y : PTm n, ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] (sg d * R) * Y ≐ R * Y := fun Y =>
      congrMul ((congrMul e1 (.eqRefl _)).eqTrans (one_mul R)) (.eqRefl _)
    exact (c A).eqTrans (h.eqTrans (c B).eqSymm)

theorem one_factor_eq {A B : PTm n} (h : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx] one * A ≐ one * B :=
  congrMul (.eqRefl _) h

/-! ## The summand identity -/

/-- With the indicator, the pair count may be replaced by the nested count. -/
theorem ind_cnt (W d e X P : PTm n) :
    Γ ⊢[PRAAx] SievePairBound.ind d e (fstT P) (fstT (sndT P)) *
        (W * (fstT P * (d * e) * cnt X (fstT P) (lc d e) (fstT (sndT P)))) ≐
      SievePairBound.ind d e (fstT P) (fstT (sndT P)) *
        (W * (fstT P * (d * e) * ap2 (sumF (mdB (mdB cB))) X (pairT e (pairT d P)))) := by
  refine eqb_factor_eq (eqb_factor_eq (sg_factor_eq (eqb_factor_eq (sg_factor_eq (eqb_factor_eq
    (one_factor_eq ?_))))))
  let C1 : List (Fm PTm n) := (monus one (fstT P) ≐ zero) :: Γ
  let C2 : List (Fm PTm n) := (gcd (fstT (sndT P)) (fstT P) ≐ one) :: C1
  let C3 : List (Fm PTm n) := (d ≐ succ (pred d)) :: C2
  let C4 : List (Fm PTm n) := (gcd d (fstT P) ≐ one) :: C3
  let C5 : List (Fm PTm n) := (e ≐ succ (pred e)) :: C4
  let C6 : List (Fm PTm n) := (gcd e (fstT P) ≐ one) :: C5
  have hq : C6 ⊢[PRAAx] le one (fstT P) := (Prf.hyp0 : C1 ⊢[PRAAx] monus one (fstT P) ≐ zero).wk.wk.wk.wk.wk
  have hd : C6 ⊢[PRAAx] d ≐ succ (pred d) := (Prf.hyp0 : C3 ⊢[PRAAx] d ≐ succ (pred d)).wk.wk.wk
  have he : C6 ⊢[PRAAx] e ≐ succ (pred e) := (Prf.hyp0 : C5 ⊢[PRAAx] e ≐ succ (pred e)).wk
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (kn_cnt X hd he hq).eqSymm)

/-- The rearrangement of the weights: `(χ q) · (λ_d (λ'_e K)) = ind · ((U_d V_e) (q (d e) K))`. -/
theorem weights_alg (c1 c2 sd gd se ge Ud Ve q d e K : PTm n) :
    Γ ⊢[PRAAx] ((c1 * c2) * q) * ((d * ((sd * gd) * Ud)) * ((e * ((se * ge) * Ve)) * K)) ≐
      (c1 * (c2 * (sd * (gd * (se * (ge * one)))))) * ((Ud * Ve) * (q * (d * e) * K)) := by
  ipra_ring

section Expansion

variable (U V : PTm 2)

/-- `λ_d · (λ'_e · Σ_{m<X} [m ≡ a][d ∣ m][e ∣ m])` over `(d, e, ⟨X, P⟩)`. -/
def Fb : PTm 3 :=
  Syn.subst ![var 0, sndT (var 2)] (lB U) *
    (Syn.subst ![var 1, sndT (var 2)] (lB V) *
      ap2 (sumF (mdB (mdB cB))) (fstT (var 2)) (pairT (var 1) (pairT (var 0) (sndT (var 2)))))

theorem inst3_Fb (i j y : PTm n) : inst3 (Fb U V) i j y =
    inst2 (lB U) i (sndT y) *
      (inst2 (lB V) j (sndT y) * ap2 (sumF (mdB (mdB cB))) (fstT y) (pairT j (pairT i (sndT y)))) := by
  have h1 : Syn.subst ![i, j, y] (Syn.subst ![var 0, sndT (var 2)] (lB U)) = inst2 (lB U) i (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have h2 : Syn.subst ![i, j, y] (Syn.subst ![var 1, sndT (var 2)] (lB V)) = inst2 (lB V) j (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, Fb, LeanProofs.IPRA.PTm.subst_mul, h1, h2, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- `χ · q` as a term in the parameter `y = ⟨X, P⟩`. -/
def kT : PTm 1 :=
  (eqb (monus one (fstT (sndT (var 0)))) zero * eqb (gcd (fstT (sndT (sndT (var 0)))) (fstT (sndT (var 0)))) one) *
    fstT (sndT (var 0))

theorem at1_kT (y : PTm n) : at1 kT y =
    (eqb (monus one (fstT (sndT y))) zero * eqb (gcd (fstT (sndT (sndT y))) (fstT (sndT y))) one) *
      fstT (sndT y) := by
  simp only [at1, kT, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, LeanProofs.IPRA.PTm.subst_monus, subst_gcd',
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

/-- The summand identity at all terms: `Am(i, j, y) = χ q · Fb(i, j, y)`. -/
theorem pair_id (i j y : PTm n) :
    Γ ⊢[PRAAx] inst3 (Am U V) i j y ≐ at1 kT y * inst3 (Fb U V) i j y := by
  rw [inst3_Am, inst3_wB, at1_kT, inst3_Fb, inst2_lB, inst2_lB]
  refine (ind_cnt (inst2 U i (sndT y) * inst2 V j (sndT y)) i j (fstT y) (sndT y)).eqTrans ?_
  exact (weights_alg _ _ _ _ _ _ _ _ _ _ _ _).eqSymm

/-- One row of the double sum of `Fb` is the outer body `SqR` of the expanded square. -/
theorem row_F (d X Z P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (Fb U V))) Z (pairT d (pairT X P)) ≐
      inst2 (SqR cB (lB U) (lB V)) d (pairT X (pairT Z P)) := by
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (Fb U V))) Z (pairT d (pairT X P)) ≐
      inst2 (lB U) d P * ap2 (sumF (RW (mdB cB) (sndB (lB V)))) Z (pairT X (pairT d P)) := by
    refine sum_scale (rowB (Fb U V)) (RW (mdB cB) (sndB (lB V))) Z (inst2 (lB U) d P) (pairT X (pairT d P))
      (pairT d (pairT X P)) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [shift_inst2]
    refine (row_pt (Fb U V) _ _ _).eqTrans ?_
    rw [inst3_Fb]
    have f1 := fst_pair (Γ := lt (var 0) (Syn.shift Z) :: Γ.map Fm.shift) (Syn.shift X) (Syn.shift P)
    have s1 := snd_pair (Γ := lt (var 0) (Syn.shift Z) :: Γ.map Fm.shift) (Syn.shift X) (Syn.shift P)
    refine (congrMul (congrInst2 (lB U) (.eqRefl _) s1) (congrMul (congrInst2 (lB V) (.eqRefl _) s1)
      (congrAp2 _ f1 (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) s1))))).eqTrans ?_
    exact congrMul (.eqRefl _) (inR_pt cB (lB V) _ _ _ _).eqSymm
  exact sc.eqTrans (SqR_at cB (lB U) (lB V) d X Z P).eqSymm

/-- The expanded square over the progression, times `χ q`, is the double sum of the pair counts. -/
theorem expansion (X Z P : PTm n) :
    Γ ⊢[PRAAx] dsum (Am U V) Z Z (pairT X P) ≐
      at1 kT (pairT X P) *
        ap2 (sumF (LW (LW cB (lB V)) (sndB (lB U)))) X (pairT Z (pairT Z P)) := by
  have e1 := dsum_scale (Γ := Γ) (Am U V) (Fb U V) kT (fun i j y => pair_id U V i j y) Z Z (pairT X P)
  have e2 : Γ ⊢[PRAAx] dsum (Fb U V) Z Z (pairT X P) ≐
      ap2 (sumF (SqR cB (lB U) (lB V))) Z (pairT X (pairT Z P)) := by
    refine dsum_rows (Fb U V) (SqR cB (lB U) (lB V)) Z Z (pairT X P) (pairT X (pairT Z P)) (.allI (.impI ?_))
    simp only [shift_pairT]
    exact row_F U V _ _ _ _
  have e3 := square_exchange (Γ := Γ) cB (lB U) (lB V) X Z P
  exact e1.eqTrans (congrMul (.eqRefl _) (e2.eqTrans e3.eqSymm))

end Expansion

end LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion
