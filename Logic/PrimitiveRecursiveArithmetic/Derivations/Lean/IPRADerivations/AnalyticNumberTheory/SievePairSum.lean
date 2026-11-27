import IPRADerivations.AnalyticNumberTheory.SievePairBound
import IPRADerivations.Probability.SymmetrizedMoments

/-!
# Summing the pair count bounds over all pairs of weight indices

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
after the square is expanded, `eq:crt-count` is applied to every pair `(d, e)` and the two resulting estimates are
summed, giving the main term `(x/q) Σ λ_d λ_e / [d, e]` and the error `Σ |λ_d| |λ_e|`.

For natural weight bodies `U(d, P)`, `V(e, P)` and the parameter `y = ⟨X, P⟩`, `P = ⟨q, ⟨a, w⟩⟩`, with
`K(d, e) = SieveCount.cnt X q (lc d e) a` and the indicator `ind` of `SievePairBound`:

* `Am`, `Bm`, `Cm`, `Dm`: the three-variable bodies
  `ind · U V · (q d e K)`, `ind · U V · (gcd(d, e) X + q d e)`, `ind · U V · (gcd(d, e) X)`,
  `ind · U V · (q d e K + q d e)`;
* `upper`: `Σ_{d<Z} Σ_{e<Z} Am ≤ Σ_{d<Z} Σ_{e<Z} Bm`, and `lower`: `Σ Σ Cm ≤ Σ Σ Dm`
  (`SymmetrizedMoments.dsum_le` with `SievePairBound.pw_upper`, `pw_lower`);
* `Am_at`, `Bm_at`, `Cm_at`, `Dm_at`: the summands at an explicit parameter;
* `subst_ind`, `subst_cnt`, `subst_lc`, `congrInd`, `congrCnt`: substitution and congruence for the compound terms.

Here `U_d` stands for `λ_d / d`, so that `d e U_d U_e = λ_d λ_e` and `gcd(d, e) U_d U_e = λ_d λ_e / [d, e]`. The
identification of these double sums with the expanded square (`SieveSquare.square_exchange`) and with the quadratic
form of `SieveDiagonal` is not part of this module.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SieveCount (cnt)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount (lc)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairBound (pw_upper pw_lower)
open LeanProofs.IPRA.Probability.Independence (dsum)
open LeanProofs.IPRA.Probability.SymmetrizedMoments (dsum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Substitution and congruence for the compound terms -/

theorem subst_gcd' {m : ℕ} (σ : Fin n → PTm m) (u v : PTm n) :
    Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
  simp only [gcd, subst_ex2, ConciseIPRA.PTm.subst_succ]

theorem subst_lc {m : ℕ} (σ : Fin n → PTm m) (d e : PTm n) :
    Syn.subst σ (lc d e) = lc (Syn.subst σ d) (Syn.subst σ e) := by
  simp only [lc, LeanProofs.IPRA.PTm.subst_mul, subst_ap2, subst_gcd']

theorem subst_cnt {m : ℕ} (σ : Fin n → PTm m) (X q l a : PTm n) :
    Syn.subst σ (cnt X q l a) = cnt (Syn.subst σ X) (Syn.subst σ q) (Syn.subst σ l) (Syn.subst σ a) := by
  simp only [cnt, BrunCounting.A, SieveCount.par, subst_ap2, subst_pairT, LeanProofs.IPRA.PTm.subst_mul,
    LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ]

theorem subst_ind {m : ℕ} (σ : Fin n → PTm m) (d e q a : PTm n) :
    Syn.subst σ (SievePairBound.ind d e q a) = SievePairBound.ind (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ q) (Syn.subst σ a) := by
  simp only [SievePairBound.ind, LeanProofs.IPRA.PTm.subst_mul, subst_eqb, LeanProofs.IPRA.PTm.subst_monus, subst_gcd',
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem congrInd {d e q q' a a' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q') (ha : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] SievePairBound.ind d e q a ≐ SievePairBound.ind d e q' a' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (SievePairBound.ind (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![d, e, q, a])
    (σ' := ![d, e, q', a']) (fun j => by fin_cases j <;> first | assumption | exact .eqRefl _)
  simp only [subst_ind, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  exact h

theorem congrCnt {X X' q q' l a a' : PTm n} (hX : Γ ⊢[PRAAx] X ≐ X') (hq : Γ ⊢[PRAAx] q ≐ q')
    (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] cnt X q l a ≐ cnt X' q' l a' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (cnt (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![X, q, l, a])
    (σ' := ![X', q', l, a']) (fun j => by fin_cases j <;> first | assumption | exact .eqRefl _)
  simp only [subst_cnt, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  exact h

/-! ## The bodies -/

section Bodies

variable (U V : PTm 2)

/-- `U(d, snd y) V(e, snd y)` over `(d, e, y)`. -/
def wB : PTm 3 := Syn.subst ![var 0, sndT (var 2)] U * Syn.subst ![var 1, sndT (var 2)] V

theorem inst3_wB (i j x : PTm n) : inst3 (wB U V) i j x = inst2 U i (sndT x) * inst2 V j (sndT x) := by
  have h1 : Syn.subst ![i, j, x] (Syn.subst ![var 0, sndT (var 2)] U) = inst2 U i (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have h2 : Syn.subst ![i, j, x] (Syn.subst ![var 1, sndT (var 2)] V) = inst2 V j (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, wB, LeanProofs.IPRA.PTm.subst_mul, h1, h2]

/-- `ind · U V · (q d e K)` over `(d, e, ⟨X, ⟨q, ⟨a, w⟩⟩⟩)`. -/
def Am : PTm 3 :=
  SievePairBound.ind (var 0) (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2)))) *
    (wB U V * (fstT (sndT (var 2)) * (var 0 * var 1) *
      cnt (fstT (var 2)) (fstT (sndT (var 2))) (lc (var 0) (var 1)) (fstT (sndT (sndT (var 2))))))

/-- `ind · U V · (gcd(d, e) X + q d e)`. -/
def Bm : PTm 3 :=
  SievePairBound.ind (var 0) (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2)))) *
    (wB U V * (gcd (var 0) (var 1) * fstT (var 2) + fstT (sndT (var 2)) * (var 0 * var 1)))

/-- `ind · U V · (gcd(d, e) X)`. -/
def Cm : PTm 3 :=
  SievePairBound.ind (var 0) (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2)))) *
    (wB U V * (gcd (var 0) (var 1) * fstT (var 2)))

/-- `ind · U V · (q d e K + q d e)`. -/
def Dm : PTm 3 :=
  SievePairBound.ind (var 0) (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2)))) *
    (wB U V * (fstT (sndT (var 2)) * (var 0 * var 1) *
      cnt (fstT (var 2)) (fstT (sndT (var 2))) (lc (var 0) (var 1)) (fstT (sndT (sndT (var 2)))) +
        fstT (sndT (var 2)) * (var 0 * var 1)))

theorem inst3_Am (i j x : PTm n) : inst3 (Am U V) i j x =
    SievePairBound.ind i j (fstT (sndT x)) (fstT (sndT (sndT x))) *
      (inst3 (wB U V) i j x * (fstT (sndT x) * (i * j) *
        cnt (fstT x) (fstT (sndT x)) (lc i j) (fstT (sndT (sndT x))))) := by
  simp only [inst3, Am, SievePairBound.ind, lc, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add,
    subst_eqb, LeanProofs.IPRA.PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_gcd', subst_cnt, subst_ap2,
    subst_pairT, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem inst3_Bm (i j x : PTm n) : inst3 (Bm U V) i j x =
    SievePairBound.ind i j (fstT (sndT x)) (fstT (sndT (sndT x))) *
      (inst3 (wB U V) i j x * (gcd i j * fstT x + fstT (sndT x) * (i * j))) := by
  simp only [inst3, Bm, SievePairBound.ind, lc, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add,
    subst_eqb, LeanProofs.IPRA.PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_gcd', subst_cnt, subst_ap2,
    subst_pairT, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem inst3_Cm (i j x : PTm n) : inst3 (Cm U V) i j x =
    SievePairBound.ind i j (fstT (sndT x)) (fstT (sndT (sndT x))) * (inst3 (wB U V) i j x * (gcd i j * fstT x)) := by
  simp only [inst3, Cm, SievePairBound.ind, lc, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add,
    subst_eqb, LeanProofs.IPRA.PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_gcd', subst_cnt, subst_ap2,
    subst_pairT, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem inst3_Dm (i j x : PTm n) : inst3 (Dm U V) i j x =
    SievePairBound.ind i j (fstT (sndT x)) (fstT (sndT (sndT x))) *
      (inst3 (wB U V) i j x * (fstT (sndT x) * (i * j) *
        cnt (fstT x) (fstT (sndT x)) (lc i j) (fstT (sndT (sndT x))) + fstT (sndT x) * (i * j))) := by
  simp only [inst3, Dm, SievePairBound.ind, lc, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_add,
    subst_eqb, LeanProofs.IPRA.PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_gcd', subst_cnt, subst_ap2,
    subst_pairT, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

/-! ## The summed bounds -/

/-- `Σ_{d<Z} Σ_{e<Z} ind · U V · (q d e K) ≤ Σ_{d<Z} Σ_{e<Z} ind · U V · (gcd(d, e) X + q d e)`. -/
theorem upper (Z y : PTm n) : Γ ⊢[PRAAx] le (dsum (Am U V) Z Z y) (dsum (Bm U V) Z Z y) :=
  dsum_le (Am U V) (Bm U V) (fun i j x => by rw [inst3_Am, inst3_Bm]; exact pw_upper _ _ _ _ _ _) Z Z y

/-- `Σ_{d<Z} Σ_{e<Z} ind · U V · (gcd(d, e) X) ≤ Σ_{d<Z} Σ_{e<Z} ind · U V · (q d e K + q d e)`. -/
theorem lower (Z y : PTm n) : Γ ⊢[PRAAx] le (dsum (Cm U V) Z Z y) (dsum (Dm U V) Z Z y) :=
  dsum_le (Cm U V) (Dm U V) (fun i j x => by rw [inst3_Cm, inst3_Dm]; exact pw_lower _ _ _ _ _ _) Z Z y

/-! ## The summands at an explicit parameter -/

/-- The projections of `y = ⟨X, ⟨q, ⟨a, w⟩⟩⟩`. -/
theorem proj (X q a w : PTm n) :
    Γ ⊢[PRAAx] (fstT (pairT X (pairT q (pairT a w))) ≐ X) ⋏
      ((sndT (pairT X (pairT q (pairT a w))) ≐ pairT q (pairT a w)) ⋏
        ((fstT (sndT (pairT X (pairT q (pairT a w)))) ≐ q) ⋏
          (fstT (sndT (sndT (pairT X (pairT q (pairT a w))))) ≐ a))) := by
  have s1 := snd_pair (Γ := Γ) X (pairT q (pairT a w))
  have hq : Γ ⊢[PRAAx] fstT (sndT (pairT X (pairT q (pairT a w)))) ≐ q :=
    (congrFst s1).eqTrans (fst_pair q (pairT a w))
  have ha : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT X (pairT q (pairT a w))))) ≐ a :=
    (congrFst ((congrSnd s1).eqTrans (snd_pair q (pairT a w)))).eqTrans (fst_pair a w)
  exact .andI (fst_pair _ _) (.andI s1 (.andI hq ha))

theorem Am_at (i j X q a w : PTm n) :
    Γ ⊢[PRAAx] inst3 (Am U V) i j (pairT X (pairT q (pairT a w))) ≐
      SievePairBound.ind i j q a * ((inst2 U i (pairT q (pairT a w)) * inst2 V j (pairT q (pairT a w))) *
        (q * (i * j) * cnt X q (lc i j) a)) := by
  have p := proj (Γ := Γ) X q a w
  have hX := Prf.andE₁ p
  have hP := Prf.andE₁ (Prf.andE₂ p)
  have hq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))
  have ha := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))
  rw [inst3_Am, inst3_wB]
  exact congrMul (congrInd hq ha) (congrMul (congrMul (congrInst2 U (.eqRefl _) hP) (congrInst2 V (.eqRefl _) hP))
    (congrMul (congrMul hq (.eqRefl _)) (congrCnt hX hq ha)))

theorem Bm_at (i j X q a w : PTm n) :
    Γ ⊢[PRAAx] inst3 (Bm U V) i j (pairT X (pairT q (pairT a w))) ≐
      SievePairBound.ind i j q a * ((inst2 U i (pairT q (pairT a w)) * inst2 V j (pairT q (pairT a w))) *
        (gcd i j * X + q * (i * j))) := by
  have p := proj (Γ := Γ) X q a w
  have hX := Prf.andE₁ p
  have hP := Prf.andE₁ (Prf.andE₂ p)
  have hq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))
  have ha := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))
  rw [inst3_Bm, inst3_wB]
  exact congrMul (congrInd hq ha) (congrMul (congrMul (congrInst2 U (.eqRefl _) hP) (congrInst2 V (.eqRefl _) hP))
    (congrAdd (congrMul (.eqRefl _) hX) (congrMul hq (.eqRefl _))))

theorem Cm_at (i j X q a w : PTm n) :
    Γ ⊢[PRAAx] inst3 (Cm U V) i j (pairT X (pairT q (pairT a w))) ≐
      SievePairBound.ind i j q a * ((inst2 U i (pairT q (pairT a w)) * inst2 V j (pairT q (pairT a w))) * (gcd i j * X)) := by
  have p := proj (Γ := Γ) X q a w
  have hX := Prf.andE₁ p
  have hP := Prf.andE₁ (Prf.andE₂ p)
  have hq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))
  have ha := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))
  rw [inst3_Cm, inst3_wB]
  exact congrMul (congrInd hq ha) (congrMul (congrMul (congrInst2 U (.eqRefl _) hP) (congrInst2 V (.eqRefl _) hP))
    (congrMul (.eqRefl _) hX))

theorem Dm_at (i j X q a w : PTm n) :
    Γ ⊢[PRAAx] inst3 (Dm U V) i j (pairT X (pairT q (pairT a w))) ≐
      SievePairBound.ind i j q a * ((inst2 U i (pairT q (pairT a w)) * inst2 V j (pairT q (pairT a w))) *
        (q * (i * j) * cnt X q (lc i j) a + q * (i * j))) := by
  have p := proj (Γ := Γ) X q a w
  have hX := Prf.andE₁ p
  have hP := Prf.andE₁ (Prf.andE₂ p)
  have hq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))
  have ha := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))
  rw [inst3_Dm, inst3_wB]
  exact congrMul (congrInd hq ha) (congrMul (congrMul (congrInst2 U (.eqRefl _) hP) (congrInst2 V (.eqRefl _) hP))
    (congrAdd (congrMul (congrMul hq (.eqRefl _)) (congrCnt hX hq ha)) (congrMul hq (.eqRefl _))))

end Bodies

end LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum

export_ipra AnalyticNumberTheory.SievePairSum (subst_gcd')
