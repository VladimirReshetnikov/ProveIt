import IPRADerivations.AnalyticNumberTheory.GcdFiber

/-!
# The divisor-sum identity `∑_{d ∣ n} φ(d) = n`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:sum-phi`.

* `sum_fiber` (reusable): for `σ` with values below `N`,
  `∑_{i<M} f(σ i) = ∑_{j<N} f(j) · #{i < M : σ i = j}`, from `Permutation.fiber` via
  `∏ 2^{f(σ i)}` and injectivity of `2^x`;
* with `σ(k) = n / gcd(k, n)` and `f = 1`: `n = ∑_{j ≤ n} #{k < n : n / gcd(k, n) = j}`, and the
  count at `j` is `[j ∣ n] φ(j)` (`count_point`): for `j ∣ n` it is the gcd fiber at `n / j`
  (`GcdFiber.gcd_fiber_at`), otherwise `n / gcd(k, n) = j` would make `j` a divisor of `n`.

The divisor sum is `∑_{d<n+1} [n mod d = 0] φ(d)`; the term `d = 0` vanishes since `φ(0) = 0`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SumPhi

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (pw_two_inj prod_pw_two)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq eqb_iff gB inst3_gB shift_pos gcd_fiber_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Two-parameter sums -/

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev p2F (e : PTm 3) : Fm PTm 3 :=
  ap3 (prod2F (pw two e)) (var 0) (var 1) (var 2) ≐ pw two (ap3 (sum2F e) (var 0) (var 1) (var 2))

private theorem prod2_pw_two₀ (e : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] p2F e := by
  ipra_ind [subst_ap2, subst_ap3]
  · exact (prod2_zero _ _ _).eqTrans ((pw_zero _).eqSymm.eqTrans (congrAp2 powF (sum2_zero _ _ _).eqSymm (.eqRefl _)))
  · refine (prod2_succ _ (var 0) _ _).eqTrans ?_
    have ee : inst3 (pw two e) (var 0 : PTm 3) (var 1) (var 2) = pw two (inst3 e (var 0) (var 1) (var 2)) := by
      simp [inst3]
    rw [ee]
    refine (congrMul Prf.hyp0 (.eqRefl _)).eqTrans ((pw_add _ _ _).eqSymm.eqTrans ?_)
    exact congrAp2 powF (sum2_succ _ _ _ _).eqSymm (.eqRefl _)

theorem prod2_pw_two (e : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (prod2F (pw two e)) N p q ≐ pw two (ap3 (sum2F e) N p q) := by
  have h := inst (Γ := Γ) (prod2_pw_two₀ e) (![N, p, q] : Fin 3 → PTm n)
  simpa using h

/-- Variables: `0 = N`, `1 = p`, `2 = x`. -/
private abbrev sumEqF (F : PTm 2) : Fm PTm 3 :=
  ap3 (sum2F (Syn.subst ![var 0, var 2] F)) (var 0) (var 1) (var 2) ≐ ap2 (sumF F) (var 0) (var 2)

private theorem sum2_eq_sum₀ (F : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] sumEqF F := by
  ipra_ind [subst_ap2, subst_ap3]
  · exact (sum2_zero _ _ _).eqTrans (sum_zero _ _).eqSymm
  · refine (sum2_succ _ _ _ _).eqTrans (.eqTrans ?_ (sum_succ' _ _ _).eqSymm)
    have e : inst3 (Syn.subst ![var 0, var 2] F) (var 0 : PTm 3) (var 1) (var 2) = Syn.subst ![var 0, var 2] F := by
      simp only [inst3, Syn.subst_subst]
      congr 1; funext k; fin_cases k <;> rfl
    rw [e]
    exact congrAdd Prf.hyp0 (.eqRefl _)

theorem sum2_eq_sum (F : PTm 2) (N p x : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F (Syn.subst ![var 0, var 2] F)) N p x ≐ ap2 (sumF F) N x := by
  have h := inst (Γ := Γ) (sum2_eq_sum₀ F) (![N, p, x] : Fin 3 → PTm n)
  simpa using h

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev zF : Fm PTm 3 := ap3 (sum2F zero) (var 0) (var 1) (var 2) ≐ zero

private theorem sum2_zero_body₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] zF := by
  ipra_ind [subst_ap3]
  · exact sum2_zero _ _ _
  · refine (sum2_succ _ _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    have e : inst3 (zero : PTm 3) (var 0 : PTm 3) (var 1) (var 2) = zero := by simp [inst3]
    rw [e]; exact .eqRefl _

/-- A two-parameter sum whose terms vanish below the bound is zero. -/
theorem sum2_zero_of_bounded (f : PTm 3) {N p q : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐ zero))) :
    Γ ⊢[PRAAx] ap3 (sum2F f) N p q ≐ zero := by
  refine (sum2_congr_bounded f zero p q p q N ?_).eqTrans ?_
  · have e : inst3 (zero : PTm 3) (var 0 : PTm (n + 1)) (Syn.shift p) (Syn.shift q) = zero := by simp [inst3]
    rw [e]; exact h
  · have h' := inst (Γ := Γ) sum2_zero_body₀ (![N, p, q] : Fin 3 → PTm n)
    simpa using h'

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev onesF : Fm PTm 2 := ap2 (sumF one) (var 0) (var 1) ≐ var 0

private theorem sum_ones₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] onesF :=
  sum_one_body (var 0) (var 1)

theorem sum_ones (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF one) N x ≐ N := by
  have h := inst (Γ := Γ) sum_ones₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

/-! ## Summing over fibers -/

/-- `f(j, x) · #{i < M : σ(i, x) = j}`, over `0 = j`, `1 = M`, `2 = x`. -/
def cB (f S : PTm 2) : PTm 3 :=
  Syn.subst ![var 0, var 2] f * ap3 (sum2F (Permutation.mB S)) (var 1) (var 0) (var 2)

theorem inst3_cB (f S : PTm 2) (j M x : PTm n) :
    inst3 (cB f S) j M x = inst2 f j x * ap3 (sum2F (Permutation.mB S)) M j x := by
  simp only [inst3, cB, inst2, PTm.subst_mul, subst_ap3, Syn.subst_subst, Syn.subst_var]
  congr 2; funext k; fin_cases k <;> rfl

/-- `∑_{i<M} f(σ i) = ∑_{j<N} f(j) · #{i < M : σ i = j}` when `σ < N`. -/
theorem sum_fiber {f S : PTm 2} {N x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S N x) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Permutation.FS f S)) M x ≐ ap3 (sum2F (cB f S)) N M x := by
  have p := Permutation.fiber (F := pw two f) hr M
  have e₁ : Permutation.FS (pw two f) S = pw two (Permutation.FS f S) := by simp [Permutation.FS]
  rw [e₁] at p
  have q : Γ ⊢[PRAAx] ap3 (prod2F (Permutation.fB (pw two f) S)) N M x ≐ ap3 (prod2F (pw two (cB f S))) N M x := by
    refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [Permutation.inst3_fB]
    have e₂ : inst3 (pw two (cB f S)) (var 0 : PTm (n + 1)) (Syn.shift M) (Syn.shift x) =
        pw two (inst3 (cB f S) (var 0) (Syn.shift M) (Syn.shift x)) := by simp [inst3]
    have e₃ : inst2 (pw two f) (var 0 : PTm (n + 1)) (Syn.shift x) = pw two (inst2 f (var 0) (Syn.shift x)) := by
      simp [inst2]
    rw [e₂, inst3_cB, e₃]
    exact pw_mul _ _ _
  exact pw_two_inj ((prod_pw_two _ _ _).eqSymm.eqTrans (p.eqTrans (q.eqTrans (prod2_pw_two _ _ _ _))))

/-! ## The map `k ↦ n / gcd(k, n)` -/

/-- `σ(k) = n / gcd(k, n)`, over `0 = k`, `1 = n`. -/
abbrev qB : PTm 2 := quo (var 1) (gcd (var 0) (var 1))

theorem inst2_q (k N : PTm n) : inst2 qB k N = quo N (gcd k N) := by
  simp only [inst2, subst_ap2, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    ConciseIPRA.PTm.subst_succ]

theorem shift_eq' {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ Syn.shift b :=
  LeanProofs.IPRA.Order.shift_eq h

theorem shift_mul' (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]

theorem shift_rem' (a b : PTm n) : Syn.shift (rem a b) = rem (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]

section Count

variable {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hN

/-- `N = gcd(k, N) · (N / gcd(k, N))`. -/
theorem N_eq (k : PTm n) : Γ ⊢[PRAAx] N ≐ gcd k N * quo N (gcd k N) :=
  eq_of_dvd' (gcd_pos_right hN) (Prf.andE₂ (gcd_dvd_at (gcd_pos_right hN)))

theorem q_le (k : PTm n) : Γ ⊢[PRAAx] le (quo N (gcd k N)) N := by
  refine le_of_eq_add (d := pred (gcd k N) * quo N (gcd k N)) ?_
  ipra_lc natEq (N_eq hN k) + Groth.ι (Q.mk _ (quo N (gcd k N))) * natEq (gcd_pos_right (a := k) hN)

omit hN in
theorem q_range (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) : Γ ⊢[PRAAx] Permutation.rangeAll qB (succ N) N := by
  refine .allI ?_
  rw [inst2_q]
  have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [e]
  exact (succ_monus_succ _ _).eqTrans (q_le (shift_pos hN) _)

/-- No `k` has `N / gcd(k, N) = 0`. -/
theorem q_ne_zero (k : PTm n) : Γ ⊢[PRAAx] neg (quo N (gcd k N) ≐ zero) := by
  refine .impI (succ_ne_zero' _ (hN.wk.eqSymm.eqTrans ((N_eq hN.wk k).eqTrans ?_)))
  exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)

/-- `N / gcd(k, N) = j ⟺ gcd(k, N) = e` when `N = e j`. -/
theorem q_iff {j e : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hNe : Γ ⊢[PRAAx] N ≐ e * j) (k : PTm n) :
    Γ ⊢[PRAAx] eqb (quo N (gcd k N)) j ≐ eqb (gcd k N) e := by
  refine eqb_iff (.impI ?_) (.impI ?_)
  · refine mul_cancel hj.wk ?_
    ipra_lc -Groth.ι (Q.mk _ (gcd k N)) * natEq (Prf.hyp0 : ((quo N (gcd k N) ≐ j) :: Γ) ⊢[PRAAx] quo N (gcd k N) ≐ j) -
      natEq (N_eq (hN.wk : ((quo N (gcd k N) ≐ j) :: Γ) ⊢[PRAAx] _) k) + natEq (hNe.wk (ψ := quo N (gcd k N) ≐ j))
  · refine (congrAp2 quoF (.eqRefl _) Prf.hyp0).eqTrans (quo_eq he.wk (q := j) (r := zero)
      (hNe.wk.eqTrans (add_zero _).eqSymm) (Order.zero_lt_of_eq_succ he.wk))

/-- `N / gcd(k, N) ≠ j` when `j ∤ N`. -/
theorem q_ne {j : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j))
    (hr : Γ ⊢[PRAAx] rem N j ≐ succ (pred (rem N j))) (k : PTm n) :
    Γ ⊢[PRAAx] neg (quo N (gcd k N) ≐ j) := by
  refine .impI (succ_ne_zero' _ (hr.wk.eqSymm.eqTrans ?_))
  exact dvd_of_eq' hj.wk (w := gcd k N)
    ((N_eq hN.wk k).eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_comm _ _)))

/-- The count at `j`: `#{k < N : N / gcd(k, N) = j} = [j ∣ N] φ(j)`. -/
theorem count_point (j : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F (Permutation.mB qB)) N j N ≐ eqb (rem N j) zero * phi j := by
  refine .orE (zero_or_succ j) ?_ ?_
  · -- `j = 0`: the count and `φ(0)` both vanish.
    have hz : ((j ≐ zero) :: Γ) ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have c : ((j ≐ zero) :: Γ) ⊢[PRAAx] ap3 (sum2F (Permutation.mB qB)) N j N ≐ zero := by
      refine sum2_zero_of_bounded _ (.allI (.impI ?_))
      rw [Permutation.inst3_mB, inst2_q]
      have hz' : (lt (var 0) (Syn.shift N) :: ((j ≐ zero) :: Γ).map Fm.shift) ⊢[PRAAx] Syn.shift j ≐ zero := by
        have e := hz.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_zero] at e
        exact e.wk
      exact (Euler.congrEqb (.eqRefl _) hz').eqTrans (eqb_of_ne (q_ne_zero (shift_pos hN.wk).wk _))
    have hp : ((j ≐ zero) :: Γ) ⊢[PRAAx] phi j ≐ zero :=
      (congrAp2 (sumF totBody) hz hz).eqTrans (sum_zero _ _)
    exact c.eqTrans ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) hp.eqSymm))
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    refine .orE (zero_or_succ (rem N j)) ?_ ?_
    · -- `j ∣ N`, `N = e j`: the fiber `gcd(k, N) = e`.
      have hr : ((rem N j ≐ zero) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] rem N j ≐ zero := Prf.hyp0
      have hj' : ((rem N j ≐ zero) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := hj.wk
      have hN' : ((rem N j ≐ zero) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := hN.wk.wk
      have factor := eq_of_dvd' hj' hr
      have hNe := factor.eqTrans (mul_comm _ _)
      have he := pos_of_eq_mul hN' factor
      have cnt : ((rem N j ≐ zero) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
          ap3 (sum2F (Permutation.mB qB)) N j N ≐ ap3 (sum2F gB) N N (quo N j) := by
        refine sum2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
        rw [Permutation.inst3_mB, inst2_q, inst3_gB]
        have hs := shift_eq' hNe
        rw [shift_mul'] at hs
        exact q_iff (shift_pos hN').wk (shift_pos hj').wk (shift_pos he).wk hs.wk _
      have gf := gcd_fiber_at he hj'
      exact cnt.eqTrans ((congrAp3 (sum2F gB) hNe hNe (.eqRefl _)).eqTrans (gf.eqTrans
        ((one_mul _).eqSymm.eqTrans (congrMul (eqb_of_eq hr).eqSymm (.eqRefl _)))))
    · -- `j ∤ N`: no `k` qualifies.
      have hr : ((rem N j ≐ succ (pred (rem N j))) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
          rem N j ≐ succ (pred (rem N j)) := Prf.hyp0
      have hj' : ((rem N j ≐ succ (pred (rem N j))) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := hj.wk
      have hN' : ((rem N j ≐ succ (pred (rem N j))) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) :=
        hN.wk.wk
      have c : ((rem N j ≐ succ (pred (rem N j))) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
          ap3 (sum2F (Permutation.mB qB)) N j N ≐ zero := by
        refine sum2_zero_of_bounded _ (.allI (.impI ?_))
        rw [Permutation.inst3_mB, inst2_q]
        have hs := shift_pos hr
        rw [shift_rem'] at hs
        exact eqb_of_ne (q_ne (shift_pos hN').wk (shift_pos hj').wk hs.wk _)
      have e₀ : ((rem N j ≐ succ (pred (rem N j))) :: (j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] eqb (rem N j) zero ≐ zero :=
        eqb_of_ne (.impI (succ_ne_zero' _ (hr.wk.eqSymm.eqTrans Prf.hyp0)))
      exact c.eqTrans ((zero_mul _).eqSymm.eqTrans (congrMul e₀.eqSymm (.eqRefl _)))

end Count

/-! ## The theorem -/

/-- `[n mod d = 0] φ(d)`, over `0 = d`, `1 = n`. -/
abbrev dpB : PTm 2 := eqb (rem (var 1) (var 0)) zero * ap2 (sumF totBody) (var 0) (var 0)

theorem inst2_dp (d N : PTm n) : inst2 dpB d N = eqb (rem N d) zero * phi d := by
  simp only [inst2, PTm.subst_mul, subst_eqb, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    ConciseIPRA.PTm.subst_zero]

/-- `thm:sum-phi` at an arbitrary `N ≥ 1`: `∑_{d ≤ N, d ∣ N} φ(d) = N`. -/
theorem sum_phi_at {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF dpB) (succ N) N ≐ N := by
  have h₁ := sum_ones (Γ := Γ) N N
  have eFS : Permutation.FS (one : PTm 2) qB = one := by simp [Permutation.FS]
  have hf := sum_fiber (f := one) (q_range hN) N
  rw [eFS] at hf
  have hpt : Γ ⊢[PRAAx] ap3 (sum2F (cB one qB)) (succ N) N N ≐
      ap3 (sum2F (Syn.subst ![var 0, var 2] dpB)) (succ N) N N := by
    refine sum2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst3_cB]
    have e : inst3 (Syn.subst ![var 0, var 2] dpB) (var 0 : PTm (n + 1)) (Syn.shift N) (Syn.shift N) =
        inst2 dpB (var 0) (Syn.shift N) := by
      simp only [inst3, inst2, Syn.subst_subst]
      congr 1; funext k; fin_cases k <;> rfl
    have e₁ : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift N) = one := by simp [inst2]
    rw [e, inst2_dp, e₁]
    exact (one_mul _).eqTrans (count_point (shift_pos hN).wk _)
  exact (sum2_eq_sum dpB _ _ _).eqSymm.eqTrans (hpt.eqSymm.eqTrans (hf.eqSymm.eqTrans h₁))

/-- `thm:sum-phi`: `∑_{d<n+1} [n mod d = 0] φ(d) = n` for `n ≥ 1`; variable `0 = n − 1`. -/
abbrev sumPhiFormula : Fm PTm 1 :=
  ap2 (sumF dpB) (succ (succ (var 0))) (succ (var 0)) ≐ succ (var 0)

theorem sum_phi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 sumPhiFormula :=
  closeUniv 1 (sum_phi_at (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.AnalyticNumberTheory.SumPhi

export_ipra AnalyticNumberTheory.SumPhi (shift_rem')
