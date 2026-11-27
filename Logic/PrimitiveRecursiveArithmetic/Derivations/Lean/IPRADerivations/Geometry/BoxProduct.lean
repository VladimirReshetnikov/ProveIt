import IPRADerivations.Foundations.FiniteAMGM
import IPRADerivations.Combinatorics.CoefficientLogConcave
import IPRADerivations.Probability.Variance

/-!
# The box inequality of the rational Brunn–Minkowski theorem

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15`, `report/euclidean.tex`:
`lem:box-product` ("If `t_1, …, t_n, q` are nonnegative rationals and `∏_i t_i ≥ q^n`, then
`∏_{i=1}^n (1 + t_i) ≥ (1 + q)^n`") and `eq:box-base` ("If `X, Y` are single boxes with side
lengths `a_i, b_i > 0` ... Whenever `q^n V(X) ≤ V(Y)`, the lemma gives
`V(X + Y) ≥ V(X)(1 + q)^n`. This is the only numerical inequality needed for the general finite
case.").

Cleared of denominators, with `q = Q/E` and `m = N + 1` coordinates:

* `box_base` (`eq:box-base`): if `a_i + b_i ≥ 1` for all `i` and `Q^m ∏ a_i ≤ E^m ∏ b_i`, then
  `∏ a_i · (E + Q)^m ≤ E^m · ∏ (a_i + b_i)`;
* `box_product` (`lem:box-product`): for `D ≥ 1`, `Q^m ≤ ∏ t_i` gives
  `(D + Q)^m ≤ ∏ (D + t_i)` (the lemma for the rationals `t_i/D`, `Q/D`).

The packet proves the lemma through the elementary symmetric sums `e_j`. Here it is the finite
AM–GM inequality (`Foundations/FiniteAMGM`) applied to the two families `a_i L_i` and `b_i L_i`,
where `L_i = ∏_{j ≠ i} (a_j + b_j)` is the leave-one-out product:

* `prod_mul`: `∏ f g = ∏ f · ∏ g`;
* `lB`, `LO`, `lo_mul`: the leave-one-out product, with `L_i (a_i + b_i) = P = ∏ (a_j + b_j)`;
* `prod_A`, `prod_B`, `sum_AB`: `∏ (a_i L_i) · P = ∏ a_i · P^m`, the same for `b`, and
  `Σ a_i L_i + Σ b_i L_i = m P`;
* `box_alg`: with `x = Σ a_i L_i`, `y = Σ b_i L_i`: from `m^m ∏ a · P^m ≤ x^m P`,
  `m^m ∏ b · P^m ≤ y^m P` and `x + y = m P`, by the decidable comparison of `x Q` with `E y` (no
  roots): in the first case `x (E + Q) ≤ E m P`, in the second `y (E + Q) ≤ Q m P`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.BoxProduct

open_ipra
open LeanProofs.IPRA.Combinatorics.CoefficientLogConcave (sub2 inst2_sub2 inst2_mul inst2_monus
  inst2_ap2)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (shift_pair shift_succ)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (pair_congr le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteAMGM (finite_amgm prod_succ'')
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The product of a product -/

/-- The product equality with the upper limit in variable `0`. -/
abbrev pmF (f g : PTm 2) (x : PTm n) : Fm PTm (n + 1) :=
  ap2 (prodF (f * g)) (var 0) (Syn.shift x) ≐
    ap2 (prodF f) (var 0) (Syn.shift x) * ap2 (prodF g) (var 0) (Syn.shift x)

theorem prod_mul_step (f g : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (prodF (f * g)) N x ≐ ap2 (prodF f) N x * ap2 (prodF g) N x) :
    Γ ⊢[PRAAx] ap2 (prodF (f * g)) (succ N) x ≐
      ap2 (prodF f) (succ N) x * ap2 (prodF g) (succ N) x := by
  have pointwise := prod_succ'' (Γ := Γ) (f * g) N x
  rw [inst2_mul] at pointwise
  refine (pointwise.eqTrans (congrMul ih (.eqRefl _))).eqTrans ?_
  refine .eqTrans ?_ (congrMul (prod_succ'' f N x).eqSymm (prod_succ'' g N x).eqSymm)
  ipra_ring

/-- `∏_{i<N} f g = ∏_{i<N} f · ∏_{i<N} g`. -/
theorem prod_mul (f g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (f * g)) N x ≐ ap2 (prodF f) N x * ap2 (prodF g) N x :=
  prod_mul_body f g N x

/-! ## The leave-one-out product -/

section LeaveOneOut

variable (c : PTm 2)

/-- `c_j^{[j ≠ i]}`, over `0 = j`, `1 = ⟨i, x⟩`. -/
def lB : PTm 2 :=
  ap2 powF (monus one (eqb (fstT (var 1)) (var 0))) (sub2 c (var 0) (sndT (var 1)))

theorem l_at (j i x : PTm n) :
    Γ ⊢[PRAAx] inst2 (lB c) j (pairT i x) ≐ pw (inst2 c j x) (monus one (eqb i j)) := by
  have e : inst2 (eqb (fstT (var 1)) (var 0) : PTm 2) j (pairT i x) =
      eqb (fstT (pairT i x)) j := by simp [inst2]
  have o : inst2 (one : PTm 2) j (pairT i x) = one := by simp [inst2]
  have s : inst2 (sndT (var 1) : PTm 2) j (pairT i x) = sndT (pairT i x) := by simp [inst2]
  have v : inst2 (var 0 : PTm 2) j (pairT i x) = j := by simp [inst2]
  have h : inst2 (lB c) j (pairT i x) =
      pw (inst2 c j (sndT (pairT i x))) (monus one (eqb (fstT (pairT i x)) j)) := by
    rw [lB, inst2_ap2, inst2_monus, inst2_sub2, e, o, s, v]
  rw [h]
  exact congrPw (congrInst2 c (.eqRefl _) (snd_pair _ _))
    (congrMonus (.eqRefl _) (congrEqb (fst_pair _ _) (.eqRefl _)))

/-- The leave-one-out product `∏_{j<N, j≠i} c_j`. -/
abbrev LO (N i x : PTm n) : PTm n := ap2 (prodF (lB c)) N (pairT i x)

/-- A factor different from the omitted one. -/
theorem l_keep {j i x : PTm n} (h : Γ ⊢[PRAAx] eqb i j ≐ zero) :
    Γ ⊢[PRAAx] inst2 (lB c) j (pairT i x) ≐ inst2 c j x :=
  (l_at c j i x).eqTrans ((congrPw (.eqRefl _)
    ((congrMonus (.eqRefl _) h).eqTrans (monus_zero one))).eqTrans (pw_one _))

/-- The omitted factor. -/
theorem l_drop {j i x : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] inst2 (lB c) j (pairT i x) ≐ one :=
  (l_at c j i x).eqTrans ((congrPw (.eqRefl _)
    ((congrMonus (.eqRefl _) (eqb_of_eq h)).eqTrans (monus_self one))).eqTrans (pw_zero _))

/-- The step of `lo_all`, in any context. -/
theorem lo_step {N i x : PTm n}
    (ihA : Γ ⊢[PRAAx] le N i ⟶ (LO c N i x ≐ ap2 (prodF c) N x))
    (ihB : Γ ⊢[PRAAx] lt i N ⟶ (LO c N i x * inst2 c i x ≐ ap2 (prodF c) N x)) :
    Γ ⊢[PRAAx] (le (succ N) i ⟶ (LO c (succ N) i x ≐ ap2 (prodF c) (succ N) x)) ⋏
      (lt i (succ N) ⟶ (LO c (succ N) i x * inst2 c i x ≐ ap2 (prodF c) (succ N) x)) := by
  refine .andI (.impI ?_) (.impI ?_)
  · have hlt : (le (succ N) i :: Γ) ⊢[PRAAx] lt N i := Prf.hyp0
    have e₁ := natEq ((prod_succ'' (lB c) N (pairT i x)).eqTrans
      (congrMul (.eqRefl _) (l_keep c (eqb_zero_of_gt hlt))))
    have e₃ := natEq (prod_succ'' (Γ := le (succ N) i :: Γ) c N x)
    apply deriveNat; ipra_simps
    rw [e₁, e₃, natEq (Prf.impE ihA.wk (le_trans (le_succ_self N) hlt))]
  · have hle : (lt i (succ N) :: Γ) ⊢[PRAAx] le i N := le_of_lt_succ Prf.hyp0
    refine .orE (lt_or_eq_of_le hle) ?_ ?_
    · have e₁ := natEq ((prod_succ'' (lB c) N (pairT i x)).eqTrans
        (congrMul (.eqRefl _) (l_keep c (eqb_zero_of_lt (Prf.hyp0 (Γ := lt i (succ N) :: Γ)
          (φ := lt i N))))))
      have e₂ := natEq (Prf.impE ihB.wk.wk (Prf.hyp0 (Γ := lt i (succ N) :: Γ) (φ := lt i N)))
      have e₃ := natEq (prod_succ'' (Γ := lt i N :: lt i (succ N) :: Γ) c N x)
      apply deriveNat; ipra_simps
      rw [e₁, e₃]
      linear_combination 𝔞 (inst2 c N x) * e₂
    · have hi : ((i ≐ N) :: lt i (succ N) :: Γ) ⊢[PRAAx] i ≐ N := Prf.hyp0
      have e₁ := natEq ((prod_succ'' (lB c) N (pairT i x)).eqTrans
        (congrMul (.eqRefl _) (l_drop c hi)))
      have e₂ := natEq (Prf.impE ihA.wk.wk (le_congr (.eqRefl _) hi.eqSymm (le_refl N)))
      have e₃ := natEq (prod_succ'' (Γ := (i ≐ N) :: lt i (succ N) :: Γ) c N x)
      apply deriveNat; ipra_simps
      rw [e₁, e₃, natEq (congrInst2 c hi (.eqRefl x)), e₂]; ring

/-- The induction formula of `lo_all`; variable `0` is the upper limit. -/
abbrev loF (i x : PTm n) : Fm PTm (n + 1) :=
  (le (var 0) (Syn.shift i) ⟶
      (LO c (var 0) (Syn.shift i) (Syn.shift x) ≐ ap2 (prodF c) (var 0) (Syn.shift x))) ⋏
    (lt (Syn.shift i) (var 0) ⟶
      (LO c (var 0) (Syn.shift i) (Syn.shift x) * inst2 c (Syn.shift i) (Syn.shift x) ≐
        ap2 (prodF c) (var 0) (Syn.shift x)))

theorem lo_all (N i x : PTm n) :
    Γ ⊢[PRAAx] (le N i ⟶ (LO c N i x ≐ ap2 (prodF c) N x)) ⋏
      (lt i N ⟶ (LO c N i x * inst2 c i x ≐ ap2 (prodF c) N x)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (loF c i x) := by
    refine PRA.qfInd _ ⟨⟨le_QF _ _, trivial⟩, ⟨lt_QF _ _, trivial⟩⟩ ?_ ?_
    · have b : Γ ⊢[PRAAx] (le zero i ⟶ (LO c zero i x ≐ ap2 (prodF c) zero x)) ⋏
          (lt i zero ⟶ (LO c zero i x * inst2 c i x ≐ ap2 (prodF c) zero x)) :=
        .andI (.impI ((prod_zero _ _).eqTrans (prod_zero _ _).eqSymm))
          (.impI (lt_zero_absurd _ Prf.hyp0))
      simpa [subst_inst2] using b
    · have st : (loF c i x :: Γ.map Fm.shift) ⊢[PRAAx]
          (le (succ (var 0)) (Syn.shift i) ⟶
              (LO c (succ (var 0)) (Syn.shift i) (Syn.shift x) ≐
                ap2 (prodF c) (succ (var 0)) (Syn.shift x))) ⋏
            (lt (Syn.shift i) (succ (var 0)) ⟶
              (LO c (succ (var 0)) (Syn.shift i) (Syn.shift x) *
                  inst2 c (Syn.shift i) (Syn.shift x) ≐
                ap2 (prodF c) (succ (var 0)) (Syn.shift x))) :=
        lo_step c (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero, subst_inst2] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero, subst_inst2] using h2

/-- `L_i c_i = ∏_{j<N} c_j` for `i < N`. -/
theorem lo_mul {N i x : PTm n} (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] LO c N i x * inst2 c i x ≐ ap2 (prodF c) N x :=
  .impE (Prf.andE₂ (lo_all c N i x)) h

end LeaveOneOut

/-! ## The two families -/

section Families

variable (c g : PTm 2)

/-- `g_i · L_i`, over `0 = i`, `1 = ⟨m, x⟩`. -/
def fam : PTm 2 :=
  sub2 g (var 0) (sndT (var 1)) *
    ap2 (prodF (lB c)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `g_i` with the parameter `⟨m, x⟩`. -/
def gP : PTm 2 := sub2 g (var 0) (sndT (var 1))

/-- The constant `∏_{j<m} c_j` with the parameter `⟨m, x⟩`. -/
def PB : PTm 2 := ap2 (prodF c) (fstT (var 1)) (sndT (var 1))

theorem fam_at (i m x : PTm n) :
    Γ ⊢[PRAAx] inst2 (fam c g) i (pairT m x) ≐ inst2 g i x * LO c m i x := by
  have h : inst2 (fam c g) i (pairT m x) = inst2 g i (sndT (pairT m x)) *
      ap2 (prodF (lB c)) (fstT (pairT m x)) (pairT i (sndT (pairT m x))) := by
    simp only [fam, inst2_mul, inst2_sub2, inst2_ap2]; simp [inst2]
  rw [h]
  exact congrMul (congrInst2 g (.eqRefl _) (snd_pair _ _))
    (congrAp2 _ (fst_pair _ _) (pair_congr (.eqRefl _) (snd_pair _ _)))

theorem gP_at (i m x : PTm n) : Γ ⊢[PRAAx] inst2 (gP g) i (pairT m x) ≐ inst2 g i x := by
  have h : inst2 (gP g) i (pairT m x) = inst2 g i (sndT (pairT m x)) := by
    simp only [gP, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrInst2 g (.eqRefl _) (snd_pair _ _)

theorem PB_at (i m x : PTm n) :
    Γ ⊢[PRAAx] inst2 (PB c) i (pairT m x) ≐ ap2 (prodF c) m x := by
  have h : inst2 (PB c) i (pairT m x) =
      ap2 (prodF c) (fstT (pairT m x)) (sndT (pairT m x)) := by
    simp only [PB, inst2_ap2]; simp [inst2]
  rw [h]
  exact congrAp2 _ (fst_pair _ _) (snd_pair _ _)

theorem shift_prod (f : PTm 2) (m x : PTm n) :
    Syn.shift (ap2 (prodF f) m x) = ap2 (prodF f) (Syn.shift m) (Syn.shift x) := by
  simp [Syn.shift]

/-- `∏_{i<m} (g_i L_i) · P = ∏_{i<m} g_i · P^m`. -/
theorem prod_fam (m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (fam c g)) m (pairT m x) * ap2 (prodF c) m x ≐
      ap2 (prodF g) m x * pw (ap2 (prodF c) m x) m := by
  have E₁ := natEq (prod_mul (Γ := Γ) (fam c g) (gP c) m (pairT m x))
  have E₂ : Γ ⊢[PRAAx] ap2 (prodF (gP c)) m (pairT m x) ≐ ap2 (prodF c) m x := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    exact gP_at c _ _ _
  have E₃ : Γ ⊢[PRAAx] ap2 (prodF (fam c g * gP c)) m (pairT m x) ≐
      ap2 (prodF (gP g * PB c)) m (pairT m x) := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    rw [inst2_mul, inst2_mul]
    have a₁ := natEq (fam_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) c g (var 0)
      (Syn.shift m) (Syn.shift x))
    have a₂ := natEq (gP_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) c (var 0)
      (Syn.shift m) (Syn.shift x))
    have a₃ := natEq (gP_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) g (var 0)
      (Syn.shift m) (Syn.shift x))
    have a₄ := natEq (PB_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) c (var 0)
      (Syn.shift m) (Syn.shift x))
    have a₅ := natEq (lo_mul c (Prf.hyp0 (Γ := Γ.map Fm.shift)
      (φ := lt (var 0) (Syn.shift m))) (x := Syn.shift x))
    apply deriveNat; ipra_simps
    rw [a₁, a₂, a₃, a₄]
    linear_combination 𝔞 (inst2 g (var 0) (Syn.shift x)) * a₅
  have E₄ := natEq (prod_mul (Γ := Γ) (gP g) (PB c) m (pairT m x))
  have E₅ : Γ ⊢[PRAAx] ap2 (prodF (gP g)) m (pairT m x) ≐ ap2 (prodF g) m x := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    exact gP_at g _ _ _
  have E₆ : Γ ⊢[PRAAx] ap2 (prodF (PB c)) m (pairT m x) ≐ pw (ap2 (prodF c) m x) m := by
    refine prod_const_of _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_prod]
    exact PB_at c _ _ _
  have e₂ := natEq E₂
  have e₃ := natEq E₃
  have e₅ := natEq E₅
  apply deriveNat; ipra_simps
  rw [← e₂, ← E₁, e₃, E₄, e₅, natEq E₆]

end Families

section Sum

variable (a b : PTm 2)

/-- `Σ_{i<m} a_i L_i + Σ_{i<m} b_i L_i = m P` for `c = a + b`. -/
theorem sum_fam (m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (fam (addBody a b) a)) m (pairT m x) +
        ap2 (sumF (fam (addBody a b) b)) m (pairT m x) ≐
      m * ap2 (prodF (addBody a b)) m x := by
  refine (sum_add _ _ m (pairT m x)).eqSymm.eqTrans ?_
  refine sum_const_of _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pair, shift_prod]
  rw [inst2_addBody]
  have a₁ := natEq (fam_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (addBody a b) a
    (var 0) (Syn.shift m) (Syn.shift x))
  have a₂ := natEq (fam_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (addBody a b) b
    (var 0) (Syn.shift m) (Syn.shift x))
  have l := lo_mul (addBody a b) (Prf.hyp0 (Γ := Γ.map Fm.shift)
    (φ := lt (var 0) (Syn.shift m))) (x := Syn.shift x)
  rw [inst2_addBody] at l
  have a₃ := natEq l
  apply deriveNat; ipra_simps
  rw [a₁, a₂]
  linear_combination a₃

end Sum

/-! ## The comparison without roots -/

section Algebra

variable {n₀ x y P Pa Pb E Q : PTm n}

local notation "𝔪" => succ n₀

theorem k_pos (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] pw 𝔪 𝔪 * pw P 𝔪 ≐ succ (pred (pw 𝔪 𝔪 * pw P 𝔪)) :=
  pos_mul' (pw_pos' (congrSucc (pred_succ n₀).eqSymm) 𝔪) (pw_pos' hP 𝔪)

/-- The case `x Q ≤ E y`. -/
theorem box_case₁ (hxy : Γ ⊢[PRAAx] x + y ≐ 𝔪 * P)
    (sA : Γ ⊢[PRAAx] le (pw 𝔪 𝔪 * (Pa * pw P 𝔪)) (pw x 𝔪 * P))
    (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (c₁ : Γ ⊢[PRAAx] le (x * Q) (E * y)) :
    Γ ⊢[PRAAx] le (Pa * pw (E + Q) 𝔪) (pw E 𝔪 * P) := by
  have k₁ : Γ ⊢[PRAAx] le (x * (E + Q)) (E * (𝔪 * P)) := by
    refine le_of_eq_add (d := monus (E * y) (x * Q)) ?_
    ipra_lc natEq (eq_add_of_le c₁) - 𝔞 E * natEq hxy
  have k₃ : Γ ⊢[PRAAx] le (pw x 𝔪 * pw (E + Q) 𝔪) (pw E 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪)) :=
    le_congr (pw_mul_base x (E + Q) 𝔪)
      ((pw_mul_base E (𝔪 * P) 𝔪).eqTrans (congrMul (.eqRefl _) (pw_mul_base 𝔪 P 𝔪)))
      (pw_le_pw 𝔪 k₁)
  have m₁ := mul_le_mul_right (pw (E + Q) 𝔪) sA
  have m₂ := mul_le_mul_right P k₃
  have tot : Γ ⊢[PRAAx] le (pw 𝔪 𝔪 * (Pa * pw P 𝔪) * pw (E + Q) 𝔪)
      (pw E 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪) * P) :=
    le_trans m₁ (le_congr (by ipra_ring) (.eqRefl _) m₂)
  have big : Γ ⊢[PRAAx] le (succ (pred (pw 𝔪 𝔪 * pw P 𝔪)) * (Pa * pw (E + Q) 𝔪))
      (succ (pred (pw 𝔪 𝔪 * pw P 𝔪)) * (pw E 𝔪 * P)) := by
    refine le_congr ?_ ?_ tot
    · ipra_lc (𝔞 Pa * 𝔞 (pw (E + Q) 𝔪)) * natEq (k_pos (n₀ := n₀) hP)
    · ipra_lc (𝔞 (pw E 𝔪) * 𝔞 P) * natEq (k_pos (n₀ := n₀) hP)
  exact mul_le_cancel big

/-- The case `E y ≤ x Q`, `Q ≥ 1`. -/
theorem box_case₂ (hxy : Γ ⊢[PRAAx] x + y ≐ 𝔪 * P)
    (sB : Γ ⊢[PRAAx] le (pw 𝔪 𝔪 * (Pb * pw P 𝔪)) (pw y 𝔪 * P))
    (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q))
    (H : Γ ⊢[PRAAx] le (pw Q 𝔪 * Pa) (pw E 𝔪 * Pb)) (c₂ : Γ ⊢[PRAAx] le (E * y) (x * Q)) :
    Γ ⊢[PRAAx] le (Pa * pw (E + Q) 𝔪) (pw E 𝔪 * P) := by
  have k₁ : Γ ⊢[PRAAx] le (y * (E + Q)) (Q * (𝔪 * P)) := by
    refine le_of_eq_add (d := monus (x * Q) (E * y)) ?_
    ipra_lc natEq (eq_add_of_le c₂) - 𝔞 Q * natEq hxy
  have k₃ : Γ ⊢[PRAAx] le (pw y 𝔪 * pw (E + Q) 𝔪) (pw Q 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪)) :=
    le_congr (pw_mul_base y (E + Q) 𝔪)
      ((pw_mul_base Q (𝔪 * P) 𝔪).eqTrans (congrMul (.eqRefl _) (pw_mul_base 𝔪 P 𝔪)))
      (pw_le_pw 𝔪 k₁)
  have t₁ := mul_le_mul_right (pw 𝔪 𝔪 * pw P 𝔪 * pw (E + Q) 𝔪) H
  have t₂ := mul_le_mul_right (pw E 𝔪 * pw (E + Q) 𝔪) sB
  have t₃ := mul_le_mul_right (pw E 𝔪 * P) k₃
  have tot : Γ ⊢[PRAAx] le (pw Q 𝔪 * Pa * (pw 𝔪 𝔪 * pw P 𝔪 * pw (E + Q) 𝔪))
      (pw Q 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪) * (pw E 𝔪 * P)) :=
    le_trans t₁ (le_trans (le_congr (by ipra_ring) (.eqRefl _) t₂)
      (le_congr (by ipra_ring) (.eqRefl _) t₃))
  have hK := pos_mul' (pw_pos' hQ 𝔪) (k_pos (n₀ := n₀) hP)
  have big : Γ ⊢[PRAAx]
      le (succ (pred (pw Q 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪))) * (Pa * pw (E + Q) 𝔪))
        (succ (pred (pw Q 𝔪 * (pw 𝔪 𝔪 * pw P 𝔪))) * (pw E 𝔪 * P)) := by
    refine le_congr ?_ ?_ tot
    · ipra_lc (𝔞 Pa * 𝔞 (pw (E + Q) 𝔪)) * natEq hK
    · ipra_lc (𝔞 (pw E 𝔪) * 𝔞 P) * natEq hK
  exact mul_le_cancel big

/-- The comparison of `x Q` with `E y` decides which of the two families is used. -/
theorem box_alg (hxy : Γ ⊢[PRAAx] x + y ≐ 𝔪 * P)
    (sA : Γ ⊢[PRAAx] le (pw 𝔪 𝔪 * (Pa * pw P 𝔪)) (pw x 𝔪 * P))
    (sB : Γ ⊢[PRAAx] le (pw 𝔪 𝔪 * (Pb * pw P 𝔪)) (pw y 𝔪 * P))
    (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (H : Γ ⊢[PRAAx] le (pw Q 𝔪 * Pa) (pw E 𝔪 * Pb)) :
    Γ ⊢[PRAAx] le (Pa * pw (E + Q) 𝔪) (pw E 𝔪 * P) := by
  refine .orE (zero_or_succ Q) ?_ ?_
  · refine box_case₁ hxy.wk sA.wk hP.wk ?_
    exact le_congr ((congrMul (.eqRefl x) Prf.hyp0).eqTrans (mul_zero x)).eqSymm (.eqRefl _)
      (zero_le _)
  · refine .orE (le_total (x * Q) (E * y)) ?_ ?_
    · exact box_case₁ hxy.wk.wk sA.wk.wk hP.wk.wk Prf.hyp0
    · exact box_case₂ hxy.wk.wk sB.wk.wk hP.wk.wk Prf.hyp1 H.wk.wk Prf.hyp0

end Algebra

/-! ## The box inequality -/

section Box

variable (a b : PTm 2)

/-- `eq:box-base`: for `m = N + 1` coordinates with `a_i + b_i ≥ 1`, `Q^m ∏ a_i ≤ E^m ∏ b_i`
gives `∏ a_i · (E + Q)^m ≤ E^m · ∏ (a_i + b_i)`. -/
theorem box_base {N x E Q : PTm n}
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ N)) ⟶
      (inst2 (addBody a b) (var 0) (Syn.shift x) ≐
        succ (pred (inst2 (addBody a b) (var 0) (Syn.shift x))))))
    (H : Γ ⊢[PRAAx] le (pw Q (succ N) * ap2 (prodF a) (succ N) x)
      (pw E (succ N) * ap2 (prodF b) (succ N) x)) :
    Γ ⊢[PRAAx] le (ap2 (prodF a) (succ N) x * pw (E + Q) (succ N))
      (pw E (succ N) * ap2 (prodF (addBody a b)) (succ N) x) := by
  have hP := prod_pos_bounded (addBody a b) x (succ N) hc
  have sA : Γ ⊢[PRAAx] le (pw (succ N) (succ N) *
        (ap2 (prodF a) (succ N) x * pw (ap2 (prodF (addBody a b)) (succ N) x) (succ N)))
      (pw (ap2 (sumF (fam (addBody a b) a)) (succ N) (pairT (succ N) x)) (succ N) *
        ap2 (prodF (addBody a b)) (succ N) x) := by
    refine le_congr ?_ (.eqRefl _) (mul_le_mul_right (ap2 (prodF (addBody a b)) (succ N) x)
      (finite_amgm (fam (addBody a b) a) N (pairT (succ N) x)))
    ipra_lc 𝔞 (pw (succ N) (succ N)) * natEq (prod_fam (Γ := Γ) (addBody a b) a (succ N) x)
  have sB : Γ ⊢[PRAAx] le (pw (succ N) (succ N) *
        (ap2 (prodF b) (succ N) x * pw (ap2 (prodF (addBody a b)) (succ N) x) (succ N)))
      (pw (ap2 (sumF (fam (addBody a b) b)) (succ N) (pairT (succ N) x)) (succ N) *
        ap2 (prodF (addBody a b)) (succ N) x) := by
    refine le_congr ?_ (.eqRefl _) (mul_le_mul_right (ap2 (prodF (addBody a b)) (succ N) x)
      (finite_amgm (fam (addBody a b) b) N (pairT (succ N) x)))
    ipra_lc 𝔞 (pw (succ N) (succ N)) * natEq (prod_fam (Γ := Γ) (addBody a b) b (succ N) x)
  exact box_alg (sum_fam a b (succ N) x) sA sB hP H

end Box

/-! ## The rational product inequality -/

section Product

variable (t : PTm 2)

/-- The constant `D`, with the parameter `⟨D, x⟩`. -/
def dB : PTm 2 := fstT (var 1)
/-- `t_i`, with the parameter `⟨D, x⟩`. -/
def tB : PTm 2 := sub2 t (var 0) (sndT (var 1))

theorem d_at (i D x : PTm n) : Γ ⊢[PRAAx] inst2 dB i (pairT D x) ≐ D := by
  have h : inst2 (dB : PTm 2) i (pairT D x) = fstT (pairT D x) := by simp [inst2, dB]
  rw [h]
  exact fst_pair _ _

theorem t_at (i D x : PTm n) : Γ ⊢[PRAAx] inst2 (tB t) i (pairT D x) ≐ inst2 t i x := by
  have h : inst2 (tB t) i (pairT D x) = inst2 t i (sndT (pairT D x)) := by
    simp only [tB, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrInst2 t (.eqRefl _) (snd_pair _ _)

/-- The term `D + t_i`. -/
theorem dt_at (i D x : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody dB (tB t)) i (pairT D x) ≐ D + inst2 t i x := by
  rw [inst2_addBody]
  exact congrAdd (d_at i D x) (t_at t i D x)

/-- `lem:box-product`, for the rationals `t_i/D` and `Q/D` (`D ≥ 1`) and `m = N + 1` factors:
`Q^m ≤ ∏ t_i` gives `(D + Q)^m ≤ ∏ (D + t_i)`. -/
theorem box_product {N x D Q : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hq : Γ ⊢[PRAAx] le (pw Q (succ N)) (ap2 (prodF t) (succ N) x)) :
    Γ ⊢[PRAAx] le (pw (D + Q) (succ N))
      (ap2 (prodF (addBody dB (tB t))) (succ N) (pairT D x)) := by
  have pa : Γ ⊢[PRAAx] ap2 (prodF dB) (succ N) (pairT D x) ≐ pw D (succ N) := by
    refine prod_const_of _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    exact d_at _ _ _
  have pb : Γ ⊢[PRAAx] ap2 (prodF (tB t)) (succ N) (pairT D x) ≐ ap2 (prodF t) (succ N) x := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    exact t_at t _ _ _
  have hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ N)) ⟶
      (inst2 (addBody dB (tB t)) (var 0) (Syn.shift (pairT D x)) ≐
        succ (pred (inst2 (addBody dB (tB t)) (var 0) (Syn.shift (pairT D x)))))) := by
    refine .allI (.impI ?_)
    have hD' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift D ≐ succ (pred (Syn.shift D)) := by
      simpa [Fm.shift, Syn.shift] using hD.shift
    simp only [shift_pair]
    refine eq_succ_pred (y := pred (Syn.shift D) + inst2 t (var 0) (Syn.shift x)) ?_
    ipra_lc natEq (dt_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) t (var 0) (Syn.shift D) (Syn.shift x)) +
      natEq (hD'.wk (ψ := lt (var 0) (Syn.shift (succ N))))
  have H : Γ ⊢[PRAAx] le (pw Q (succ N) * ap2 (prodF dB) (succ N) (pairT D x))
      (pw D (succ N) * ap2 (prodF (tB t)) (succ N) (pairT D x)) :=
    le_congr (congrMul (.eqRefl _) pa.eqSymm)
      ((mul_comm _ _).eqTrans (congrMul (.eqRefl _) pb.eqSymm))
      (mul_le_mul_right (pw D (succ N)) hq)
  have bb := box_base dB (tB t) hc H
  have hpos := pw_pos' hD (succ N)
  exact mul_le_cancel (le_congr (congrMul (pa.eqTrans hpos) (.eqRefl _))
    (congrMul hpos (.eqRefl _)) bb)

end Product

end LeanProofs.IPRA.Geometry.BoxProduct
