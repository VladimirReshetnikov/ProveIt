import DiophantineConsistency.ModelRepPell
import DiophantineConsistency.ModelRepInterfaces

/-! # Internal correctness of the Pell-based exponentiation graph

`PowerRepresentation.coordinates` represents `m = n^k` by the certificate of
Mathlib's `Pell.eq_pow_of_pell`. Inside every model of `𝗜𝚺₁` this file proves
that the same syntax is correct for the internal power `ArithmeticPow.power`:

* `x_sub_y_congr`: with `T + (N²+1) = 2·A·N`, the Pell coordinates of base
  `A = C+2` satisfy `yₖ·(A-N) + N^k ≡ xₖ (mod T)` (a one-step induction;
  `f(k+1) = N·f(k) - T·yₖ` in `DiffRing V`);
* `power_le_x`: `A^j ≤ xⱼ(A)`; `pow_bound`: `P < a`, `N ≤ P` give
  `P + (N²+1) < 2·a·N`;
* `powCrit_iff`: the internal certificate holds exactly when `m = power n k`;
* `powCase : ModelRepInterfaces.PowCase`. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace DiophantineConsistency.ModelRepPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR ModelRepBasic ModelRepArith ModelRepPell
open ArithmeticPellRecurrence ArithmeticPow
open AdaptiveEquationSyntax2011 (InternalZero)

/-! ### Pell arithmetic for exponentiation -/

section Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The second Pell coordinate tracks powers modulo `T = 2AN - N² - 1`. -/
theorem x_sub_y_congr (C A N T : V) (hA : C + 2 = A) (hNA : N ≤ A)
    (hT : T + (N * N + 1) = 2 * A * N) (k : V) :
    ∃ q₁ q₂ : V, ycoord k C * (A - N) + power N k + T * q₁ = xcoord k C + T * q₂ := by
  have hsub : (ι (A - N) : DiffRing V) = ι A - ι N := by
    have h1 := congrArg (ι (V := V)) (tsub_add_cancel_of_le hNA)
    rw [map_add] at h1
    exact eq_sub_of_add_eq h1
  have hδ : (ι (delta C) : DiffRing V) = ι A * ι A - 1 := by
    have h1 : delta C + 1 = A * A := by
      rw [← hA]
      unfold delta
      ring
    have h2 := congrArg (ι (V := V)) h1
    rw [map_add, map_one, map_mul] at h2
    exact eq_sub_of_add_eq h2
  have hTι : (ι T : DiffRing V) + (ι N * ι N + 1) = 2 * ι A * ι N := by
    have h1 := congrArg (ι (V := V)) hT
    rw [map_add, map_add, map_mul, map_one, map_mul, map_mul, ModelArithmetic.ι_two] at h1
    exact h1
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 0, by simp⟩
  case succ k ih =>
    obtain ⟨q₁, q₂, h⟩ := ih
    refine ⟨N * q₁ + ycoord k C, N * q₂, ?_⟩
    rw [y_succ, x_succ, power_succ, hA]
    apply ι_injective
    have hι := congrArg (ι (V := V)) h
    simp only [map_add, map_mul] at hι ⊢
    rw [hsub] at hι ⊢
    rw [hδ]
    linear_combination (ι N) * hι + (ι (ycoord k C)) * hTι

/-- The congruence of `x_sub_y_congr` as an equality of residues. -/
theorem x_mod_eq (C A N T k : V) (hA : C + 2 = A) (hNA : N ≤ A)
    (hT : T + (N * N + 1) = 2 * A * N) (hTpos : 0 < T) :
    xcoord k C % T = (ycoord k C * (A - N) + power N k) % T := by
  obtain ⟨q₁, q₂, h⟩ := x_sub_y_congr C A N T hA hNA hT k
  have h1 := congrArg (· % T) h
  simp only [mod_add_mul' _ _ hTpos] at h1
  exact h1.symm

/-- `A^j ≤ xⱼ` for base `A = C+2`. -/
theorem power_le_x (C j : V) : power (C + 2) j ≤ xcoord j C := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    rw [power_succ, x_succ]
    exact le_trans (mul_le_mul_of_nonneg_left ih (Arithmetic.zero_le _)) le_self_add

/-- The size estimate behind `t > n^k`. -/
theorem pow_bound (N P a : V) (hN : 1 ≤ N) (hNP : N ≤ P) (hPa : P < a) :
    P + (N * N + 1) < 2 * a * N := by
  have h1 : P + 1 ≤ a := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hPa
  apply ι_lt_ι.mp
  have e1 : (ι (P + (N * N + 1)) : DiffRing V) = ι P + (ι N * ι N + 1) := by
    rw [map_add, map_add, map_mul, map_one]
  have e2 : (ι (2 * a * N) : DiffRing V) = 2 * ι a * ι N := by
    rw [map_mul, map_mul, ModelArithmetic.ι_two]
  rw [e1, e2]
  have hN' : (1 : DiffRing V) ≤ ι N :=
    calc (1 : DiffRing V) = ι 1 := (map_one (ι (V := V))).symm
      _ ≤ ι N := ι_le_ι.mpr hN
  have hNP' : (ι N : DiffRing V) ≤ ι P := ι_le_ι.mpr hNP
  have h1' : (ι P : DiffRing V) + 1 ≤ ι a := by
    have h := ι_le_ι.mpr h1
    rwa [map_add, map_one] at h
  nlinarith [mul_nonneg (sub_nonneg.mpr h1') (le_trans zero_le_one hN'),
    mul_nonneg (sub_nonneg.mpr hNP') (by linarith : (0 : DiffRing V) ≤ 2 * ι N - 1),
    mul_nonneg (sub_nonneg.mpr hN') (le_trans zero_le_one hN')]

/-- `N ≤ N^k` for `k ≥ 1`. -/
theorem le_power_self (N k : V) (hN : 1 ≤ N) (hk : 0 < k) : N ≤ power N k := by
  have h := power_mono_exponent N 1 k hN (pos_iff_one_le.mp hk)
  rwa [power_one] at h

/-- The chain `N^k ≤ N^j < (w+1)^j ≤ xⱼ(w+1)` for `k ≤ j`, `N ≤ w`, `0 < j`. -/
theorem power_lt_x (C N k j w : V) (hw : w + 1 = C + 2) (hN : 1 ≤ N) (hNw : N ≤ w)
    (hkj : k ≤ j) (hj : 0 < j) : power N k < xcoord j C := by
  calc power N k ≤ power N j := power_mono_exponent N k j hN hkj
    _ < power (w + 1) j :=
      power_strict_base N (w + 1) j (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mpr hNw) hj
    _ = power (C + 2) j := by rw [hw]
    _ ≤ xcoord j C := power_le_x C j

end Arithmetic

/-! ### The internal certificate -/

section Certificate
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The finite certificate of `Pell.eq_pow_of_pell`, raw form of the syntax. -/
def PowFinRawV (m n k w a t z x y : V) : Prop :=
  PellGraph a k x y ∧ x % t = (y * (a - n) + m) % t ∧
    ((2 : ℕ) : V) * a * n = t + (n * n + ((1 : ℕ) : V)) ∧ m < t ∧ n ≤ w ∧ k ≤ w ∧
    INorm (w + ((1 : ℕ) : V)) a (w * z)

/-- The finite certificate of `Pell.eq_pow_of_pell`. -/
def PowFin (m n k w a t z x y : V) : Prop :=
  PellGraph a k x y ∧ x % t = (y * (a - n) + m) % t ∧ 2 * a * n = t + (n * n + 1) ∧
    m < t ∧ n ≤ w ∧ k ≤ w ∧ INorm (w + 1) a (w * z)

/-- The whole criterion, raw form of the syntax. -/
def PowCritRaw (m n k : V) : Prop :=
  (k = ((0 : ℕ) : V) ∧ m = ((1 : ℕ) : V)) ∨ (((0 : ℕ) : V) < k ∧
    ((n = ((0 : ℕ) : V) ∧ m = ((0 : ℕ) : V)) ∨ (((0 : ℕ) : V) < n ∧
      ∃ z : Fin 6 → V, PowFinRawV m n k (z 0) (z 1) (z 2) (z 3) (z 4) (z 5))))

/-- The whole criterion. -/
def PowCrit (m n k : V) : Prop :=
  (k = 0 ∧ m = 1) ∨ (0 < k ∧ ((n = 0 ∧ m = 0) ∨
    (0 < n ∧ ∃ w a t z x y : V, PowFin m n k w a t z x y)))

theorem powFinRaw_iff (m n k w a t z x y : V) :
    PowFinRawV m n k w a t z x y ↔ PowFin m n k w a t z x y := by
  have h2 : ((2 : ℕ) : V) = 2 := Nat.cast_ofNat
  unfold PowFinRawV PowFin
  simp only [h2, Nat.cast_one]

theorem powCritRaw_iff (m n k : V) : PowCritRaw m n k ↔ PowCrit m n k := by
  unfold PowCritRaw PowCrit
  simp only [Nat.cast_zero, Nat.cast_one, powFinRaw_iff]
  constructor
  · rintro (h | ⟨hk, h | ⟨hn, z, hz⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hk, Or.inl h⟩
    · exact Or.inr ⟨hk, Or.inr ⟨hn, z 0, z 1, z 2, z 3, z 4, z 5, hz⟩⟩
  · rintro (h | ⟨hk, h | ⟨hn, w, a, t, z, x, y, hz⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hk, Or.inl h⟩
    · exact Or.inr ⟨hk, Or.inr ⟨hn, ![w, a, t, z, x, y], hz⟩⟩

/-- Pell's exponentiation criterion inside the model. -/
theorem powCrit_iff (m n k : V) : PowCrit m n k ↔ m = power n k := by
  constructor
  · rintro (⟨hk, hm⟩ | ⟨hk, ⟨hn, hm⟩ | ⟨hn, w, a, t, z, x, y, ⟨ha, hx, hy⟩, hcong, hT, hmt,
      hnw, hkw, hnorm⟩⟩)
    · rw [hk, hm, power_zero]
    · rw [hn, hm, zero_power_of_pos k hk]
    have hN1 : 1 ≤ n := pos_iff_one_le.mp hn
    have hw : 0 < w := lt_of_lt_of_le hn hnw
    obtain ⟨C, hC⟩ : ∃ C, C + 1 = w := ⟨w - 1, tsub_add_cancel_of_le (pos_iff_one_le.mp hw)⟩
    have hw1 : w + 1 = C + 2 := by rw [← hC]; ring
    rw [hw1] at hnorm
    obtain ⟨j, -, hxj, hyj⟩ :=
      ArithmeticPellClassification.solution_index C a (w * z) ((inorm_iff C a (w * z)).mp hnorm)
    have hj : 0 < j := by
      rcases eq_zero_or_pos j with h0 | h0
      · exfalso
        rw [h0, x_zero] at hxj
        rw [← hxj] at ha
        exact (_root_.lt_irrefl _) ha
      · exact h0
    have hwj : w ∣ j := by
      have h1 := (ArithmeticPellCongruences.residue_mod j C w ⟨1, by rw [hC, mul_one]⟩ hw).2
      rw [hyj, mod_mul_self_right] at h1
      exact mod_eq_zero_iff_dvd.mp h1.symm
    have hwle : w ≤ j := LO.FirstOrder.Arithmetic.le_of_dvd hj hwj
    have hPa : power n k < a := by
      rw [← hxj]
      exact power_lt_x C n k j w hw1 hN1 hnw (le_trans hkw hwle) hj
    have hNP : n ≤ power n k := le_power_self n k hN1 hk
    have hPt : power n k < t := by
      have h1 := pow_bound n (power n k) a hN1 hNP hPa
      rw [hT] at h1
      exact lt_of_add_lt_add_right h1
    have hna : n ≤ a := le_of_lt (lt_of_le_of_lt hNP hPa)
    have ht0 : 0 < t := lt_of_le_of_lt (Arithmetic.zero_le m) hmt
    have hac : a - 2 + 2 = a :=
      tsub_add_cancel_of_le (LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp ha)
    have hmod := x_mod_eq (a - 2) a n t k hac hna hT.symm ht0
    rw [← hx, ← hy, hcong, add_comm (y * (a - n)) m, add_comm (y * (a - n)) (power n k)] at hmod
    have hcancel := ArithmeticPellResidueClasses.mod_add_cancel m (power n k) (y * (a - n)) t ht0
      hmod
    rwa [mod_eq_self_of_lt hmt, mod_eq_self_of_lt hPt] at hcancel
  · rintro rfl
    rcases eq_zero_or_pos k with hk | hk
    · exact Or.inl ⟨hk, by rw [hk, power_zero]⟩
    refine Or.inr ⟨hk, ?_⟩
    rcases eq_zero_or_pos n with hn | hn
    · exact Or.inl ⟨hn, by rw [hn]; exact zero_power_of_pos k hk⟩
    refine Or.inr ⟨hn, ?_⟩
    have hN1 : 1 ≤ n := pos_iff_one_le.mp hn
    have hW : 0 < n + k := lt_of_lt_of_le hn le_self_add
    obtain ⟨C, hC⟩ : ∃ C, C + 1 = n + k :=
      ⟨n + k - 1, tsub_add_cancel_of_le (pos_iff_one_le.mp hW)⟩
    have hw1 : n + k + 1 = C + 2 := by rw [← hC]; ring
    obtain ⟨-, s, -, hys⟩ :=
      ArithmeticPellCongruences.residue_quotients (n + k) C (n + k) ⟨1, by rw [hC, mul_one]⟩
    have hz : ycoord (n + k) C = (n + k) * (1 + s) := by rw [hys]; ring
    have hPa : power n k < xcoord (n + k) C :=
      power_lt_x C n k (n + k) (n + k) hw1 hN1 le_self_add le_add_self hW
    have hNP : n ≤ power n k := le_power_self n k hN1 hk
    have ha1 : 1 < xcoord (n + k) C := lt_of_le_of_lt (one_le_power n k hN1) hPa
    have hbound := pow_bound n (power n k) (xcoord (n + k) C) hN1 hNP hPa
    have hle : n * n + 1 ≤ 2 * xcoord (n + k) C * n := le_of_lt (lt_of_le_of_lt le_add_self hbound)
    obtain ⟨T, hT⟩ : ∃ T, T + (n * n + 1) = 2 * xcoord (n + k) C * n :=
      ⟨_, tsub_add_cancel_of_le hle⟩
    have hPT : power n k < T := by
      rw [← hT] at hbound
      exact lt_of_add_lt_add_right hbound
    have hna : n ≤ xcoord (n + k) C := le_of_lt (lt_of_le_of_lt hNP hPa)
    have hac : xcoord (n + k) C - 2 + 2 = xcoord (n + k) C :=
      tsub_add_cancel_of_le (LO.FirstOrder.Arithmetic.one_lt_iff_two_le.mp ha1)
    have hT0 : 0 < T := lt_of_le_of_lt (Arithmetic.zero_le _) hPT
    have hmod := x_mod_eq (xcoord (n + k) C - 2) (xcoord (n + k) C) n T k hac hna hT hT0
    have hnorm : INorm (n + k + 1) (xcoord (n + k) C) ((n + k) * (1 + s)) := by
      rw [hw1, ← hz]
      exact (inorm_iff C _ _).mpr (ArithmeticPellRecurrence.norm (n + k) C)
    exact ⟨n + k, xcoord (n + k) C, T, 1 + s, xcoord k (xcoord (n + k) C - 2),
      ycoord k (xcoord (n + k) C - 2), ⟨ha1, rfl, rfl⟩, hmod, hT.symm, hPT, le_self_add,
      le_add_self, hnorm⟩

end Certificate

/-! ### The syntax -/

section Syntax

/-- The certificate variables `m,n,k | w,a,t,z,x,y`. -/
abbrev WV := PowerRepresentation.CertificateVar

theorem holds_powFiniteRep : Holds PowerRepresentation.finiteRep (fun V _ _ q =>
    PowFinRawV (q (Sum.inl 0)) (q (Sum.inl 1)) (q (Sum.inl 2)) (q (Sum.inr 0)) (q (Sum.inr 1))
      (q (Sum.inr 2)) (q (Sum.inr 3)) (q (Sum.inr 4)) (q (Sum.inr 5))) :=
  holds_congr _ (by intro V _ _ q; exact Iff.rfl)
    (holds_conjunction
      (holds_reindex holds_pellRep
        (![Sum.inr 1, Sum.inl 2, Sum.inr 4, Sum.inr 5] : Fin 4 → WV))
    (holds_conjunction
      (holds_modEqGraphs (graphHolds_natExpr (NatExpr.var (Sum.inr 4 : WV)))
        (graphHolds_add
          (graphHolds_mul (graphHolds_natExpr (NatExpr.var (Sum.inr 5 : WV)))
            (graphHolds_sub (graphHolds_natExpr (NatExpr.var (Sum.inr 1 : WV)))
              (graphHolds_natExpr (NatExpr.var (Sum.inl 1 : WV)))))
          (graphHolds_natExpr (NatExpr.var (Sum.inl 0 : WV))))
        (graphHolds_natExpr (NatExpr.var (Sum.inr 2 : WV))))
    (holds_conjunction
      (holds_naturalEquality
        (2 * NatExpr.var (Sum.inr 1 : WV) * NatExpr.var (Sum.inl 1))
        (NatExpr.var (Sum.inr 2 : WV) +
          (NatExpr.var (Sum.inl 1) * NatExpr.var (Sum.inl 1) + 1)))
    (holds_conjunction
      (holds_naturalLt (NatExpr.var (Sum.inl 0 : WV)) (NatExpr.var (Sum.inr 2)))
    (holds_conjunction
      (holds_naturalLe (NatExpr.var (Sum.inl 1 : WV)) (NatExpr.var (Sum.inr 0)))
    (holds_conjunction
      (holds_naturalLe (NatExpr.var (Sum.inl 2 : WV)) (NatExpr.var (Sum.inr 0)))
      (holds_compose (holds_normRep (0 : Fin 3) 1 2)
        (g := fun i => (![NatExpr.var (Sum.inr 0 : WV) + 1, NatExpr.var (Sum.inr 1),
          NatExpr.var (Sum.inr 0) * NatExpr.var (Sum.inr 3)] i).graphRep)
        (G := fun i V _ _ q => (![NatExpr.var (Sum.inr 0 : WV) + 1, NatExpr.var (Sum.inr 1),
          NatExpr.var (Sum.inr 0) * NatExpr.var (Sum.inr 3)] i).evalSemiring q)
        (fun i => graphHolds_natExpr _))))))))

theorem holds_powCriterionRep : Holds PowerRepresentation.criterionRep
    (fun V _ _ v => PowCritRaw (v 0) (v 1) (v 2)) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_disjunction
      (holds_conjunction (holds_naturalEquality (NatExpr.var (2 : Fin 3)) 0)
        (holds_naturalEquality (NatExpr.var (0 : Fin 3)) 1))
      (holds_conjunction (holds_naturalLt (0 : NatExpr (Fin 3)) (NatExpr.var 2))
        (holds_disjunction
          (holds_conjunction (holds_naturalEquality (NatExpr.var (1 : Fin 3)) 0)
            (holds_naturalEquality (NatExpr.var (0 : Fin 3)) 0))
          (holds_conjunction (holds_naturalLt (0 : NatExpr (Fin 3)) (NatExpr.var 1))
            (holds_existsBlock holds_powFiniteRep)))))

end Syntax

/-- The Pell-based exponentiation graph is internally correct for `power`. -/
theorem powCase : ModelRepInterfaces.PowCase := by
  refine holds_congr _ ?_ (holds_reindex holds_powCriterionRep
    (![none, some 0, some 1] : Fin 3 → Option (Fin 2)))
  intro V _ _ v
  exact (powCritRaw_iff (v none) (v (some 0)) (v (some 1))).trans
    (powCrit_iff (v none) (v (some 0)) (v (some 1)))

end DiophantineConsistency.ModelRepPower
