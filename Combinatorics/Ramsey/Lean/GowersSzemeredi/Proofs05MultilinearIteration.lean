import GowersSzemeredi.Proofs05MultilinearPartition

/-! # Simultaneous multilinear partitions by repeated proper refinement -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def multilinearIterationConstant (k : Nat) : Nat :=
  multilinearPartitionConstant k ^ (2 ^ k)

theorem multilinearPartitionExponent_iteration (k q : Nat) :
    multilinearPartitionExponent k q = ((multilinearIterationConstant k : Real) ^ q)⁻¹ := by
  simp only [multilinearPartitionExponent, multilinearIterationConstant, Nat.cast_pow, ← pow_mul]

theorem multilinearPartitionThreshold_iteration (k q : Nat) :
    multilinearPartitionThreshold k q =
      (2 * polynomialPartitionThreshold k) ^ (multilinearIterationConstant k ^ q) := by
  simp only [multilinearPartitionThreshold, multilinearIterationConstant, ← pow_mul]

theorem multilinearIterationConstant_pos {k : Nat} (hk : 2 ≤ k) :
    0 < multilinearIterationConstant k := by
  have hK := multilinearPartitionConstant_eight_le hk
  unfold multilinearIterationConstant
  positivity

/-- Integral intermediate scale for a simultaneous refinement; ceiling
rounding preserves both the threshold and the desired composed exponent. -/
theorem multilinear_iteration_scale {k q m : Nat} (hk : 2 ≤ k)
    (hm : multilinearPartitionThreshold k (q + 1) ≤ m) :
    ∃ v : Nat, multilinearPartitionThreshold k q ≤ v ∧
      (∀ L : Nat, (m : Real) ^ multilinearPartitionExponent k 1 ≤ L → v ≤ L) ∧
      (m : Real) ^ multilinearPartitionExponent k (q + 1) ≤
        (v : Real) ^ multilinearPartitionExponent k q ∧
      (v : Real) ^ (-multilinearPartitionExponent k q) ≤
        (m : Real) ^ (-multilinearPartitionExponent k (q + 1)) := by
  let C := multilinearIterationConstant k
  let T := multilinearPartitionThreshold k q
  let x : Real := (m : Real) ^ (C : Real)⁻¹
  have hC : 0 < C := multilinearIterationConstant_pos hk
  have hCr : (0 : Real) < C := by exact_mod_cast hC
  have hm2 : 2 ≤ m := (multilinearHeightThreshold_bounds hk (2 ^ k * (q + 1))).1.trans hm
  have hm0 : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hm0 _
  have hr : (m : Real) = x ^ C := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, inv_mul_cancel₀ hCr.ne', Real.rpow_one]
  have hTpow : T ^ C ≤ m := by
    simpa only [T, C, multilinearPartitionThreshold_iteration, pow_succ, pow_mul] using hm
  have hTx : (T : Real) ≤ x := by
    have h : (T : Real) ^ C ≤ x ^ C := by rw [← hr]; exact_mod_cast hTpow
    exact le_of_pow_le_pow_left₀ hC.ne' hx0.le h
  let v := Nat.ceil x
  have hv : x ≤ (v : Real) := Nat.le_ceil x
  have hv0 : (0 : Real) < v := hx0.trans_le hv
  have hexp1 : (m : Real) ^ multilinearPartitionExponent k 1 = x := by
    simp only [multilinearPartitionExponent_iteration, pow_one]
    rfl
  have hroot : (m : Real) ^ multilinearPartitionExponent k (q + 1) =
      x ^ multilinearPartitionExponent k q := by
    rw [multilinearPartitionExponent_iteration, multilinearPartitionExponent_iteration,
      hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    change (C : Real) * ((C : Real) ^ (q + 1))⁻¹ = ((C : Real) ^ q)⁻¹
    rw [pow_succ]
    field_simp
  have hwidth : (m : Real) ^ multilinearPartitionExponent k (q + 1) ≤
      (v : Real) ^ multilinearPartitionExponent k q := by
    rw [hroot]
    exact Real.rpow_le_rpow hx0.le hv (by unfold multilinearPartitionExponent; positivity)
  refine ⟨v, ?_, ?_, hwidth, ?_⟩
  · exact_mod_cast hTx.trans hv
  · intro L hL
    rw [hexp1] at hL
    exact Nat.ceil_le.mpr hL
  · rw [Real.rpow_neg hv0.le, Real.rpow_neg hm0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hm0 _) hwidth

/-- Threshold monotonicity in the number of functions. -/
theorem multilinearPartitionThreshold_mono_q {k q r : Nat} (hk : 2 ≤ k) (hqr : q ≤ r) :
    multilinearPartitionThreshold k q ≤ multilinearPartitionThreshold k r := by
  have hC : 0 < multilinearIterationConstant k := multilinearIterationConstant_pos hk
  have hT : 0 < 2 * polynomialPartitionThreshold k := by
    unfold polynomialPartitionThreshold weylThreshold; positivity
  rw [multilinearPartitionThreshold_iteration, multilinearPartitionThreshold_iteration]
  exact Nat.pow_le_pow_right hT (Nat.pow_le_pow_right hC hqr)

/-- The final exponent is no larger than the first-stage exponent. -/
theorem multilinearPartitionExponent_succ_le_one {k q : Nat} (hk : 2 ≤ k) :
    multilinearPartitionExponent k (q + 1) ≤ multilinearPartitionExponent k 1 := by
  have hC : (1 : Real) ≤ multilinearIterationConstant k := by
    exact_mod_cast multilinearIterationConstant_pos hk
  rw [multilinearPartitionExponent_iteration, multilinearPartitionExponent_iteration]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hC (by omega))

/-- Simultaneous partitioning, including an empty function family as the
induction base. All refinements remain proper. -/
theorem proper_multilinear_simultaneous (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    ∀ (N m : Nat) [NeZero N] (P : Box N k), P.IsProper →
      ∀ mu : Fin q → Point N k → ZMod N,
        multilinearPartitionThreshold k q ≤ m → m ≤ P.width →
        (∀ i, MultilinearOn P.carrier (mu i)) →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (m : Real) ^ multilinearPartitionExponent k q ≤ (Q j).width) ∧
          ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i))
            (2 * (m : Real) ^ (-multilinearPartitionExponent k q) * N) := by
  induction q with
  | zero =>
    intro N m _ P hP mu hm hmP hmu
    refine ⟨1, fun _ => P, ?_, fun _ => hP, ?_, ?_⟩
    · constructor
      · intro x; simp
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · intro j
      simpa [multilinearPartitionExponent] using (show (m : Real) ≤ P.width by exact_mod_cast hmP)
    · intro i; exact Fin.elim0 i
  | succ q ih =>
    intro N m _ P hP mu hm hmP hmu
    have hm1 : multilinearPartitionThreshold k 1 ≤ m :=
      (multilinearPartitionThreshold_mono_q hk (by omega)).trans hm
    obtain ⟨M, Q, hQpart, hQproper, hQbounds⟩ :=
      proper_multilinear_partition P hP (mu 0) hk hm1 hmP (hmu 0)
    obtain ⟨v, hvT, hvle, hvwidth, hvdiam⟩ := multilinear_iteration_scale hk hm
    have hlocal (i : Fin M) (a : Fin q) : MultilinearOn (Q i).carrier (mu a.succ) := by
      obtain ⟨psi, hpsi, heq⟩ := hmu a.succ
      exact ⟨psi, hpsi, fun x hx => heq x (IsPartition.cell_subset hQpart i hx)⟩
    choose L R hRpart hRproper hRwidth hRdiam using fun i =>
      ih N v (Q i) (hQproper i) (fun a => mu a.succ) hvT (hvle _ (hQbounds i).1) (hlocal i)
    have hfinal (i : Fin M) (j : Fin (L i)) (a : Fin (q + 1)) :
        diameterAtMostReal ((R i j).carrier.image (mu a))
          (2 * (m : Real) ^ (-multilinearPartitionExponent k (q + 1)) * N) := by
      refine Fin.cases ?_ (fun b => ?_) a
      · apply diameterAtMostReal_mono
          (Finset.image_mono _ (IsPartition.cell_subset (hRpart i) j)) (hQbounds i).2
        have hmReal : (1 : Real) ≤ m := by
          have h := (multilinearHeightThreshold_bounds hk (2 ^ k * (q + 1))).1.trans hm
          exact_mod_cast (show 1 ≤ m by omega)
        have hpow := Real.rpow_le_rpow_of_exponent_le hmReal
          (neg_le_neg (multilinearPartitionExponent_succ_le_one (q := q) hk))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Nat.cast_nonneg N)
      · apply diameterAtMostReal_mono (Finset.Subset.refl _) (hRdiam i b j)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvdiam (by norm_num)) (Nat.cast_nonneg N)
    refine ⟨∑ i, L i, boxFlatten L R, boxFlatten_partition P Q L R hQpart hRpart, ?_, ?_, ?_⟩
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      exact hRproper z.1 z.2
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      exact hvwidth.trans (hRwidth z.1 z.2)
    · intro a j
      let z := (section5NatFlattenEquiv L).symm j
      exact hfinal z.1 z.2 a

/-- Corollary 5.11, retaining properness at every refinement stage. -/
theorem corollary_5_11_holds : corollary_5_11 := by
  intro N k q m _ P mu hP hk _hq hm hmP hmu
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ :=
    proper_multilinear_simultaneous k hk q N m P hP mu hm hmP hmu
  exact ⟨M, Q, hpart, hproper, fun i j => ⟨hwidth j, hdiam i j⟩⟩

end LeanProofs.GowersSzemeredi
