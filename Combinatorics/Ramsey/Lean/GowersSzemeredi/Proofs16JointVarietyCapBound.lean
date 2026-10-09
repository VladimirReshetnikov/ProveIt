import GowersSzemeredi.Proofs16VarietySliceProvider
import GowersSzemeredi.Proofs16FreimanVarietyCapBound

/-! Explicit polynomial controls for simultaneous variety-piece covers.
The shared partition costs degree seventeen in the family size and the
structure budget. Extracting the variety pieces remains separate.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A direct lower bound retaining the actual rounded structure rank. -/
theorem section16JointVarietyCoverExponent_rank_lower {C p : Nat}
    (hC : 2 ≤ C) (hp : 0 < p) (n D : Nat) {c : Real}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    let B := milicevicBound D c
    let R := Nat.ceil B
    1 / (4 * section16FreimanVarietyDegree p (n * (2 * R)) (n * R) *
      ((C : Real) * (n * (2 * R) + n * R + 1) + 17 + B)) ≤
      section16JointVarietyCoverExponent C p n D c := by
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
  simpa only [section16JointVarietyCoverExponent, Nat.cast_mul, Nat.cast_ofNat] using
    section16FreimanVariety_capped_lower hC hp
      (n * (2 * Nat.ceil (milicevicBound D c))) (n * Nat.ceil (milicevicBound D c)) hB

/-- Uniform inverse-polynomial dependence on both the number of pieces
and the structure budget, including the empty family. -/
theorem section16JointVarietyCoverExponent_lower {C p : Nat}
    (hC : 2 ≤ C) (hp : 0 < p) (n D : Nat) {c : Real}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    1 / (1024 * (p : Real)^2 * (4 * C + 18) *
      ((n : Real) + 1)^17 * (milicevicBound D c + 2)^17) ≤
      section16JointVarietyCoverExponent C p n D c := by
  let B := milicevicBound D c
  let R := Nat.ceil B
  let T := ((n : Real) + 1) * (B + 2)
  have hB : 0 ≤ B := by
    have h := two_le_milicevic_base hc hc1
    exact pow_nonneg (by linarith) D
  have hR : (R : Real) ≤ B + 1 := (Nat.ceil_lt_add_one hB).le
  have hnR := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg n : (0 : Real) ≤ n)
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hT : B + 2 ≤ T := by
    dsimp [T]
    nlinarith only [mul_nonneg hn (show 0 ≤ B + 2 by linarith)]
  have hTpos : 0 < T := by linarith
  have hR1 : (n * R : Nat) + (1 : Real) ≤ T := by
    dsimp [T]
    push_cast
    nlinarith only [hnR, hn, hB]
  have hR2 : (n * (2 * R) : Nat) + (1 : Real) ≤ 2 * T := by
    dsimp [T]
    push_cast
    nlinarith only [hnR, hn, hB]
  have hd : (section16FreimanVarietyDegree p (n * (2 * R)) (n * R) : Real) ≤
      256 * (p : Real)^2 * T^16 := by
    have hdegree (s r : Nat) : (section16FreimanVarietyDegree p s r : Real) =
        (p : Real)^2 * ((r : Real) + 1)^8 * ((s : Real) + 1)^8 := by
      simp only [section16FreimanVarietyDegree, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_add, Nat.cast_one, pow_two]
      ac_rfl
    have h1 := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ (n * R : Nat) + 1) hR1 8
    have h2 := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ (n * (2 * R) : Nat) + 1) hR2 8
    have h := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hpow : T^8 * (2 * T)^8 = 256 * T^16 := by
      rw [mul_pow (2 : Real) T 8, show (2 : Real)^8 = 256 by norm_num]
      calc
        T^8 * (256 * T^8) = 256 * (T^8 * T^8) := by ac_rfl
        _ = 256 * T^16 := by rw [← pow_add]
    rw [hdegree, mul_assoc]
    calc
      _ ≤ (p : Real)^2 * (T^8 * (2 * T)^8) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = 256 * (p : Real)^2 * T^16 := by rw [hpow]; ac_rfl
  have hL : (C : Real) * ((n * (2 * R) : Nat) + (n * R : Nat) + 1) + 17 + B ≤
      (4 * C + 18) * T := by
    have hsum : ((n * (2 * R) : Nat) : Real) + (n * R : Nat) + 1 ≤ 3 * T := by
      linarith only [hR1, hR2]
    have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg C : (0 : Real) ≤ C)
    nlinarith only [h, hT, hB,
      mul_nonneg (Nat.cast_nonneg C : (0 : Real) ≤ C) hTpos.le]
  have hdpos : (0 : Real) < section16FreimanVarietyDegree p (n * (2 * R)) (n * R) := by
    exact_mod_cast section16FreimanVarietyDegree_pos hp _ _
  apply le_trans _ (section16FreimanVariety_capped_lower hC hp (n * (2 * R)) (n * R) hB)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  rw [mul_assoc (1024 * (p : Real)^2 * (4 * C + 18)), ← mul_pow]
  change _ ≤ 1024 * (p : Real)^2 * (4 * C + 18) * T^17
  have h := mul_le_mul hd hL (by positivity) (by positivity)
  calc
    _ = 4 * ((section16FreimanVarietyDegree p (n * (2 * R)) (n * R) : Real) *
        ((C : Real) * ((n * (2 * R) : Nat) + (n * R : Nat) + 1) + 17 + B)) :=
      mul_assoc _ _ _
    _ ≤ 4 * (256 * (p : Real)^2 * T^16 * ((4 * C + 18) * T)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 1024 * (p : Real)^2 * (4 * C + 18) * T^17 := by
      rw [show (1024 : Real) = 4 * 256 by norm_num, pow_succ T 16]
      ac_rfl

/-- A rational polynomial lower control for the joint cover exponent. -/
def section16PolynomialJointVarietyExponent (C p n D : Nat) (c : Real) : Real :=
  1 / (1024 * (p : Real)^2 * (4 * C + 18) *
    ((n : Real) + 1)^17 * (milicevicBound D c + 2)^17)

theorem section16PolynomialJointVarietyExponent_pos (C n D : Nat) {p : Nat}
    (hp : 0 < p) {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < section16PolynomialJointVarietyExponent C p n D c := by
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
  unfold section16PolynomialJointVarietyExponent
  positivity

theorem section16PolynomialJointVarietyExponent_le_one {C p : Nat}
    (hC : 2 ≤ C) (hp : 0 < p) (n D : Nat) {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    section16PolynomialJointVarietyExponent C p n D c ≤ 1 :=
  (section16JointVarietyCoverExponent_lower hC hp n D hc hc1).trans
    (section16JointVarietyCoverExponent_le_one C n D hp c)

/-- The statement of `exists_polynomial_variety_piece_family_cover` at fixed constants. -/
def PolynomialVarietyPieceFamilyCoverAt (C p : Nat) : Prop :=
  ∀ (N n D : Nat) [NeZero N] [Fact N.Prime] (c : Real),
    0 < c → c ≤ 1 →
    ∀ (A : Fin n → Finset (ZMod N × ZMod N))
      (phi : Fin n → ZMod N × ZMod N → ZMod N),
    (∀ i, IsVarietyPiece D c (phi i) (A i)) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i) (A i) (phi i)) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16PolynomialJointVarietyExponent C p n D c)
        (section16FinsetUnion G)

/-- `exists_polynomial_variety_piece_family_cover` at the constants of its input. -/
theorem polynomialVarietyPieceFamilyCoverAt_of {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hcover : VarietyPieceFamilyCoverAt C p) : PolynomialVarietyPieceFamilyCoverAt C p := by
  unfold PolynomialVarietyPieceFamilyCoverAt
  intro N n D _ _ c hc hc1 A phi hpiece G hG
  exact (hcover N n D c A phi hpiece G hG).weaken (by intros; exact le_rfl)
    (by intros; exact section16PolynomialJointVarietyExponent_pos C n D hp hc hc1)
    (by intros; exact section16JointVarietyCoverExponent_lower hC hp n D hc hc1)

/-- Actual joint covers with an explicit polynomial exponent. -/
theorem exists_polynomial_variety_piece_family_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n D : Nat) [NeZero N] [Fact N.Prime] (c : Real),
    0 < c → c ≤ 1 →
    ∀ (A : Fin n → Finset (ZMod N × ZMod N))
      (phi : Fin n → ZMod N × ZMod N → ZMod N),
    (∀ i, IsVarietyPiece D c (phi i) (A i)) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i) (A i) (phi i)) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16PolynomialJointVarietyExponent C p n D c)
        (section16FinsetUnion G) := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_variety_piece_family_cover
  exact ⟨C, p, hC, hp, polynomialVarietyPieceFamilyCoverAt_of hC hp hcover⟩

/-- The polynomial controls satisfy every range condition required by
the general affine lift, for all sampled families of structured slices. -/
theorem exists_polynomial_variety_slice_provider :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N D : Nat) [NeZero N] [Fact N.Prime] (c : Real),
    0 < c → c ≤ 1 →
    ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
    (∀ t : ZMod N, IsVarietyPiece D c
      (fun q => phi (appendCoordinate (pairPoint q) t)) (section16FinalPairSection B t)) →
    Section16SliceProvider B phi (fun n _ => 9 * n)
      (fun n _ => section16PolynomialJointVarietyExponent C p n D c) ∧
    Section16SliceProviderRanges (fun n _ => 9 * n)
      (fun n _ => section16PolynomialJointVarietyExponent C p n D c) := by
  obtain ⟨C, p, hC, hp, hprovider⟩ := exists_variety_slice_provider
  refine ⟨C, p, hC, hp, ?_⟩
  intro N D _ _ c hc hc1 B phi hpiece
  obtain ⟨hslice, hranges⟩ := hprovider N D c B phi hpiece
  constructor
  · intro n sample
    exact (hslice n sample).weaken (by intros; exact le_rfl)
      (by intros; exact section16PolynomialJointVarietyExponent_pos C n D hp hc hc1)
      (by intros; exact section16JointVarietyCoverExponent_lower hC hp n D hc hc1)
  · intro n eps hn heps heps1
    exact ⟨(hranges n eps hn heps heps1).1,
      section16PolynomialJointVarietyExponent_pos C n D hp hc hc1,
      section16PolynomialJointVarietyExponent_le_one hC hp n D hc hc1⟩

end LeanProofs.GowersSzemeredi
