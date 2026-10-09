import GowersSzemeredi.Proofs16RobustDifferenceProgression

/-! Signed-coordinate calculus and quantitative shrinking of proper centered
progressions. These supply the progression geometry needed for the bridge
selection in the purification of bounded-image column relations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

abbrev CenteredProgression (N : Nat) := OAI.Erdos3.BohrProgression.CyclicCenteredGAP N

/-- Change only the coordinate radii, keeping rank and generators. -/
def centeredProgressionResize {N : Nat} (Q : CenteredProgression N)
    (r : Fin Q.rank → Nat) : CenteredProgression N where
  rank := Q.rank
  step := Q.step
  radius := r

/-- Membership is equivalent to a bounded signed-coordinate representation. -/
theorem centered_progression_mem_iff {N : Nat} (Q : CenteredProgression N) (x : ZMod N) :
    x ∈ Q.carrier ↔ ∃ z : Fin Q.rank → Int,
      (∀ i, |z i| ≤ (Q.radius i : Int)) ∧ x = ∑ i, (z i : ZMod N)*Q.step i := by
  constructor
  · intro hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Q.coeff v, Q.coeff_abs_le v, rfl⟩
  · rintro ⟨z, hz, he⟩
    let v : Q.Param := fun i => ⟨(z i + Q.radius i).toNat, by
      have hi := (abs_le.mp (hz i))
      have ht := Int.toNat_of_nonneg (by omega : 0 ≤ z i + (Q.radius i : Int))
      omega⟩
    have hv : ∀ i, Q.coeff v i = z i := by
      intro i
      change (((z i + Q.radius i).toNat : Nat) : Int) - Q.radius i = z i
      rw [Int.toNat_of_nonneg (by have := (abs_le.mp (hz i)).1; omega)]
      omega
    refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
    simpa only [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval, hv] using he.symm

/-- Smaller radii give a subset of the original progression. -/
theorem centered_progression_resize_subset {N : Nat} (Q : CenteredProgression N)
    (r : Fin Q.rank → Nat) (hr : ∀ i, r i ≤ Q.radius i) :
    (centeredProgressionResize Q r).carrier ⊆ Q.carrier := by
  intro x hx
  obtain ⟨z, hz, he⟩ := (centered_progression_mem_iff _ _).mp hx
  apply (centered_progression_mem_iff Q x).mpr
  exact ⟨z, fun i => (hz i).trans (by exact_mod_cast hr i), he⟩

/-- A smaller coordinate box remains proper. -/
theorem centered_progression_resize_proper {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) (r : Fin Q.rank → Nat) (hr : ∀ i, r i ≤ Q.radius i) :
    (centeredProgressionResize Q r).Proper := by
  let embed : (centeredProgressionResize Q r).Param → Q.Param := fun x i =>
    ⟨(x i).val + Q.radius i - r i, by
      have hi := (x i).isLt
      change (x i).val < 2*r i+1 at hi
      have := hr i
      omega⟩
  have he : ∀ x i, Q.coeff (embed x) i = (centeredProgressionResize Q r).coeff x i := by
    intro x i
    change (((x i).val + Q.radius i - r i : Nat) : Int) - Q.radius i =
      ((x i).val : Int) - r i
    have := hr i
    omega
  have heval : ∀ x, Q.eval (embed x) = (centeredProgressionResize Q r).eval x := by
    intro x
    simp only [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval, he]
    rfl
  intro x y hxy
  have h : embed x = embed y := hQ ((heval x).trans (hxy.trans (heval y).symm))
  funext i
  apply Fin.ext
  have hi := congrArg (fun v => Q.coeff v i) h
  rw [he, he] at hi
  change ((x i).val : Int)-r i = ((y i).val : Int)-r i at hi
  omega

/-- Centered progressions are symmetric, including when they are not proper. -/
theorem centered_progression_neg_mem {N : Nat} (Q : CenteredProgression N)
    {x : ZMod N} (hx : x ∈ Q.carrier) : -x ∈ Q.carrier := by
  obtain ⟨z, hz, he⟩ := (centered_progression_mem_iff Q x).mp hx
  refine (centered_progression_mem_iff Q (-x)).mpr ⟨fun i => -z i, ?_, ?_⟩
  · intro i
    simpa using hz i
  · rw [he]
    simp

/-- Coordinate radius budgets certify addition inside a larger box. -/
theorem centered_progression_add_mem {N : Nat} (Q : CenteredProgression N)
    (r s t : Fin Q.rank → Nat) (hbudget : ∀ i, r i+s i ≤ t i)
    {x y : ZMod N} (hx : x ∈ (centeredProgressionResize Q r).carrier)
    (hy : y ∈ (centeredProgressionResize Q s).carrier) :
    x+y ∈ (centeredProgressionResize Q t).carrier := by
  obtain ⟨z, hz, he⟩ := (centered_progression_mem_iff _ x).mp hx
  obtain ⟨w, hw, hf⟩ := (centered_progression_mem_iff _ y).mp hy
  dsimp only [centeredProgressionResize] at z w hz hw he hf ⊢
  refine (centered_progression_mem_iff _ _).mpr ⟨fun i => z i+w i, ?_, ?_⟩
  · intro i
    calc |z i+w i| ≤ |z i|+|w i| := abs_add_le _ _
      _ ≤ (r i : Int)+s i := add_le_add (hz i) (hw i)
      _ ≤ t i := by exact_mod_cast hbudget i
  · rw [he, hf]
    change (∑ i, (z i : ZMod N)*Q.step i) + (∑ i, (w i : ZMod N)*Q.step i) =
      ∑ i, ((z i+w i : Int) : ZMod N)*Q.step i
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Int.cast_add, add_mul]

/-- Shrink each radius by an integer factor. Zero radii remain available. -/
def centeredProgressionShrink {N : Nat} (Q : CenteredProgression N) (m : Nat) :
    CenteredProgression N := centeredProgressionResize Q (fun i => Q.radius i/m)

theorem centered_progression_shrink_subset {N : Nat} (Q : CenteredProgression N) (m : Nat) :
    (centeredProgressionShrink Q m).carrier ⊆ Q.carrier :=
  centered_progression_resize_subset Q _ (fun i => Nat.div_le_self _ _)

theorem centered_progression_shrink_proper {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) (m : Nat) : (centeredProgressionShrink Q m).Proper :=
  centered_progression_resize_proper Q hQ _ (fun i => Nat.div_le_self _ _)

/-- Shrinking loses at most a factor `(2m)^rank` in cardinality. -/
theorem centered_progression_shrink_card {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) {m : Nat} (hm : 0 < m) :
    Q.carrier.card ≤ (2*m)^Q.rank*(centeredProgressionShrink Q m).carrier.card := by
  rw [Q.card_carrier_of_proper hQ,
    (centeredProgressionShrink Q m).card_carrier_of_proper (centered_progression_shrink_proper Q hQ m)]
  dsimp only [centeredProgressionShrink, centeredProgressionResize]
  have hi : ∀ i, 2*Q.radius i+1 ≤ (2*m)*(2*(Q.radius i/m)+1) := by
    intro i
    have hmod := Nat.mod_lt (Q.radius i) hm
    have hdiv := Nat.div_add_mod (Q.radius i) m
    calc 2*Q.radius i+1 ≤ 2*(m*(Q.radius i/m)+m) := by omega
      _ ≤ (2*m)*(2*(Q.radius i/m)+1) := by
        nlinarith only [Nat.zero_le (m*(Q.radius i/m))]
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun i _ => Nat.zero_le (2*Q.radius i+1)) (fun i _ => hi i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow] at hprod ⊢
  convert hprod using 1 <;> rfl

/-- All `m`-fold sums of the shrinking lie in the original progression. -/
theorem centered_progression_shrink_sum_mem {N m : Nat} (Q : CenteredProgression N)
    (xs : Fin m → ZMod N) (hxs : ∀ j, xs j ∈ (centeredProgressionShrink Q m).carrier) :
    (∑ j, xs j) ∈ Q.carrier := by
  choose z hz he using fun j => (centered_progression_mem_iff _ _).mp (hxs j)
  refine (centered_progression_mem_iff Q _).mpr ⟨fun i => ∑ j, z j i, ?_, ?_⟩
  · intro i
    have hsum : |∑ j, z j i| ≤ ∑ j, |z j i| := Finset.abs_sum_le_sum_abs _ _
    calc |∑ j, z j i| ≤ ∑ j, |z j i| := hsum
      _ ≤ ∑ _j : Fin m, ((Q.radius i/m : Nat) : Int) :=
        Finset.sum_le_sum fun j _ => hz j i
      _ = (m : Int)*(Q.radius i/m) := by simp
      _ ≤ Q.radius i := by exact_mod_cast Nat.mul_div_le (Q.radius i) m
  · simp_rw [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [Finset.sum_mul, centeredProgressionShrink, centeredProgressionResize]

end LeanProofs.GowersSzemeredi
