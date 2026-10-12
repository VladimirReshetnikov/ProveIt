import GowersSzemeredi.Proofs05IntegerRepresentatives
import GowersSzemeredi.Proofs13ContextExtraction

/-! The small-width case of the printed Theorem 13.12, over every prime
modulus without an eventual-large-modulus hypothesis. A single large
Fourier point lies in a genuine two-by-two integer square. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def adjacentIntegerAP {N : Nat} (x : ZMod N) : NatAP :=
  ⟨min x.val (N - 2), 1, 2⟩

theorem adjacentIntegerAP_hasIntegerRepresentatives {N : Nat} [NeZero N]
    (hN : 2 ≤ N) (x : ZMod N) :
    ((adjacentIntegerAP x).toModAP N).HasIntegerRepresentatives := by
  apply NatAP.toModAP_hasIntegerRepresentatives_of_bound _ (by simp [adjacentIntegerAP])
  intro i hi
  have hstart : min x.val (N - 2) ≤ N - 2 := min_le_right _ _
  change min x.val (N - 2) + i * 1 < N
  change i < 2 at hi
  omega

theorem adjacentIntegerAP_mem {N : Nat} [NeZero N] (hN : 2 ≤ N) (x : ZMod N) :
    x ∈ ((adjacentIntegerAP x).toModAP N).carrier := by
  classical
  let a := min x.val (N - 2)
  have ha : a ≤ x.val := min_le_left _ _
  have hx := ZMod.val_lt x
  have hi : x.val - a < 2 := by
    dsimp [a]
    rw [min_def]
    split_ifs <;> omega
  have heq : a + (x.val - a) = x.val := Nat.add_sub_of_le ha
  refine Finset.mem_image.mpr ⟨⟨x.val - a, hi⟩, Finset.mem_univ _, ?_⟩
  simp only [NatAP.toModAP, adjacentIntegerAP, Nat.cast_one]
  change ((a : ZMod N) + ((x.val - a : Nat) : ZMod N) * 1) = x
  rw [mul_one, ← Nat.cast_add, heq, ZMod.natCast_zmod_val]

/-- Nonuniformity supplies at least one large Fourier point, without an
asymptotic modulus assumption. The prepared graph gives more structure,
but no structural hypothesis is assumed here. -/
theorem cubic_nonuniformity_large_second_fourier {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ z : Pair N, ∃ r : ZMod N, alpha * N / 2 ≤
      ‖secondDifferenceFourier f z.1 z.2 r‖ := by
  obtain ⟨A, phi, hcard, _, hfourier⟩ := section13_prepared_frequency_graph alpha ha ha1 f hf hnot
  have hpos : 0 < (A.card : Real) :=
    (mul_pos (pow_pos (by positivity : (0 : Real) < alpha / 2) _)
      (pow_pos (by exact_mod_cast NeZero.pos N : (0 : Real) < N) _)).trans_le hcard
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨z, hz⟩ := hA
  exact ⟨z, phi z, by simpa only [div_mul_eq_mul_div] using hfourier z hz⟩

/-- The printed size and density bounds of Theorem 13.12 hold whenever
its target side length is at most two. Both progressions have genuine
integer representatives, for every prime modulus in this regime. -/
theorem theorem_13_12_integer_small {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsize : (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step ≠ 0 ∧ P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
      Q.HasIntegerRepresentatives ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  classical
  have hN : 2 ≤ N := (Fact.out : Nat.Prime N).two_le
  obtain ⟨z, r, hlarge⟩ := cubic_nonuniformity_large_second_fourier alpha ha ha1 f hf hnot
  let P := (adjacentIntegerAP z.1).toModAP N
  let Q := (adjacentIntegerAP z.2).toModAP N
  let B : Finset (Pair N) := {z}
  let phi : Pair N → ZMod N := fun _ => r
  refine ⟨P, Q, B, phi, ?_, rfl, adjacentIntegerAP_hasIntegerRepresentatives hN _,
    adjacentIntegerAP_hasIntegerRepresentatives hN _, rfl, hsize, ?_, ?_, ?_, ?_⟩
  · simp [P, NatAP.toModAP, adjacentIntegerAP]
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_product.mpr ⟨adjacentIntegerAP_mem hN _, adjacentIntegerAP_mem hN _⟩
  · have hhalf : alpha / 2 ≤ (1 / 2 : Real) := by linarith only [ha1]
    have hgamma1 : alpha / 2 ≤ 1 := by linarith only [ha1]
    have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (1 / 4 : Real) := by
      have hexp : 2 ≤ (2 : Nat) ^ 76 := by
        have h := Nat.lt_two_pow_self (n := 76)
        omega
      calc
        _ ≤ (alpha / 2) ^ (2 : Nat) :=
          pow_le_pow_of_le_one (by positivity) hgamma1 hexp
        _ ≤ (1 / 2 : Real) ^ (2 : Nat) := pow_le_pow_left₀ (by positivity) hhalf _
        _ = 1 / 4 := by norm_num
    change (alpha / 2) ^ ((2 : Nat) ^ 76) * (2 : Real) * 2 ≤ (B.card : Real)
    simp only [B, Finset.card_singleton, Nat.cast_one]
    exact (show ∀ b : Real, b ≤ 1 / 4 → b * 2 * 2 ≤ 1 from by
      intro b hb; linarith only [hb]) _ hcoef
  · exact ⟨phi, ⟨r, 0, 0, 0, by intro w; simp [phi]⟩, fun _ _ => rfl⟩
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact hlarge

end LeanProofs.GowersSzemeredi
