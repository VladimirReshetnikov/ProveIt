import GowersSzemeredi.Proofs08QuadraticFrequencies
import GowersSzemeredi.Proofs13CoefficientPartition
import GowersSzemeredi.Proofs13CommonStepCover

/-! Affine frequency data on a long progression, with its actual relative
mass retained. These statements make no asymptotic assumption on the modulus. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The entire cyclic group is an indexed progression of length N. -/
@[simp] theorem modInterval_zero_modulus_carrier (N : Nat) [NeZero N] :
    (modInterval N 0 N).carrier = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro x
  refine Finset.mem_image.mpr ⟨⟨x.val, x.val_lt⟩, Finset.mem_univ _, ?_⟩
  change 0 + (x.val : ZMod N) * 1 = x
  simp

/-- A dense Freiman frequency map agrees with a global affine function on a
dense subset of one long, proper progression with nonzero step. -/
theorem freiman_frequencies_affine_progression
    (N : Nat) [Fact N.Prime] (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hmass : delta * N ≤ (B.card : Real)) (hphi : FreimanHom 8 B phi) :
    ∃ P : ModAP N, ∃ D : Finset (ZMod N), ∃ a b : ZMod N,
      P.step != 0 ∧ P.IsProper ∧ D ⊆ B ∧ D ⊆ P.carrier ∧
      (N : Real) ^ cor711Exponent delta 1 ≤ P.length ∧
      delta * P.length ≤ (D.card : Real) ∧
      ∀ x ∈ D, phi x = a * x + b := by
  classical
  let R := modInterval N 0 N
  have hRuniv : R.carrier = Finset.univ := modInterval_zero_modulus_carrier N
  have hR : R.IsProper := by
    change R.carrier.card = N
    rw [hRuniv, Finset.card_univ, ZMod.card]
  obtain ⟨M, Q, hp, hcell⟩ := corollary_7_11_all_scales_universal N R B delta
    hR (by simp [R, modInterval]) (NeZero.pos N) hδ hδone
    (by rw [hRuniv]; exact Finset.subset_univ _) hmass
  have hmass' : delta * R.carrier.card ≤ (B.card : Real) := by
    simpa only [hRuniv, Finset.card_univ, ZMod.card] using hmass
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell B R.carrier id (fun j ↦ (Q j).carrier)
    (by rw [hRuniv]; exact Finset.univ_nonempty) hp
    (fun _ _ ↦ by rw [hRuniv]; exact Finset.mem_univ _) hmass'
  obtain ⟨hstep, hproper, hlen, hlinear⟩ := hcell j
  obtain ⟨a, b, hab⟩ := hlinear phi hphi
  refine ⟨Q j, B.filter (fun x ↦ x ∈ (Q j).carrier), a, b,
    hstep, hproper, Finset.filter_subset _ _, ?_, hlen, ?_, ?_⟩
  · exact fun _ hx ↦ (Finset.mem_filter.mp hx).2
  · simpa only [id_eq, show (Q j).carrier.card = (Q j).length from hproper] using hj
  · intro x hx
    obtain ⟨hxB, hxQ⟩ := Finset.mem_filter.mp hx
    exact hab x (Finset.mem_filter.mpr ⟨hxQ, hxB⟩)

/-- The degree-two obstruction produces a long affine Fourier progression. -/
theorem quadratic_nonuniformity_affine_frequencies
    (N : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 2) :
    ∃ P : ModAP N, ∃ D : Finset (ZMod N), ∃ a b : ZMod N,
      P.step != 0 ∧ P.IsProper ∧ D ⊆ P.carrier ∧
      (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 ≤ P.length ∧
      (alpha / 2) ^ (12359 : Nat) * P.length ≤ (D.card : Real) ∧
      ∀ x ∈ D, alpha / 2 * N ≤ ‖fourier (difference f x) (a * x + b)‖ := by
  obtain ⟨B, phi, hmass, hfreiman, hlarge⟩ :=
    quadratic_nonuniformity_freiman_frequencies N f alpha hα hαone hf hnot
  obtain ⟨P, D, a, b, hs, hP, hDB, hDP, hl, hm, hab⟩ :=
    freiman_frequencies_affine_progression N B phi ((alpha / 2) ^ (12359 : Nat))
      (by positivity) (pow_le_one₀ (by positivity) (by linarith)) hmass hfreiman
  refine ⟨P, D, a, b, hs, hP, hDP, hl, hm, fun x hx ↦ ?_⟩
  rw [← hab x hx]
  exact hlarge x (hDB hx)

end LeanProofs.GowersSzemeredi
