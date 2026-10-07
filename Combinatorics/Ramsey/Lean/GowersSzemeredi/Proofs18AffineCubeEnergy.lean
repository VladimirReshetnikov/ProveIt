import GowersSzemeredi.Proofs18IntervalCubeEnergy
import GowersSzemeredi.Proofs18AffineTransfer
import GowersSzemeredi.Proofs17PartitionEnergy

/-! Exact local uniformity transfer from an affine progression to a new
cyclic model, including the ambient normalization factor. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Affine changes of variable commute with iterated differences when the
sidelengths are scaled by the common difference. -/
theorem cubeDifference_affine {N k : Nat} (f : ZMod N → Complex) (b d : ZMod N)
    (a : Point N k) (s : ZMod N) :
    cubeDifference (fun x => f (b + d * x)) a s =
      cubeDifference f (fun i => d * a i) (b + d * s) := by
  induction k generalizing s with
  | zero => simp [cubeDifference, iteratedDifference]
  | succ k ih =>
    have ha : a = Fin.cons (a 0) (Fin.tail a) := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [ha]
    rw [show (fun i => d * Fin.cons (a 0) (Fin.tail a) i) =
      Fin.cons (d * a 0) (fun i => d * Fin.tail a i) from by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl]
    rw [cubeDifference_cons, cubeDifference_cons]
    unfold difference
    rw [ih, ih]
    congr 2
    congr 1
    ring

/-- Invertible affine changes preserve the unnormalized uniformity energy. -/
theorem uniformEnergy_affine {N k : Nat} [Fact N.Prime]
    (f : ZMod N → Complex) (b d : ZMod N) (hd : d ≠ 0) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (fun x => f (b + d * x)) a s‖ ^ 2) =
      ∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 := by
  let E : Point N k ≃ Point N k := Equiv.piCongrRight (fun _ => Equiv.mulLeft₀ d hd)
  let F : ZMod N ≃ ZMod N := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft b)
  have hinner (a : Point N k) :
      (∑ s : ZMod N, cubeDifference (fun x => f (b + d * x)) a s) =
        ∑ s : ZMod N, cubeDifference f (E a) s := by
    simp_rw [cubeDifference_affine]
    exact F.sum_comp (cubeDifference f (E a))
  simp_rw [hinner]
  exact E.sum_comp (fun a => ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2)

/-- Function on the index interval of a progression. -/
def ModAP.pullbackFunction {N : Nat} (P : ModAP N) (f : ZMod N → Complex) :
    Fin P.length → Complex := fun i => f (P.index i)

/-- A short progression becomes the standard interval under its affine
parametrization. The support identity uses the nonzero step explicitly. -/
theorem ModAP.restrict_affine_eq_intervalExtension {N : Nat} [Fact N.Prime]
    (P : ModAP N) (f : ZMod N → Complex) (hd : P.step ≠ 0) (hL : P.length ≤ N) :
    (fun x => restrictToCell P.carrier f (P.start + P.step * x)) =
      intervalExtension N (P.pullbackFunction f) := by
  classical
  funext x
  have hmem : P.start + P.step * x ∈ P.carrier ↔ x.val < P.length := by
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      have hi' : (i : ZMod N) = x := by
        apply mul_left_cancel₀ hd
        have heq := add_left_cancel hi
        simpa only [mul_comm] using heq
      have hv : x.val = i := by rw [← hi', ZMod.val_natCast_of_lt (i.isLt.trans_le hL)]
      rw [hv]
      exact i.isLt
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨⟨x.val, hx⟩, Finset.mem_univ _, ?_⟩
      simp only [ZMod.natCast_zmod_val]
      ring
  by_cases hx : x.val < P.length
  · rw [restrictToCell, if_pos (hmem.mpr hx), intervalExtension, dif_pos hx]
    simp only [ModAP.pullbackFunction, ModAP.index, ZMod.natCast_zmod_val]
    congr 1
    ring
  · rw [restrictToCell, if_neg (fun h => hx (hmem.mp h)), intervalExtension, dif_neg hx]

/-- Exact energy equality for a function restricted to a short progression
and its index function in a new sufficiently large modulus. -/
theorem ModAP.restrict_uniformEnergy_eq {N M k : Nat} [Fact N.Prime] [NeZero M]
    (P : ModAP N) (f : ZMod N → Complex) (hd : P.step ≠ 0)
    (hN : (k + 2) * P.length ≤ N) (hM : (k + 2) * P.length ≤ M) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (restrictToCell P.carrier f) a s‖ ^ 2) =
      ∑ a : Point M k, ‖∑ s : ZMod M,
        cubeDifference (intervalExtension M (P.pullbackFunction f)) a s‖ ^ 2 := by
  have hL : P.length ≤ N := (Nat.le_mul_of_pos_left P.length (by omega)).trans hN
  have h := uniformEnergy_affine (k := k) (restrictToCell P.carrier f) P.start P.step hd
  rw [P.restrict_affine_eq_intervalExtension f hd hL] at h
  exact h.symm.trans (intervalExtension_uniformEnergy_eq hN hM (P.pullbackFunction f))

/-- Uniformity transport with the exact power of the ratio of moduli. -/
theorem ModAP.restrict_uniform_iff {N M k : Nat} [Fact N.Prime] [NeZero M]
    (P : ModAP N) (f : ZMod N → Complex) (hd : P.step ≠ 0)
    (hN : (k + 2) * P.length ≤ N) (hM : (k + 2) * P.length ≤ M) (alpha : Real) :
    UniformOfDegree (restrictToCell P.carrier f) alpha k ↔
      UniformOfDegree (intervalExtension M (P.pullbackFunction f))
        (alpha * ((N : Real) / M) ^ (k + 2)) k := by
  have hMne : (M : Real) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hscale : (alpha * ((N : Real) / M) ^ (k + 2)) * (M : Real) ^ (k + 2) =
      alpha * (N : Real) ^ (k + 2) := by rw [div_pow]; field_simp
  unfold UniformOfDegree
  rw [P.restrict_uniformEnergy_eq f hd hN hM, hscale]

end LeanProofs.GowersSzemeredi
