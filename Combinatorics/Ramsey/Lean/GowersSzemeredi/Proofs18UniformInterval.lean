import GowersSzemeredi.Proofs03ProgressionExistence
import GowersSzemeredi.Proofs18AffineTransfer

/-!
# The uniform stopping cases for Section 18

Apply the proved cyclic Corollary 3.6 and then the interval/affine transfer.
The density parameter is always relative to the cyclic modulus; it is not
silently identified with the density on the underlying integer interval.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Corollary 3.6 gives an ordinary progression when the embedded set lies in
a short integer interval. -/
theorem hasNatAP_of_uniform_interval {N n k : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 n) (hsize : 2 * n < N)
    (hk : 2 ≤ k) (hkN : k ≤ N) (alpha delta : Real) (hdelta : 0 < delta)
    (hcard : (A.card : Real) = delta * N)
    (huniform : UniformSetOfDegree (A.image fun x : Nat => (x : ZMod N))
      alpha (k - 2))
    (halpha : alpha ≤ (delta / 2) ^ ((k : Real) * 2 ^ k))
    (hscale : 32 * (k : Real) ^ 2 * delta ^ (-(k : Real)) ≤ N) :
    HasNatAP A k := by
  classical
  apply hasNatAP_of_hasModAP_image A hA hsize
  apply corollary_3_6_holds N k hkN _ alpha delta hdelta hk _ huniform halpha hscale
  have hcastCard : (A.image fun x : Nat => (x : ZMod N)).card = A.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj hij
    have hiN : i < N := by have := (Finset.mem_Icc.mp (hA hi)).2; omega
    have hjN : j < N := by have := (Finset.mem_Icc.mp (hA hj)).2; omega
    have h := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using h
  rw [hcastCard, hcard]

/-- Uniformity in the new prime cyclic model of a proper progression supplies
a stopping case for the density-increment iteration on the old modulus. -/
theorem ModAP.hasModAP_of_uniform_cyclic_pullback {N M k : Nat}
    [NeZero M] [Fact M.Prime]
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N))
    (hsize : 2 * P.length < M) (hk : 2 ≤ k) (hkM : k ≤ M)
    (alpha delta : Real) (hdelta : 0 < delta)
    (hcard : ((A ∩ P.carrier).card : Real) = delta * M)
    (huniform : UniformSetOfDegree
      ((P.pullback A).image fun i : Nat => (i : ZMod M)) alpha (k - 2))
    (halpha : alpha ≤ (delta / 2) ^ ((k : Real) * 2 ^ k))
    (hscale : 32 * (k : Real) ^ 2 * delta ^ (-(k : Real)) ≤ M) :
    HasModAP A k := by
  classical
  apply P.hasModAP_of_cyclic_pullback hP A hk hsize
  apply corollary_3_6_holds M k hkM _ alpha delta hdelta hk _ huniform halpha hscale
  rw [P.card_cyclic_pullback hP A (by omega), hcard]

end LeanProofs.GowersSzemeredi
