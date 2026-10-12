import GowersSzemeredi.Proofs05IntegerRepresentatives
import GowersSzemeredi.Proofs16OrientedPartitions

/-! Integer representatives on short containing intervals. These lemmas
connect Section 16's modular index geometry to genuine integer progressions
without introducing a primality hypothesis or losing points. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Integer representability depends only on the carrier and the length,
so a reversal or other carrier-preserving reparameterization is harmless. -/
theorem ModAP.hasIntegerRepresentatives_congr {N : Nat} {P R : ModAP N}
    (hcarrier : P.carrier = R.carrier) (hlen : P.length = R.length) :
    P.HasIntegerRepresentatives ↔ R.HasIntegerRepresentatives := by
  unfold ModAP.HasIntegerRepresentatives
  rw [hcarrier, hlen]

/-- An increasing sequence of canonical representatives gives a genuine
integer AP with exactly the same length and carrier. -/
theorem ModAP.hasIntegerRepresentatives_of_val_formula {N : Nat} [NeZero N]
    (P : ModAP N) (d : Nat) (hd : 0 < d)
    (hformula : ∀ i : Nat, i < P.length →
      (P.start + (i : ZMod N) * P.step).val = P.start.val + i * d) :
    P.HasIntegerRepresentatives := by
  classical
  let Q : NatAP := ⟨P.start.val, d, P.length⟩
  have hbound (i : Nat) (hi : i < Q.length) : Q.start + i * Q.step < N := by
    change P.start.val + i * d < N
    rw [← hformula i hi]
    exact ZMod.val_lt _
  obtain ⟨Q', hQ', hlen, hsub, himage⟩ :=
    Q.toModAP_hasIntegerRepresentatives_of_bound hd hbound
  refine ⟨Q', hQ', hlen, hsub, himage.trans ?_⟩
  unfold ModAP.carrier
  apply Finset.image_congr
  intro i _
  change ((P.start.val : ZMod N) + (i.val : ZMod N) * (d : ZMod N)) =
    P.start + (i.val : ZMod N) * P.step
  have h := congrArg (fun x : Nat => (x : ZMod N)) (hformula i.val i.isLt)
  simpa only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul] using h.symm

/-- Reversing an affine representative sequence reverses its integer
common difference. The statement also handles empty progressions. -/
theorem ModAP.reverse_int_val_formula {N : Nat} [NeZero N]
    (P : ModAP N) (d : Int)
    (hformula : ∀ i : Nat, i < P.length →
      ((P.start + (i : ZMod N) * P.step).val : Int) =
        P.start.val + (i : Int) * d) :
    ∀ i : Nat, i < P.reverse.length →
      ((P.reverse.start + (i : ZMod N) * P.reverse.step).val : Int) =
        P.reverse.start.val + (i : Int) * (-d) := by
  intro i hi
  let j : Fin P.length := ⟨i, hi⟩
  have hj := hformula j.rev.val j.rev.isLt
  have hlast : P.length - 1 < P.length := by change i < P.length at hi; omega
  have hbase := hformula (P.length - 1) hlast
  change ((P.reverse.start.val : Nat) : Int) =
    P.start.val + ((P.length - 1 : Nat) : Int) * d at hbase
  have hsum : P.length - 1 = j.rev.val + i := by
    change P.length - 1 = (P.length - (i + 1)) + i
    have hiL : i < P.length := hi
    omega
  have hsumInt : ((P.length - 1 : Nat) : Int) = (j.rev.val : Int) + (i : Int) := by
    exact_mod_cast hsum
  have hindex := congrArg (fun x : ZMod N => (x.val : Int)) (P.reverse_index j)
  calc
    ((P.reverse.start + (i : ZMod N) * P.reverse.step).val : Int) =
        ((P.start + (j.rev.val : ZMod N) * P.step).val : Int) := hindex
    _ = P.start.val + (j.rev.val : Int) * d := hj
    _ = P.reverse.start.val + (i : Int) * (-d) := by
      rw [hsumInt] at hbase
      nlinarith

/-- The same lifting statement with a positive integer common difference. -/
theorem ModAP.hasIntegerRepresentatives_of_int_val_formula {N : Nat} [NeZero N]
    (P : ModAP N) (d : Int) (hd : 0 < d)
    (hformula : ∀ i : Nat, i < P.length →
      ((P.start + (i : ZMod N) * P.step).val : Int) =
        P.start.val + (i : Int) * d) : P.HasIntegerRepresentatives := by
  have hcast : (d.toNat : Int) = d := Int.toNat_of_nonneg hd.le
  have hpos : 0 < d.toNat := by omega
  apply P.hasIntegerRepresentatives_of_val_formula d.toNat hpos
  intro i hi
  have h := hformula i hi
  rw [← hcast] at h
  exact_mod_cast h

/-- A proper modular progression contained in an initial interval of
length at most half the modulus has genuine integer representatives.
Its orientation can be reversed, but its length and every point survive. -/
theorem ModAP.hasIntegerRepresentatives_of_short_interval {N n : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hn : 2 * n ≤ N)
    (hsub : P.carrier ⊆ (modInterval N 0 n).carrier) :
    P.HasIntegerRepresentatives := by
  by_cases hshort : P.length ≤ 1
  · apply P.hasIntegerRepresentatives_of_val_formula 1 (by omega)
    intro i hi
    have hi0 : i = 0 := by omega
    simp [hi0]
  have hL : 2 ≤ P.length := by omega
  have hd : P.step ≠ 0 := by
    intro hz
    have h := section5IndexPoint_injective_on_range P hP
      (Finset.mem_range.mpr (by omega : 0 < P.length))
      (Finset.mem_range.mpr (by omega : 1 < P.length))
      (show section5IndexPoint P 0 = section5IndexPoint P 1 by simp [section5IndexPoint, hz])
    omega
  let d := P.step.valMinAbs
  have hdne : d ≠ 0 := by
    intro hz
    have hcast := ZMod.coe_valMinAbs P.step
    change (d : ZMod N) = P.step at hcast
    rw [hz, Int.cast_zero] at hcast
    exact hd hcast.symm
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · have hformula := P.reverse_int_val_formula d
      (fun i hi => P.val_affine_of_short_interval hn hsub i hi)
    have hrev := P.reverse.hasIntegerRepresentatives_of_int_val_formula (-d) (by omega) hformula
    exact (ModAP.hasIntegerRepresentatives_congr P.reverse_carrier rfl).mp hrev
  · exact P.hasIntegerRepresentatives_of_int_val_formula d hpos
      (fun i hi => P.val_affine_of_short_interval hn hsub i hi)

/-- Composing ordinary index progressions inside a genuine integer parent
preserves integer representability, over arbitrary nonzero moduli. -/
theorem NatAP.integer_representatives_transport {N : Nat} [NeZero N]
    (P R : NatAP) (hP : P.IsProper) (hR : R.IsProper)
    (hparent : P.carrier ⊆ Finset.range N)
    (hindices : R.carrier ⊆ Finset.range P.length) :
    ((section5NatTransport P R).toModAP N).HasIntegerRepresentatives :=
  (section5NatTransport P R).toModAP_hasIntegerRepresentatives
    (section5NatTransport_isProper P R hP hR)
    ((section5NatTransport_subset P R hindices).trans hparent)

end LeanProofs.GowersSzemeredi
