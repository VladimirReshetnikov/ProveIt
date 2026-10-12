import GowersSzemeredi.Proofs05ShortIntegerRepresentatives

/-! Genuine integer representatives for Section 16 boxes. In addition to
axis injectivity, all axes must be represented by ordinary progressions
with one positive integer common difference. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Integer representatives of all box axes, with one shared positive
integer difference. The shared orientation may be reversed. -/
def Box.HasIntegerRepresentatives {N k : Nat} (P : Box N k) : Prop :=
  ∃ d : Nat, 0 < d ∧
    ((d : ZMod N) = P.commonDiff ∨ (d : ZMod N) = -P.commonDiff) ∧
    ∃ Q : Fin k → NatAP, ∀ i,
      (Q i).IsProper ∧ (Q i).step = d ∧ (Q i).length = (P.axis i).length ∧
      (Q i).carrier ⊆ Finset.range N ∧
      (Q i).carrier.image (fun x : Nat => (x : ZMod N)) = (P.axis i).carrier

theorem Box.HasIntegerRepresentatives.axis {N k : Nat} {P : Box N k}
    (hP : P.HasIntegerRepresentatives) (i : Fin k) :
    (P.axis i).HasIntegerRepresentatives := by
  obtain ⟨d, hd, hcast, Q, hQ⟩ := hP
  exact ⟨Q i, (hQ i).1, (hQ i).2.2.1, (hQ i).2.2.2.1, (hQ i).2.2.2.2⟩

theorem Box.HasIntegerRepresentatives.isProper {N k : Nat} [NeZero N]
    {P : Box N k} (hP : P.HasIntegerRepresentatives) : P.IsProper :=
  fun i => (hP.axis i).isProper

/-- Reverse every axis simultaneously, retaining a single common step. -/
def Box.reverse {N k : Nat} (P : Box N k) : Box N k :=
  ⟨fun i => (P.axis i).reverse, -P.commonDiff,
    fun i => congrArg Neg.neg (P.axis_step i)⟩

theorem Box.reverse_carrier {N k : Nat} [NeZero N] (P : Box N k) :
    P.reverse.carrier = P.carrier := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    Box.reverse, ModAP.reverse_carrier]

theorem Box.reverse_width {N k : Nat} (P : Box N k) : P.reverse.width = P.width := by
  simp only [Box.width, Box.reverse, ModAP.reverse]

theorem Box.hasIntegerRepresentatives_of_reverse {N k : Nat} (P : Box N k)
    (hP : P.reverse.HasIntegerRepresentatives) : P.HasIntegerRepresentatives := by
  obtain ⟨d, hd, hcast, Q, hQ⟩ := hP
  refine ⟨d, hd, ?_, Q, fun i => ?_⟩
  · rcases hcast with h | h
    · exact Or.inr h
    · exact Or.inl (by simpa only [Box.reverse, neg_neg] using h)
  · exact ⟨(hQ i).1, (hQ i).2.1, (hQ i).2.2.1, (hQ i).2.2.2.1,
      (hQ i).2.2.2.2.trans (P.axis i).reverse_carrier⟩

/-- Casting a genuine integer box with a shared positive difference gives
a box meeting the stronger geometric predicate. -/
theorem Box.hasIntegerRepresentatives_of_nat_axes {N k : Nat} [NeZero N]
    (P : Box N k) (Q : Fin k → NatAP) (d : Nat) (hd : 0 < d)
    (hstep : ∀ i, (Q i).step = d) (hcommon : (d : ZMod N) = P.commonDiff)
    (haxis : ∀ i, (Q i).toModAP N = P.axis i)
    (hbound : ∀ i j, j < (Q i).length → (Q i).start + j * d < N) :
    P.HasIntegerRepresentatives := by
  refine ⟨d, hd, Or.inl hcommon, Q, fun i => ?_⟩
  have hproper : (Q i).IsProper := by
    refine ⟨by simpa only [hstep i] using hd, ?_⟩
    classical
    unfold NatAP.carrier
    rw [Finset.card_image_of_injective]
    · simp
    · intro j l hjl
      apply Fin.ext
      exact Nat.mul_right_cancel (by simpa only [hstep i] using hd)
        (Nat.add_left_cancel hjl)
  refine ⟨hproper, hstep i, ?_, ?_, ?_⟩
  · exact congrArg ModAP.length (haxis i)
  · intro x hx
    classical
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [hstep i]
    exact Finset.mem_range.mpr (hbound i j.val j.isLt)
  · rw [← haxis i, NatAP.toModAP_carrier]

/-- A box whose representative sequences have one positive integer slope
has a genuine common-difference integer representation. -/
theorem Box.hasIntegerRepresentatives_of_int_val_formula {N k : Nat} [NeZero N]
    (P : Box N k) (d : Int) (hd : 0 < d) (hcommon : (d : ZMod N) = P.commonDiff)
    (hformula : ∀ i j, j < (P.axis i).length →
      (((P.axis i).start + (j : ZMod N) * (P.axis i).step).val : Int) =
        (P.axis i).start.val + (j : Int) * d) : P.HasIntegerRepresentatives := by
  let Q : Fin k → NatAP := fun i => ⟨(P.axis i).start.val, d.toNat, (P.axis i).length⟩
  have hInt : (d.toNat : Int) = d := Int.toNat_of_nonneg hd.le
  have hNat : 0 < d.toNat := by omega
  have hcast : (d.toNat : ZMod N) = P.commonDiff := by
    calc
      (d.toNat : ZMod N) = ((d.toNat : Int) : ZMod N) := (Int.cast_natCast d.toNat).symm
      _ = (d : ZMod N) := congrArg (fun z : Int => (z : ZMod N)) hInt
      _ = P.commonDiff := hcommon
  apply P.hasIntegerRepresentatives_of_nat_axes Q d.toNat hNat (fun _ => rfl) hcast
  · intro i
    change (⟨((P.axis i).start.val : ZMod N), (d.toNat : ZMod N),
      (P.axis i).length⟩ : ModAP N) = P.axis i
    rw [ZMod.natCast_zmod_val, hcast, ← P.axis_step i] <;> cases P.axis i <;> rfl
  · intro i j hj
    have h := hformula i j hj
    rw [← hInt] at h
    have hval : ((P.axis i).start + (j : ZMod N) * (P.axis i).step).val =
        (P.axis i).start.val + j * d.toNat := by exact_mod_cast h
    change (P.axis i).start.val + j * d.toNat < N
    rw [← hval]
    exact ZMod.val_lt _

/-- Containment of every axis in an initial interval of length at most
half the modulus suffices for genuine integer box geometry. All axes use
the same centered step and the same orientation. Injectivity need not be
assumed separately: the nonzero step and short interval imply it. -/
theorem Box.hasIntegerRepresentatives_of_short_interval {N n k : Nat} [NeZero N]
    (P : Box N k) (hn : 2 * n ≤ N) (hd : P.commonDiff ≠ 0)
    (hsub : ∀ i, (P.axis i).carrier ⊆ (modInterval N 0 n).carrier) :
    P.HasIntegerRepresentatives := by
  let d := P.commonDiff.valMinAbs
  have hcast : (d : ZMod N) = P.commonDiff := ZMod.coe_valMinAbs _
  have hdne : d ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hcast
    exact hd hcast.symm
  have hformula (i : Fin k) (j : Nat) (hj : j < (P.axis i).length) :
      (((P.axis i).start + (j : ZMod N) * (P.axis i).step).val : Int) =
        (P.axis i).start.val + (j : Int) * d := by
    simpa only [P.axis_step] using
      (P.axis i).val_affine_of_short_interval hn (hsub i) j hj
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · have hrev : P.reverse.HasIntegerRepresentatives := by
      apply P.reverse.hasIntegerRepresentatives_of_int_val_formula (-d) (by omega)
      · simp only [Int.cast_neg, hcast, Box.reverse]
      · intro i
        exact (P.axis i).reverse_int_val_formula d (hformula i)
    exact P.hasIntegerRepresentatives_of_reverse hrev
  · exact P.hasIntegerRepresentatives_of_int_val_formula d hpos hcast hformula

/-- The coordinate index model of any proper box is a genuine integer
box. This preserves all axis lengths and the exact width. -/
theorem boxIndexModel_hasIntegerRepresentatives {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) : (boxIndexModel P).HasIntegerRepresentatives := by
  let Q : Fin k → NatAP := fun i => ⟨0, 1, (P.axis i).length⟩
  apply Box.hasIntegerRepresentatives_of_nat_axes (boxIndexModel P) Q 1 (by omega)
  · intro i; rfl
  · simp only [boxIndexModel, Nat.cast_one]
  · intro i
    simp only [Q, NatAP.toModAP, boxIndexModel, modInterval, Nat.cast_zero, Nat.cast_one]
  · intro i j hj
    have hlen : (P.axis i).length ≤ N := by
      rw [← hP i]
      simpa only [ZMod.card] using (P.axis i).carrier.card_le_univ
    simpa only [Q, zero_add, mul_one] using hj.trans_le hlen

/-- Casting commutes with composition of genuine integer progressions. -/
theorem NatAP.toModAP_natTransport (N : Nat) (P R : NatAP) :
    (section5NatTransport P R).toModAP N = modAPAffine (P.toModAP N) (R.toModAP N) := by
  simp [section5NatTransport, section5NatIndexPoint, NatAP.toModAP, modAPAffine, mul_comm]

/-- Affine transport of an integer box through integer index progressions
inside each parent axis produces another genuine integer box. This keeps
the full common-difference requirement and works over composite moduli. -/
theorem Box.integer_representatives_affine_transport {N k : Nat} [NeZero N]
    (P R : Box N k) (Q T : Fin k → NatAP) (d e : Nat)
    (hd : 0 < d) (he : 0 < e)
    (hQ : ∀ i, (Q i).IsProper) (hT : ∀ i, (T i).IsProper)
    (hQstep : ∀ i, (Q i).step = d) (hTstep : ∀ i, (T i).step = e)
    (hPcommon : (d : ZMod N) = P.commonDiff) (hRcommon : (e : ZMod N) = R.commonDiff)
    (hPaxis : ∀ i, (Q i).toModAP N = P.axis i)
    (hRaxis : ∀ i, (T i).toModAP N = R.axis i)
    (hparent : ∀ i, (Q i).carrier ⊆ Finset.range N)
    (hindices : ∀ i, (T i).carrier ⊆ Finset.range (Q i).length) :
    (boxAffineTransport P R).HasIntegerRepresentatives := by
  let U : Fin k → NatAP := fun i => section5NatTransport (Q i) (T i)
  refine ⟨d * e, Nat.mul_pos hd he, Or.inl ?_, U, fun i => ?_⟩
  · simp only [Nat.cast_mul, hPcommon, hRcommon, boxAffineTransport]
  · refine ⟨section5NatTransport_isProper (Q i) (T i) (hQ i) (hT i), ?_, ?_, ?_, ?_⟩
    · simp only [U, section5NatTransport, hQstep, hTstep, Nat.mul_comm]
    · exact congrArg ModAP.length (hRaxis i)
    · exact (section5NatTransport_subset (Q i) (T i) (hindices i)).trans (hparent i)
    · change (U i).carrier.image (fun x : Nat => (x : ZMod N)) =
        (modAPAffine (P.axis i) (R.axis i)).carrier
      rw [← NatAP.toModAP_carrier, NatAP.toModAP_natTransport, hPaxis i, hRaxis i]

/-- A proper one-dimensional modular box whose canonical representative
axis is not an integer progression. -/
def wrappingOneDimensionalBox : Box 7 1 :=
  ⟨fun _ => wrappingThreeTermAP, 1, fun _ => rfl⟩

theorem wrappingOneDimensionalBox_isProper : wrappingOneDimensionalBox.IsProper :=
  fun _ => wrappingThreeTermAP_isProper

theorem wrappingOneDimensionalBox_noIntegerRepresentatives :
    ¬ wrappingOneDimensionalBox.HasIntegerRepresentatives := by
  intro h
  exact wrappingThreeTermAP_noIntegerRepresentatives (h.axis 0)

end LeanProofs.GowersSzemeredi
