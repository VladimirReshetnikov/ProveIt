import GowersSzemeredi.Proofs16SingletonPartition

/-! # Recovering canonical factors from a product-box carrier

The displayed factors may have noncanonical presentations. Their carriers
agree with the actual axes of a nonempty product box, so properness and
width estimates can be taken from the original box itself.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Membership in a specified last-coordinate product. -/
theorem IsLastCoordinateBoxProduct.mem_snoc {N k : Nat} [NeZero N]
    {P : Box N (k + 1)} {Q : Box N k} {I : ModAP N}
    (h : IsLastCoordinateBoxProduct P Q I) (x : Point N k) (y : ZMod N) :
    Fin.snoc x y ∈ P.carrier ↔ x ∈ Q.carrier ∧ y ∈ I.carrier := by
  rw [h.1]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, section16Init_snoc,
    section16Last, Fin.snoc_last]

/-- For a nonempty product, the base factor's carrier is the canonical
initial-coordinate projection, regardless of formal axis lengths. -/
theorem IsLastCoordinateBoxProduct.init_carrier {N k : Nat} [NeZero N]
    {P : Box N (k + 1)} {Q : Box N k} {I : ModAP N}
    (h : IsLastCoordinateBoxProduct P Q I) (hP : P.carrier.Nonempty) :
    (boxInit P).carrier = Q.carrier := by
  classical
  obtain ⟨z, hz⟩ := hP
  have hz' : Fin.snoc (Fin.init z) (z (Fin.last k)) ∈ P.carrier := by
    simpa only [Fin.snoc_init_self] using hz
  have hp := (mem_boxInit_snoc P _ _).mp hz'
  have hq := (h.mem_snoc _ _).mp hz'
  ext x
  exact ⟨fun hx => ((h.mem_snoc _ _).mp ((mem_boxInit_snoc P _ _).mpr ⟨hx, hp.2⟩)).1,
    fun hx => ((mem_boxInit_snoc P _ _).mp ((h.mem_snoc _ _).mpr ⟨hx, hq.2⟩)).1⟩

/-- The final factor likewise agrees with the canonical final axis. -/
theorem IsLastCoordinateBoxProduct.last_carrier {N k : Nat} [NeZero N]
    {P : Box N (k + 1)} {Q : Box N k} {I : ModAP N}
    (h : IsLastCoordinateBoxProduct P Q I) (hP : P.carrier.Nonempty) :
    (P.axis (Fin.last k)).carrier = I.carrier := by
  classical
  obtain ⟨z, hz⟩ := hP
  have hz' : Fin.snoc (Fin.init z) (z (Fin.last k)) ∈ P.carrier := by
    simpa only [Fin.snoc_init_self] using hz
  have hp := (mem_boxInit_snoc P _ _).mp hz'
  have hq := (h.mem_snoc _ _).mp hz'
  ext y
  exact ⟨fun hy => ((h.mem_snoc _ _).mp ((mem_boxInit_snoc P _ _).mpr ⟨hp.1, hy⟩)).2,
    fun hy => ((mem_boxInit_snoc P _ _).mp ((h.mem_snoc _ _).mpr ⟨hq.1, hy⟩)).2⟩

/-- A positive width supplies the nonemptiness needed to recover both
canonical factors; no extra assumptions on their presentations are needed. -/
theorem IsLastCoordinateBoxProduct.canonical_factors {N k : Nat} [NeZero N]
    {P : Box N (k + 1)} {Q : Box N k} {I : ModAP N}
    (h : IsLastCoordinateBoxProduct P Q I) (hwidth : 0 < P.width) :
    (boxInit P).carrier = Q.carrier ∧ (P.axis (Fin.last k)).carrier = I.carrier := by
  have hP := P.carrier_nonempty_of_axis_pos (fun i => hwidth.trans_le (P.width_le_axis_length i))
  exact ⟨h.init_carrier hP, h.last_carrier hP⟩

end LeanProofs.GowersSzemeredi
