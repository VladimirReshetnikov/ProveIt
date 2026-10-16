import BusyBeaver.ZFC.PositiveClosure
import BusyBeaver.ZFC.ProfileCongruence

/-!
Hereditary saturation for the raw subset-seeded PSC interpretation.

The definitions and purity-cut argument follow batch144 source08 of the
closure-kernel collection. Saturating the member extension of a guarded raw
hull repairs its lack of profile closure. Every set-existence resource below
names its particular instance: a constant profile-image relation, the Pure
separation cut, or one guarded PSC matrix. No theorem assumes all semantic
relations form a first-order schema. These semantic lemmas do not yet give
first-order adapters, a theory consistency calibration or a TM endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.PSCSaturation

open PositiveClosure Profile

universe u
variable {V : Type u}

/-- An extension closed under all incoming-profile copies of its members. -/
def Saturated (mem : V → V → Prop) (a : V) : Prop :=
  ∀ x y, Same mem x y → mem x a → mem y a

/-- Hereditary saturation requires only saturated members of the cover. -/
def Pure (mem : V → V → Prop) (a : V) : Prop :=
  Saturated mem a ∧ ∃ t, Transitive mem t ∧ Sub mem a t ∧
    ∀ x, mem x t → Saturated mem x

def ProfileImage (mem : V → V → Prop) (a y : V) : Prop :=
  ∃ x, mem x a ∧ Same mem x y

/-- Exact member extension; representing objects need not be unique. -/
def SatExtension (mem : V → V → Prop) (a b : V) : Prop :=
  Exact mem (ProfileImage mem a) b

def PurityCut (mem : V → V → Prop) (v c : V) : Prop :=
  Exact mem (fun x => mem x v ∧ Pure mem x) c

theorem saturated_mem_iff (mem : V → V → Prop) {a x y : V}
    (ha : Saturated mem a) (hxy : Same mem x y) : mem x a ↔ mem y a :=
  ⟨ha x y hxy, ha y x (same_symm mem hxy)⟩

theorem saturated_congr (mem : V → V → Prop) {a b : V}
    (hab : Same mem a b) : Saturated mem a ↔ Saturated mem b := by
  constructor
  · intro ha x y hxy hxb
    exact (hab y).mp (ha x y hxy ((hab x).mpr hxb))
  · intro hb x y hxy hxa
    exact (hab y).mpr (hb x y hxy ((hab x).mp hxa))

theorem pure_congr (mem : V → V → Prop) {a b : V}
    (hab : Same mem a b) : Pure mem a ↔ Pure mem b := by
  constructor
  · rintro ⟨ha, t, ht, hat, hMembers⟩
    exact ⟨(saturated_congr mem hab).mp ha, t, ht,
      fun z hzb => hat z ((hab z).mpr hzb), hMembers⟩
  · rintro ⟨hb, t, ht, hbt, hMembers⟩
    exact ⟨(saturated_congr mem hab).mpr hb, t, ht,
      fun z hza => hbt z ((hab z).mp hza), hMembers⟩

theorem pure_hereditary (mem : V → V → Prop) {a x : V}
    (ha : Pure mem a) (hxa : mem x a) : Pure mem x := by
  obtain ⟨_, t, ht, hat, hMembers⟩ := ha
  have hxt : mem x t := hat x hxa
  exact ⟨hMembers x hxt, t, ht, ht x hxt, hMembers⟩

theorem pure_empty (mem : V → V → Prop) (e : V) (he : ∀ z, ¬ mem z e) : Pure mem e := by
  refine ⟨?_, e, ?_, sub_refl mem e, ?_⟩
  · intro x y _ hxe
    exact (he x hxe).elim
  · intro x hxe
    exact (he x hxe).elim
  · intro x hxe
    exact (he x hxe).elim

theorem pure_nonempty (mem : V → V → Prop)
    (hEmpty : ∃ e, ∀ z, ¬ mem z e) : ∃ e, Pure mem e := by
  obtain ⟨e, he⟩ := hEmpty
  exact ⟨e, pure_empty mem e he⟩

/-- One transitive cover and the fixed Pure cut replace a choice of many covers. -/
theorem pure_of_saturated_members (mem : V → V → Prop) (a : V)
    (hSat : Saturated mem a) (hMembers : ∀ x, mem x a → Pure mem x)
    (hCover : ∃ v, Transitive mem v ∧ Sub mem a v)
    (hCut : ∀ v, ∃ c, PurityCut mem v c) : Pure mem a := by
  obtain ⟨v, hv, hav⟩ := hCover
  obtain ⟨c, hc⟩ := hCut v
  refine ⟨hSat, c, ?_, ?_, ?_⟩
  · intro x hxc y hyx
    obtain ⟨hxv, hxPure⟩ := (hc x).mp hxc
    exact (hc y).mpr ⟨hv x hxv y hyx, pure_hereditary mem hxPure hyx⟩
  · intro x hxa
    exact (hc x).mpr ⟨hav x hxa, hMembers x hxa⟩
  · intro x hxc
    exact ((hc x).mp hxc).2.1

theorem pure_iff_saturated_members (mem : V → V → Prop) (a : V)
    (hCover : ∃ v, Transitive mem v ∧ Sub mem a v)
    (hCut : ∀ v, ∃ c, PurityCut mem v c) :
    Pure mem a ↔ Saturated mem a ∧ ∀ x, mem x a → Pure mem x := by
  constructor
  · intro ha
    exact ⟨ha.1, fun _ hx => pure_hereditary mem ha hx⟩
  · rintro ⟨hSat, hMembers⟩
    exact pure_of_saturated_members mem a hSat hMembers hCover hCut

theorem saturation_contains (mem : V → V → Prop) {a b : V}
    (h : SatExtension mem a b) : Sub mem a b := by
  intro x hxa
  exact (h x).mpr ⟨x, hxa, same_refl mem x⟩

theorem saturation_saturated (mem : V → V → Prop) {a b : V}
    (h : SatExtension mem a b) : Saturated mem b := by
  intro x y hxy hxb
  obtain ⟨z, hza, hzx⟩ := (h x).mp hxb
  exact (h y).mpr ⟨z, hza, same_trans mem hzx hxy⟩

theorem saturation_preserves (mem : V → V → Prop) {a b : V}
    (h : SatExtension mem a b) (p : V → Prop)
    (hInvariant : ∀ x y, Same mem x y → p x → p y)
    (hMembers : ∀ x, mem x a → p x) : ∀ y, mem y b → p y := by
  intro y hyb
  obtain ⟨x, hxa, hxy⟩ := (h y).mp hyb
  exact hInvariant x y hxy (hMembers x hxa)

/-- The one constant profile-image PSC instance produces an exact saturation. -/
theorem saturation_of_instance (mem : V → V → Prop) (seed : V → V → Prop)
    (witness : V) (hSeed : ∀ a, seed a a) (a union : V)
    (hUnion : Exact mem (fun z => ∃ x, mem x a ∧ mem z x) union)
    (hInstance : ClosureInstance mem seed (fun _ y => ProfileImage mem a y)) :
    ∃ b, SatExtension mem a b := by
  apply constant_exact_of_instance mem seed witness hSeed (ProfileImage mem a)
    ⟨union, ?_⟩ hInstance
  rintro y ⟨x, hxa, hxy⟩ z hzy
  exact (hUnion z).mpr ⟨x, hxa, (hxy z).mpr hzy⟩

theorem saturation_pure (mem : V → V → Prop) {a b : V}
    (h : SatExtension mem a b) (hMembers : ∀ x, mem x a → Pure mem x)
    (hCover : ∃ v, Transitive mem v ∧ Sub mem b v)
    (hCut : ∀ v, ∃ c, PurityCut mem v c) : Pure mem b := by
  apply pure_of_saturated_members mem b (saturation_saturated mem h) ?_ hCover hCut
  exact saturation_preserves mem h (Pure mem)
    (fun _ _ hxy hx => (pure_congr mem hxy).mp hx) hMembers

theorem pure_member_congr (mem : V → V → Prop) {x x' a a' : V}
    (ha : Pure mem a) (hxx' : Same mem x x') (haa' : Same mem a a') :
    mem x a ↔ mem x' a' :=
  (saturated_mem_iff mem ha.1 hxx').trans (haa' x')

theorem pure_extensionality (mem : V → V → Prop) {a b : V}
    (ha : Pure mem a) (hb : Pure mem b)
    (hMembers : ∀ z, Pure mem z → (mem z a ↔ mem z b)) : Same mem a b := by
  intro z
  constructor
  · intro hza
    exact (hMembers z (pure_hereditary mem ha hza)).mp hza
  · intro hzb
    exact (hMembers z (pure_hereditary mem hb hzb)).mpr hzb

theorem pure_sub_iff (mem : V → V → Prop) {a : V} (ha : Pure mem a) (b : V) :
    (∀ z, Pure mem z → mem z a → mem z b) ↔ Sub mem a b := by
  exact ⟨fun h z hz => h z (pure_hereditary mem ha hz) hz, fun h z _ hz => h z hz⟩

def Guarded (mem : V → V → Prop) (r : V → V → Prop) (x y : V) : Prop :=
  Pure mem x ∧ Pure mem y ∧ r x y

def PureRelationInvariant (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∀ x x' y y', Pure mem x → Pure mem x' → Pure mem y → Pure mem y' →
    Same mem x x' → Same mem y y' → (r x y ↔ r x' y')

def PureLocalBound (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∀ x, Pure mem x → ∃ b, Pure mem b ∧ ∀ y, Pure mem y → r x y → Sub mem y b

def PureHull (mem : V → V → Prop) (r : V → V → Prop) (a c : V) : Prop :=
  Pure mem c ∧
  (∀ x y, Pure mem x → Pure mem y → (Sub mem x a ∨ mem x c) → r x y → mem y c) ∧
  (∀ y, mem y c → ∃ x, Pure mem x ∧ r x y)

theorem guarded_subset_bounded (mem : V → V → Prop) (r : V → V → Prop)
    (hBound : PureLocalBound mem r) : SubsetBounded mem (Guarded mem r) := by
  classical
  intro x
  by_cases hx : Pure mem x
  · obtain ⟨b, _, hb⟩ := hBound x hx
    exact ⟨b, fun y hy => hb y hy.2.1 hy.2.2⟩
  · exact ⟨x, fun _ hy => (hx hy.1).elim⟩

/-- Saturation repairs both recurrent closure and unrestricted global support. -/
theorem saturated_hull_transfer (mem : V → V → Prop) (r : V → V → Prop) (a c0 c : V)
    (hRaw : PositiveHull mem (Sub mem) (Guarded mem r) a c0)
    (hSat : SatExtension mem c0 c) (hInvariant : PureRelationInvariant mem r)
    (hCover : ∃ v, Transitive mem v ∧ Sub mem c v)
    (hCut : ∀ v, ∃ cut, PurityCut mem v cut) : PureHull mem r a c := by
  have hMembers : ∀ x, mem x c0 → Pure mem x := by
    intro x hx
    obtain ⟨_, _, hxPure, _⟩ := hRaw.2 x hx
    exact hxPure
  refine ⟨saturation_pure mem hSat hMembers hCover hCut, ?_, ?_⟩
  · intro x y hx hy hActive hxy
    apply saturation_contains mem hSat
    rcases hActive with hSeed | hxC
    · exact hRaw.1 x y (Or.inl hSeed) ⟨hx, hy, hxy⟩
    · obtain ⟨x0, hx0C, hx0x⟩ := (hSat x).mp hxC
      have hx0 := hMembers x0 hx0C
      have hx0y : r x0 y := (hInvariant x0 x y y hx0 hx hy hy hx0x (same_refl mem y)).mpr hxy
      exact hRaw.1 x0 y (Or.inr hx0C) ⟨hx0, hy, hx0y⟩
  · intro y hyC
    obtain ⟨y0, hy0C, hy0y⟩ := (hSat y).mp hyC
    obtain ⟨x, hx, hy0, hxy0⟩ := hRaw.2 y0 hy0C
    have hy : Pure mem y := (pure_congr mem hy0y).mp hy0
    exact ⟨x, hx, (hInvariant x x y0 y hx hx hy0 hy (same_refl mem x) hy0y).mp hxy0⟩

/-- A single guarded matrix instance transfers once its named saturation resources are supplied. -/
theorem pure_hull_of_instance (mem : V → V → Prop) (r : V → V → Prop)
    (hBound : PureLocalBound mem r) (hInvariant : PureRelationInvariant mem r)
    (hInstance : ClosureInstance mem (Sub mem) (Guarded mem r))
    (hSaturate : ∀ c0, ∃ c, SatExtension mem c0 c)
    (hCovers : ∀ c, ∃ v, Transitive mem v ∧ Sub mem c v)
    (hCut : ∀ v, ∃ cut, PurityCut mem v cut) (a : V) :
    ∃ c, PureHull mem r a c := by
  obtain ⟨c0, hRaw⟩ := hInstance (guarded_subset_bounded mem r hBound) a
  obtain ⟨c, hSat⟩ := hSaturate c0
  exact ⟨c, saturated_hull_transfer mem r a c0 c hRaw hSat hInvariant (hCovers c) hCut⟩

#print axioms pure_congr
#print axioms pure_hereditary
#print axioms pure_of_saturated_members
#print axioms saturation_of_instance
#print axioms saturated_hull_transfer
#print axioms pure_hull_of_instance

end SetTheory.BusyBeaver.ZFC.PSCSaturation
