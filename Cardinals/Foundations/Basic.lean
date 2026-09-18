/-
  Set-theoretic framework for the synthesis, inside Mathlib's model `ZFSet` of ZFC.

  * rank-initial segments `V_ α`, sets of ordinals, cofinal subsets;
  * satisfaction for the set structures `(A, ∈)` using ProveIt's first-order
    syntax `SetTheory.Form` / `SetTheory.Sat` (language `{∈, =}`);
  * ordinal definability from a class of parameters, `ODfrom`;
  * complete ultrafilters on ordinals and Goldberg's classes `CD η`, `HCD η`;
  * elementary hulls `σ ≺ V_ α`, clubs and stationary sets in `P_κ(A)`;
  * inner models of ZF / ZFC (via ProveIt's axiomatization `ZFax`, `ZFCax`).

  There are no admitted statements in this file.
-/
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Tactic
import ZF.Zf
import BoundedZFCConsistency.Choice

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

/-! ### Sets of ordinals -/

/-- The von Neumann ordinal, as a `ZFSet`. -/
noncomputable abbrev ordZ (o : Ordinal.{u}) : ZFSet.{u} := o.toZFSet

/-- `a` is a set of ordinals below `lam`. -/
def SubOrd (a : ZFSet.{u}) (lam : Ordinal.{u}) : Prop :=
  ∀ x ∈ a, ∃ ξ < lam, x = ordZ ξ

/-- `a` is a cofinal set of ordinals below `lam`. -/
def CofinalIn (a : ZFSet.{u}) (lam : Ordinal.{u}) : Prop :=
  SubOrd a lam ∧ ∀ ξ < lam, ∃ η, ξ ≤ η ∧ η < lam ∧ ordZ η ∈ a

/-- `a` is a *short* cofinal subset of `lam`: cofinal, of cardinality below `|lam|`.
For a cardinal `lam` this is equivalent to `ot(a) < lam`. -/
def ShortCofinal (a : ZFSet.{u}) (lam : Ordinal.{u}) : Prop :=
  CofinalIn a lam ∧ ZFSet.card a < lam.card

theorem subOrd_iff_subset {a : ZFSet.{u}} {lam : Ordinal.{u}} :
    SubOrd a lam ↔ a ⊆ ordZ lam := by
  constructor
  · intro h x hx
    obtain ⟨ξ, hξ, rfl⟩ := h x hx
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hξ
  · intro h x hx
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (h hx)
    exact ⟨ξ, hξ, rfl⟩

/-! ### Satisfaction in set structures -/

/-- The carrier of the set structure `(A, ∈)`. -/
abbrev Carrier (A : ZFSet.{u}) : Type (u + 1) := {x : ZFSet.{u} // x ∈ A}

/-- Membership on the carrier of `A`. -/
def memOn (A : ZFSet.{u}) : Carrier A → Carrier A → Prop := fun x y => x.1 ∈ y.1

/-- `σ` is (the universe of) an elementary substructure of `(A, ∈)`. -/
def ElemSub (σ A : ZFSet.{u}) : Prop :=
  ∃ h : σ ⊆ A, ∀ (φ : Form) (e : ℕ → Carrier σ),
    Sat (memOn σ) e φ ↔ Sat (memOn A) (fun n => ⟨(e n).1, h (e n).2⟩) φ

/-! ### Ordinal definability -/

/-- The environment determined by a finite list of parameters (padded by `d`). -/
def envOf {A : ZFSet.{u}} (d : Carrier A) (ps : List (Carrier A)) : ℕ → Carrier A :=
  fun n => ps.getD n d

/-- `x` is definable over `(V_ θ, ∈)` by a formula whose parameters are ordinals
or satisfy `P`. -/
def DefinableIn (θ : Ordinal.{u}) (P : ZFSet.{u} → Prop) (x : ZFSet.{u}) : Prop :=
  ∃ (φ : Form) (d : Carrier (V_ θ)) (ps : List (Carrier (V_ θ))) (hx : x ∈ V_ θ),
    IsOrdinal d.1 ∧ (∀ p ∈ ps, IsOrdinal p.1 ∨ P p.1) ∧
    ∀ y : Carrier (V_ θ), Sat (memOn (V_ θ)) (scons y (envOf d ps)) φ ↔ y = ⟨x, hx⟩

/-- `x` is ordinal definable from parameters in the class `P`
(definable over some rank `V_ θ`; by reflection this is the usual notion). -/
def ODfrom (P : ZFSet.{u} → Prop) (x : ZFSet.{u}) : Prop := ∃ θ, DefinableIn θ P x

theorem ODfrom.mono {P Q : ZFSet.{u} → Prop} (h : ∀ p, P p → Q p) {x : ZFSet.{u}}
    (hx : ODfrom P x) : ODfrom Q x := by
  obtain ⟨θ, φ, d, ps, hxθ, hd, hps, hdef⟩ := hx
  exact ⟨θ, φ, d, ps, hxθ, hd, fun p hp => (hps p hp).imp id (h p.1), hdef⟩

/-- Every ordinal is ordinal definable (from no parameters at all). -/
theorem ODfrom_ordinal (P : ZFSet.{u} → Prop) (ξ : Ordinal.{u}) : ODfrom P (ordZ ξ) := by
  have hmem : ordZ ξ ∈ V_ (ξ + 1) := by
    rw [mem_vonNeumann, rank_toZFSet]; exact Order.lt_add_one_iff.mpr le_rfl
  refine ⟨ξ + 1, fEq 0 1, ⟨ordZ ξ, hmem⟩, [⟨ordZ ξ, hmem⟩], hmem, isOrdinal_toZFSet ξ, ?_, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Or.inl (isOrdinal_toZFSet ξ)
  · intro y
    simp [Sat, scons, envOf]

/-! ### Complete ultrafilters on ordinals and Goldberg's classes -/

/-- `U` is an ultrafilter on the ordinal `τ` (as a set of subsets of `τ`). -/
structure IsUltrafilterOn (τ : Ordinal.{u}) (U : ZFSet.{u}) : Prop where
  sub : U ⊆ powerset (ordZ τ)
  univ_mem : ordZ τ ∈ U
  empty_notMem : ∅ ∉ U
  upward : ∀ A ∈ U, ∀ B, B ⊆ ordZ τ → A ⊆ B → B ∈ U
  inter : ∀ A ∈ U, ∀ B ∈ U, A ∩ B ∈ U
  ultra : ∀ A, A ⊆ ordZ τ → A ∈ U ∨ (ordZ τ \ A) ∈ U

/-- `U` is an `η`-complete ultrafilter on some ordinal: closed under intersections
of fewer than `η` of its members. -/
def IsCompleteUF (η : Cardinal.{u}) (U : ZFSet.{u}) : Prop :=
  ∃ τ, IsUltrafilterOn τ U ∧
    ∀ S : ZFSet.{u}, S ⊆ U → S.Nonempty → ZFSet.card S < η → ⋂₀ S ∈ U

/-- Goldberg's class `CD(η)`: ordinal definable from `η`-complete ultrafilters on
ordinals. -/
def CD (η : Cardinal.{u}) (x : ZFSet.{u}) : Prop := ODfrom (IsCompleteUF η) x

/-- Goldberg's class `HCD(η)`: hereditarily in `CD(η)`. -/
def HCD (η : Cardinal.{u}) (x : ZFSet.{u}) : Prop :=
  ∃ t : ZFSet.{u}, IsTransitive t ∧ x ∈ t ∧ ∀ y ∈ t, CD η y

theorem IsCompleteUF.mono {η ξ : Cardinal.{u}} (h : η ≤ ξ) {U : ZFSet.{u}}
    (hU : IsCompleteUF ξ U) : IsCompleteUF η U := by
  obtain ⟨τ, hτ, hc⟩ := hU
  exact ⟨τ, hτ, fun S hS hne hcard => hc S hS hne (hcard.trans_le h)⟩

/-- The hierarchy is decreasing: higher completeness allows fewer parameters. -/
theorem CD.mono {η ξ : Cardinal.{u}} (h : η ≤ ξ) {x : ZFSet.{u}} (hx : CD ξ x) : CD η x :=
  ODfrom.mono (fun _ hp => hp.mono h) hx

theorem HCD.mono {η ξ : Cardinal.{u}} (h : η ≤ ξ) {x : ZFSet.{u}} (hx : HCD ξ x) : HCD η x := by
  obtain ⟨t, ht, hxt, hall⟩ := hx
  exact ⟨t, ht, hxt, fun y hy => (hall y hy).mono h⟩

theorem HCD.cd {η : Cardinal.{u}} {x : ZFSet.{u}} (hx : HCD η x) : CD η x := by
  obtain ⟨t, -, hxt, hall⟩ := hx
  exact hall x hxt

/-- For a set of ordinals, membership in `CD(η)` already gives membership in
`HCD(η)` (synthesis, Definition 2.3). -/
theorem HCD_of_CD_of_subOrd {η : Cardinal.{u}} {a : ZFSet.{u}} {lam : Ordinal.{u}}
    (ha : SubOrd a lam) (hcd : CD η a) : HCD η a := by
  refine ⟨insert a (ordZ lam), ?_, mem_insert a _, ?_⟩
  · intro y hy z hz
    rw [mem_insert_iff] at hy ⊢
    right
    rcases hy with rfl | hy
    · exact subOrd_iff_subset.mp ha hz
    · exact (isOrdinal_toZFSet lam).isTransitive.subset_of_mem hy hz
  · intro y hy
    rw [mem_insert_iff] at hy
    rcases hy with rfl | hy
    · exact hcd
    · obtain ⟨ξ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      exact ODfrom_ordinal _ ξ

/-! ### Clubs and stationary sets in `P_κ(A)` -/

/-- `P_κ(A)`: subsets of `A` of cardinality below `κ`. -/
def PkA (κ : Cardinal.{u}) (A : ZFSet.{u}) : Set ZFSet.{u} :=
  {σ | σ ⊆ A ∧ ZFSet.card σ < κ}

/-- `C ⊆ P_κ(A)` is club: unbounded, and closed under unions of `⊆`-chains of
length below `κ`. -/
structure IsClubPkA (κ : Cardinal.{u}) (A : ZFSet.{u}) (C : Set ZFSet.{u}) : Prop where
  sub : C ⊆ PkA κ A
  unbounded : ∀ σ ∈ PkA κ A, ∃ τ ∈ C, σ ⊆ τ
  closed : ∀ D : ZFSet.{u}, D.Nonempty → (∀ σ ∈ D, σ ∈ C) →
    (∀ σ ∈ D, ∀ τ ∈ D, σ ⊆ τ ∨ τ ⊆ σ) → ZFSet.card D < κ → ⋃₀ D ∈ C

/-- `S ⊆ P_κ(A)` is stationary: it meets every club. -/
def IsStationaryPkA (κ : Cardinal.{u}) (A : ZFSet.{u}) (S : Set ZFSet.{u}) : Prop :=
  ∀ C, IsClubPkA κ A C → ∃ σ, σ ∈ C ∧ σ ∈ S

/-! ### Inner models -/

/-- Membership on a class. -/
def memCls (N : ZFSet.{u} → Prop) : {x // N x} → {x // N x} → Prop := fun x y => x.1 ∈ y.1

/-- `N` is an inner model of ZF: a transitive class containing the ordinals and
satisfying every axiom of ZF (ProveIt's `SetTheory.ZFax`). -/
structure IsInnerModelZF (N : ZFSet.{u} → Prop) : Prop where
  trans : ∀ x, N x → ∀ y ∈ x, N y
  ords : ∀ ξ : Ordinal.{u}, N (ordZ ξ)
  zf : ∀ φ, SetTheory.ZFax φ → ∀ e : ℕ → {x // N x}, Sat (memCls N) e φ

/-- `N` is an inner model of ZFC. -/
structure IsInnerModelZFC (N : ZFSet.{u} → Prop) : Prop extends IsInnerModelZF N where
  choice : ∀ e : ℕ → {x // N x},
    Sat (memCls N) e LeanProofs.BoundedZFCConsistency.Choice_form

/-- `lam` is regular in the class `N`, in the set form used throughout: `N` has no
short cofinal subset of `lam`.  (For an inner model of ZF this is equivalent to the
non-existence in `N` of a cofinal map from a smaller ordinal.) -/
def RegularIn (N : ZFSet.{u} → Prop) (lam : Ordinal.{u}) : Prop :=
  ∀ a, N a → ¬ ShortCofinal a lam

/-- An inner model of ZF is closed under intersecting a set with an ordinal. -/
theorem IsInnerModelZF.inter_ord {N : ZFSet.{u} → Prop} (hN : IsInnerModelZF N)
    {b : ZFSet.{u}} (hb : N b) (lam : Ordinal.{u}) : N (b ∩ ordZ lam) := by
  have hsep := SetTheory.bridge_Sep_fwd (mem := memCls N)
    (fun φ e => hN.zf _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, rfl⟩))))))) e)
  obtain ⟨s, hs⟩ := hsep (fMem 0 1) (fun _ => ⟨ordZ lam, hN.ords lam⟩) ⟨b, hb⟩
  have : s.1 = b ∩ ordZ lam := by
    ext x
    rw [mem_inter]
    constructor
    · intro hx
      have := (hs ⟨x, hN.trans _ s.2 x hx⟩).mp hx
      exact ⟨this.1, this.2⟩
    · rintro ⟨hxb, hxl⟩
      exact (hs ⟨x, hN.trans _ hb x hxb⟩).mpr ⟨hxb, hxl⟩
  exact this ▸ s.2

end Cardinals
