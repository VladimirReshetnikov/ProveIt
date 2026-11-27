import GRHArticle.ProgressionFree.IntegerPrefix
import Std.Data.TreeMap.Lemmas

/-!
# Checking a branch-and-packing certificate for a weighted cover

At a packing leaf, each listed triple spends the least remaining capacity
of its three vertices. Every cover meets the triple and therefore pays at
least that amount. Branches pay for the vertex selected from a triple.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- A certificate for a lower bound on the cost of a cover of a triple system. -/
inductive IntegerBoundaryCertificate where
  | paid
  | packing (indices : List ℕ)
  | branch (index : ℕ) (first middle last : IntegerBoundaryCertificate)

def integerBoundaryEdgeAt (table : Array IntegerPrefixTriple) (index : ℕ) : IntegerPrefixTriple :=
  table[index]?.getD ⟨0,0,0⟩

def integerBoundaryFresh (table : Array IntegerPrefixTriple) (removed : List ℕ) (index : ℕ) : Bool :=
  decide (index < table.size) &&
  !(integerBoundaryEdgeAt table index).vertices.any removed.contains

theorem integerBoundaryFresh_iff {table : Array IntegerPrefixTriple} {removed : List ℕ}
    {index : ℕ} :
    integerBoundaryFresh table removed index = true ↔
      index < table.size ∧
        ∀ n ∈ (integerBoundaryEdgeAt table index).vertices, n ∉ removed := by
  simp only [integerBoundaryFresh, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hidx, hf⟩
    refine ⟨hidx, ?_⟩
    intro x hx hrem
    have he := List.any_eq_true.mpr ⟨x,hx,List.contains_iff_mem.mpr hrem⟩
    simp [he] at hf
  · rintro ⟨hidx,hrem⟩
    refine ⟨hidx, ?_⟩
    cases ha : (integerBoundaryEdgeAt table index).vertices.any removed.contains with
    | false => rfl
    | true =>
      obtain ⟨x,hx,h⟩ := List.any_eq_true.mp ha
      exact (hrem x hx (List.contains_iff_mem.mp h)).elim

private abbrev CapacityTable := Std.TreeMap ℕ ℕ

private def available (cap : ℕ → ℕ) (used : CapacityTable) (n : ℕ) : ℕ :=
  used.getD n (cap n)

private def debit (cap : ℕ → ℕ) (used : CapacityTable) (n w : ℕ) : CapacityTable :=
  used.insert n (available cap used n - w)

private theorem available_debit (cap : ℕ → ℕ) (used : CapacityTable) (n w x : ℕ) :
    available cap (debit cap used n w) x =
      if n = x then available cap used n - w else available cap used x := by
  simp only [available, debit, Std.TreeMap.getD_insert, Nat.compare_eq_eq]

private theorem available_debit_le (cap : ℕ → ℕ) (used : CapacityTable) (n w x : ℕ) :
    available cap (debit cap used n w) x ≤ available cap used x := by
  rw [available_debit]
  split
  · next he => subst x; exact Nat.sub_le _ _
  · exact le_rfl

private def packingClaim (cap : ℕ → ℕ) (used : CapacityTable) (e : IntegerPrefixTriple) : ℕ :=
  min (available cap used e.first)
    (min (available cap used e.middle) (available cap used e.last))

private theorem packingClaim_le (cap : ℕ → ℕ) (used : CapacityTable) (e : IntegerPrefixTriple)
    {x : ℕ} (hx : x ∈ e.vertices) : packingClaim cap used e ≤ available cap used x := by
  simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private def debitTriple (cap : ℕ → ℕ) (used : CapacityTable) (e : IntegerPrefixTriple)
    (w : ℕ) : CapacityTable :=
  debit cap (debit cap (debit cap used e.first w) e.middle w) e.last w

private theorem debitTriple_le (cap : ℕ → ℕ) (used : CapacityTable)
    (e : IntegerPrefixTriple) (w x : ℕ) :
    available cap (debitTriple cap used e w) x ≤ available cap used x :=
  (available_debit_le ..).trans ((available_debit_le ..).trans (available_debit_le ..))

private theorem debitTriple_le_sub (cap : ℕ → ℕ) (used : CapacityTable)
    (e : IntegerPrefixTriple) (w : ℕ) {x : ℕ} (hx : x ∈ e.vertices) :
    available cap (debitTriple cap used e w) x ≤ available cap used x - w := by
  simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · apply (available_debit_le ..).trans ((available_debit_le ..).trans ?_)
    rw [available_debit, if_pos rfl]
  · apply (available_debit_le ..).trans
    rw [available_debit, if_pos rfl]
    exact Nat.sub_le_sub_right (available_debit_le ..) _
  · unfold debitTriple
    rw [available_debit, if_pos rfl]
    exact Nat.sub_le_sub_right ((available_debit_le ..).trans (available_debit_le ..)) _

private def inspectedPackingMass {ι : Type*} (cap : ℕ → ℕ) (resolve : ι → Option IntegerPrefixTriple) :
    CapacityTable → List ι → Option ℕ
  | _, [] => some 0
  | used, i::is =>
    match resolve i with
    | none => none
    | some e =>
      let m := packingClaim cap used e
      (inspectedPackingMass cap resolve (debitTriple cap used e m) is).map (m+·)

def IntegerBoundaryCover (table : Array IntegerPrefixTriple) (removed : List ℕ) (C : Finset ℕ) : Prop :=
  ∀ i, integerBoundaryFresh table removed i = true →
    ∃ x ∈ (integerBoundaryEdgeAt table i).vertices, x ∈ C

private theorem inspectedPackingMass_sound {ι : Type*} (cap : ℕ → ℕ)
    (resolve : ι → Option IntegerPrefixTriple) {C : Finset ℕ}
    (hc : ∀ i e, resolve i = some e → ∃ x ∈ e.vertices, x ∈ C)
    (used : CapacityTable) {is : List ι} {total : ℕ}
    (h : inspectedPackingMass cap resolve used is = some total) :
    total ≤ ∑ x ∈ C, available cap used x := by
  induction is generalizing used total with
  | nil =>
    change some 0 = some total at h
    exact (Option.some.inj h) ▸ Nat.zero_le _
  | cons i is ih =>
    cases hi : resolve i with
    | none => simp [inspectedPackingMass, hi] at h
    | some e =>
      let m := packingClaim cap used e
      let next := debitTriple cap used e m
      simp only [inspectedPackingMass, hi] at h
      change (inspectedPackingMass cap resolve next is).map (m+·) = some total at h
      cases hrest : inspectedPackingMass cap resolve next is with
      | none => simp [hrest] at h
      | some rest =>
        have heq : total = m + rest := (Option.some.inj (by simpa only [hrest, Option.map_some] using h)).symm
        have htail := ih next hrest
        obtain ⟨x,hx,hxC⟩ := hc i e hi
        have hm : m ≤ available cap used x := packingClaim_le cap used e hx
        have hpay : available cap next x + m ≤ available cap used x := by
          have hxwithdraw := debitTriple_le_sub cap used e m hx
          change available cap next x ≤ _ at hxwithdraw
          omega
        have hrestcost : (∑ z ∈ C.erase x, available cap next z) ≤
            ∑ z ∈ C.erase x, available cap used z := by
          exact sum_le_sum (fun z _ ↦ debitTriple_le cap used e m z)
        rw [heq]
        calc
          _ ≤ m + ∑ z ∈ C, available cap next z := Nat.add_le_add_left htail _
          _ = (∑ z ∈ C.erase x, available cap next z) + (available cap next x + m) := by
            rw [← sum_erase_add C (available cap next) hxC]
            omega
          _ ≤ (∑ z ∈ C.erase x, available cap used z) + available cap used x :=
            Nat.add_le_add hrestcost hpay
          _ = _ := sum_erase_add C (available cap used) hxC

private def verifiedPackingMass (cap : ℕ → ℕ) (table : Array IntegerPrefixTriple)
    (removed : List ℕ) (used : CapacityTable) (is : List ℕ) : Option ℕ :=
  inspectedPackingMass cap
    (fun i ↦ if integerBoundaryFresh table removed i then some (integerBoundaryEdgeAt table i) else none)
    used is

private theorem verifiedPackingMass_sound (cap : ℕ → ℕ) (table : Array IntegerPrefixTriple)
    (removed : List ℕ) {C : Finset ℕ} (hc : IntegerBoundaryCover table removed C)
    (used : CapacityTable) {is : List ℕ} {total : ℕ}
    (h : verifiedPackingMass cap table removed used is = some total) :
    total ≤ ∑ x ∈ C, available cap used x := by
  apply inspectedPackingMass_sound _ _ ?_ _ h
  intro i e hi
  split at hi
  · next hf => exact (Option.some.inj hi) ▸ hc i hf
  · simp at hi

private theorem integerBoundaryCover_erase {table : Array IntegerPrefixTriple}
    {removed : List ℕ} {C : Finset ℕ} (hc : IntegerBoundaryCover table removed C) (x : ℕ) :
    IntegerBoundaryCover table (x::removed) (C.erase x) := by
  intro i hi
  obtain ⟨hidx, hrem⟩ := integerBoundaryFresh_iff.mp hi
  obtain ⟨v,hv,hvC⟩ := hc i (integerBoundaryFresh_iff.mpr
    ⟨hidx, fun y hy hyr ↦ hrem y hy (List.mem_cons_of_mem _ hyr)⟩)
  refine ⟨v,hv, mem_erase.mpr ⟨?_,hvC⟩⟩
  intro h
  exact hrem v hv (h ▸ List.mem_cons_self)

def checkIntegerBoundaryCertificate (cap : ℕ → ℕ) (table : Array IntegerPrefixTriple) :
    List ℕ → ℕ → IntegerBoundaryCertificate → Bool
  | _, budget, .paid => budget == 0
  | removed, budget, .packing indices =>
      match verifiedPackingMass cap table removed ∅ indices with
      | some mass => decide (budget ≤ mass)
      | none => false
  | removed, budget, .branch index first middle last =>
      let e := integerBoundaryEdgeAt table index
      integerBoundaryFresh table removed index &&
        checkIntegerBoundaryCertificate cap table (e.first::removed) (budget-cap e.first) first &&
        checkIntegerBoundaryCertificate cap table (e.middle::removed) (budget-cap e.middle) middle &&
        checkIntegerBoundaryCertificate cap table (e.last::removed) (budget-cap e.last) last

theorem checkIntegerBoundaryCertificate_branch (cap : ℕ → ℕ) (table : Array IntegerPrefixTriple)
    (removed : List ℕ) (budget index : ℕ) (first middle last : IntegerBoundaryCertificate)
    (hx : integerBoundaryFresh table removed index = true)
    (hfirst : checkIntegerBoundaryCertificate cap table ((integerBoundaryEdgeAt table index).first::removed)
      (budget-cap (integerBoundaryEdgeAt table index).first) first = true)
    (hmiddle : checkIntegerBoundaryCertificate cap table ((integerBoundaryEdgeAt table index).middle::removed)
      (budget-cap (integerBoundaryEdgeAt table index).middle) middle = true)
    (hlast : checkIntegerBoundaryCertificate cap table ((integerBoundaryEdgeAt table index).last::removed)
      (budget-cap (integerBoundaryEdgeAt table index).last) last = true) :
    checkIntegerBoundaryCertificate cap table removed budget (.branch index first middle last) = true := by
  simp only [checkIntegerBoundaryCertificate, hx, hfirst, hmiddle, hlast, Bool.and_self]

/-- A successfully checked certificate lower-bounds the weight of any cover. -/
theorem checkIntegerBoundaryCertificate_sound {cap : ℕ → ℕ} {table : Array IntegerPrefixTriple}
    {removed : List ℕ} {budget : ℕ} {cert : IntegerBoundaryCertificate} {C : Finset ℕ}
    (h : checkIntegerBoundaryCertificate cap table removed budget cert = true)
    (hc : IntegerBoundaryCover table removed C) :
    budget ≤ ∑ x ∈ C, cap x := by
  induction cert generalizing removed budget C with
  | paid =>
    have h₀ : budget = 0 := by simpa [checkIntegerBoundaryCertificate] using h
    exact h₀ ▸ Nat.zero_le _
  | packing indices =>
    cases he : verifiedPackingMass cap table removed ∅ indices with
    | none => simp [checkIntegerBoundaryCertificate, he] at h
    | some total =>
      have hbudget : budget ≤ total := by simpa [checkIntegerBoundaryCertificate, he] using h
      have hm := verifiedPackingMass_sound cap table removed hc ∅ he
      simp only [available, Std.TreeMap.getD_emptyc] at hm
      exact hbudget.trans hm
  | branch index first middle last ihFirst ihMiddle ihLast =>
    simp only [checkIntegerBoundaryCertificate, Bool.and_eq_true, and_assoc] at h
    obtain ⟨hedge,hfirst,hmiddle,hlast⟩ := h
    obtain ⟨x,hx,hxC⟩ := hc index hedge
    have hrest := integerBoundaryCover_erase hc x
    have hcost : budget-cap x ≤ ∑ y ∈ C.erase x, cap y := by
      simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ihFirst hfirst hrest
      · exact ihMiddle hmiddle hrest
      · exact ihLast hlast hrest
    have hsum := sum_erase_add C cap hxC
    omega

def integerBoundaryDirectFresh (valid : IntegerPrefixTriple → Bool) (removed : List ℕ)
    (e : IntegerPrefixTriple) : Bool :=
  valid e && !e.vertices.any removed.contains

theorem integerBoundaryDirectFresh_iff {valid : IntegerPrefixTriple → Bool} {removed : List ℕ}
    {e : IntegerPrefixTriple} :
    integerBoundaryDirectFresh valid removed e = true ↔
      valid e = true ∧ ∀ x ∈ e.vertices, x ∉ removed := by
  simp only [integerBoundaryDirectFresh, Bool.and_eq_true]
  constructor
  · rintro ⟨he, hdis⟩
    refine ⟨he, ?_⟩
    intro x hx hrem
    have h := List.any_eq_true.mpr ⟨x, hx, List.contains_iff_mem.mpr hrem⟩
    simp [h] at hdis
  · rintro ⟨he, hrem⟩
    refine ⟨he, ?_⟩
    cases h : e.vertices.any removed.contains with
    | false => rfl
    | true =>
      obtain ⟨x,hx,hX⟩ := List.any_eq_true.mp h
      exact (hrem x hx (List.contains_iff_mem.mp hX)).elim

/-- A cover for the allowed triples that avoid previously charged vertices. -/
def IntegerBoundaryDirectCover (valid : IntegerPrefixTriple → Bool) (removed : List ℕ)
    (C : Finset ℕ) : Prop :=
  ∀ e, integerBoundaryDirectFresh valid removed e = true → ∃ x ∈ e.vertices, x ∈ C

/-- Check a greedy packing directly in terms of triples, without array lookup. -/
def checkIntegerBoundaryDirectPacking (cap : ℕ → ℕ) (valid : IntegerPrefixTriple → Bool)
    (removed : List ℕ) (budget : ℕ) (edges : List IntegerPrefixTriple) : Bool :=
  match inspectedPackingMass cap
    (fun e ↦ if integerBoundaryDirectFresh valid removed e then some e else none) ∅ edges with
  | some mass => decide (budget ≤ mass)
  | none => false

theorem checkIntegerBoundaryDirectPacking_sound {cap : ℕ → ℕ} {valid : IntegerPrefixTriple → Bool}
    {removed : List ℕ} {budget : ℕ} {edges : List IntegerPrefixTriple} {C : Finset ℕ}
    (h : checkIntegerBoundaryDirectPacking cap valid removed budget edges = true)
    (hc : IntegerBoundaryDirectCover valid removed C) :
    budget ≤ ∑ x ∈ C, cap x := by
  let resolve := fun e ↦ if integerBoundaryDirectFresh valid removed e then some e else none
  change (match inspectedPackingMass cap resolve ∅ edges with
    | some mass => decide (budget ≤ mass)
    | none => false) = true at h
  cases hp : inspectedPackingMass cap resolve ∅ edges with
  | none => simp [hp] at h
  | some mass =>
    have hm := inspectedPackingMass_sound cap resolve (C := C) (fun i e hi ↦ by
      unfold resolve at hi
      split at hi
      · next h => exact (Option.some.inj hi) ▸ hc i h
      · simp at hi) ∅ hp
    simp only [available, Std.TreeMap.getD_emptyc] at hm
    rw [hp, decide_eq_true_eq] at h
    exact h.trans hm

private theorem integerBoundaryDirectCover_erase {valid : IntegerPrefixTriple → Bool}
    {removed : List ℕ} {C : Finset ℕ} (hc : IntegerBoundaryDirectCover valid removed C) (x : ℕ) :
    IntegerBoundaryDirectCover valid (x::removed) (C.erase x) := by
  intro e he
  obtain ⟨hvalid, hrem⟩ := integerBoundaryDirectFresh_iff.mp he
  obtain ⟨v,hv,hvC⟩ := hc e (integerBoundaryDirectFresh_iff.mpr
    ⟨hvalid, fun y hy hyr ↦ hrem y hy (List.mem_cons_of_mem _ hyr)⟩)
  refine ⟨v,hv, mem_erase.mpr ⟨?_,hvC⟩⟩
  intro h
  exact hrem v hv (h ▸ List.mem_cons_self)

/-- Join bounds from the three ways of hitting the chosen triple. -/
theorem integerBoundaryDirect_branch_bound {cap : ℕ → ℕ} {valid : IntegerPrefixTriple → Bool}
    {removed : List ℕ} {budget : ℕ} {e : IntegerPrefixTriple}
    (he : integerBoundaryDirectFresh valid removed e = true)
    (hfirst : ∀ C, IntegerBoundaryDirectCover valid (e.first::removed) C →
      budget-cap e.first ≤ ∑ x ∈ C, cap x)
    (hmiddle : ∀ C, IntegerBoundaryDirectCover valid (e.middle::removed) C →
      budget-cap e.middle ≤ ∑ x ∈ C, cap x)
    (hlast : ∀ C, IntegerBoundaryDirectCover valid (e.last::removed) C →
      budget-cap e.last ≤ ∑ x ∈ C, cap x)
    (C : Finset ℕ) (hc : IntegerBoundaryDirectCover valid removed C) :
    budget ≤ ∑ x ∈ C, cap x := by
  obtain ⟨x,hx,hxC⟩ := hc e he
  have hr := integerBoundaryDirectCover_erase hc x
  have hcost : budget-cap x ≤ ∑ y ∈ C.erase x, cap y := by
    simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfirst _ hr
    · exact hmiddle _ hr
    · exact hlast _ hr
  have hsum := sum_erase_add C cap hxC
  omega

end GRHArticle.ProgressionFree
