import BusyBeaver.ZFC.ZFRank

set_option autoImplicit false

/-!
Finite-resource Collection argument. The relation R is arbitrary;
no Separation/Replacement instance about R is inherited from the pure ZF bundle.
The three such resources are explicit fields below. The total least-rank graph
uses the empty ordinal for inputs without outputs, avoiding domain Separation
and partial-image carving. The ordinary relation remains arbitrary.
-/
namespace LeanProofs.ZFCinPA.CollectionResources254
open _root_.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC
open InternalOrd InternalRank ZFRank
universe u
variable {V : Type u} {mem : V → V → Prop}

/-- A witness whose rank is bounded by an internal ordinal. -/
def WitnessRank (H : ZFAxioms mem) (R : V → V → Prop) (x c : V) : Prop :=
  ∃ S y, IsV H c S ∧ mem y S ∧ R x y

/-- The least ordinal bounding some output for x. -/
def LeastRank (H : ZFAxioms mem) (R : V → V → Prop) (x c : V) : Prop :=
  Ord mem c ∧ WitnessRank H R x c ∧
    ∀ e, Ord mem e → WitnessRank H R x e → c = e ∨ mem c e

def Empty (mem : V → V → Prop) (c : V) : Prop := ∀ z, ¬mem z c

/-- A genuinely total graph: no-output inputs map to the unique empty ordinal. -/
def TotalRank (H : ZFAxioms mem) (R : V → V → Prop) (x c : V) : Prop :=
  LeastRank H R x c ∨ ((¬∃ y, R x y) ∧ Empty mem c)

/-- Exactly three relation-dependent resources, with Foundation's globally
    total Replacement convention. Pure ZF resources still come from H. -/
structure Resources (H : ZFAxioms mem) (R : V → V → Prop) : Prop where
  witnessSep : ∀ x a, ∃ s, ∀ c,
    mem c s ↔ mem c a ∧ WitnessRank H R x c
  rankReplacement : (∀ x, ∃ c, TotalRank H R x c ∧ ∀ d, TotalRank H R x d → d=c) →
    ∀ a, ∃ image, ∀ c, mem c image ↔ ∃ x, mem x a ∧ TotalRank H R x c
  outputSep : ∀ a bound, ∃ b, ∀ y,
    mem y b ↔ mem y bound ∧ ∃ x, mem x a ∧ R x y

private theorem empty_eq (H : ZFAxioms mem) {c : V} (hc : Empty mem c) :
    c = vempty H :=
  H.ext c (vempty H) (fun z => ⟨fun hz => (hc z hz).elim,
    fun hz => (vempty_spec H z hz).elim⟩)

private theorem empty_ord (H : ZFAxioms mem) : Ord mem (vempty H) :=
  ⟨fun x hx => (vempty_spec H x hx).elim,
    fun x hx => (vempty_spec H x hx).elim⟩

/-- Least-rank selection uses ONLY the explicit witness Separation resource,
    Regularity, and pure ordinal comparison. -/
theorem leastRank_exists (H : ZFAxioms mem) (hR : Regular mem)
    (R : V → V → Prop) (hSep : ∀ x a, ∃ s, ∀ c,
      mem c s ↔ mem c a ∧ WitnessRank H R x c)
    {x a : V} (ha : Ord mem a) (hWa : WitnessRank H R x a) :
    ∃ c, LeastRank H R x c := by
  obtain ⟨s, hs⟩ := hSep x (vsucc H a)
  obtain ⟨c, hc, hmin⟩ := hR s
    ⟨a, (hs a).2 ⟨vsucc_self H a, hWa⟩⟩
  obtain ⟨hcA, hWc⟩ := (hs c).1 hc
  have hoc : Ord mem c := by
    rcases (vsucc_spec H a c).1 hcA with h | rfl
    · exact ord_of_mem ha h
    · exact ha
  refine ⟨c, hoc, hWc, fun e hoe hWe => ?_⟩
  rcases trichotomy H hR c hoc e hoe with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact (hmin ⟨e, h, (hs e).2
      ⟨(ord_succ H ha).1 c hcA e h, hWe⟩⟩).elim

/-- Totality and functionality are proved, not supplied as an extra Collection
    assumption. No relation-dependent schema is used except witnessSep. -/
theorem totalRank_total (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (R : V → V → Prop) (hSep : ∀ x a, ∃ s, ∀ c,
      mem c s ↔ mem c a ∧ WitnessRank H R x c) :
    ∀ x, ∃ c, TotalRank H R x c ∧ ∀ d, TotalRank H R x d → d=c := by
  classical
  intro x
  by_cases hxy : ∃ y, R x y
  · obtain ⟨y, hy⟩ := hxy
    obtain ⟨a, S, ha, hS, hyS⟩ := ranked H hR hP y
    obtain ⟨c, hc⟩ := leastRank_exists H hR R hSep ha ⟨S, y, hS, hyS, hy⟩
    refine ⟨c, Or.inl hc, fun d hd => ?_⟩
    rcases hd with hd | hd
    · exact least_unique H hR hd.1 hc.1 hd.2.2 hc.2.2 hd.2.1 hc.2.1
    · exact (hd.1 ⟨y, hy⟩).elim
  · refine ⟨vempty H, Or.inr ⟨hxy, vempty_spec H⟩, fun d hd => ?_⟩
    rcases hd with hd | hd
    · obtain ⟨S, y, -, -, hy⟩ := hd.2.1
      exact (hxy ⟨y, hy⟩).elim
    · exact empty_eq H hd.2

theorem totalRank_ordinal (H : ZFAxioms mem) (R : V → V → Prop)
    {x c : V} (hc : TotalRank H R x c) : Ord mem c := by
  rcases hc with hc | hc
  · exact hc.1
  · rw [empty_eq H hc.2]
    exact empty_ord H

/-- Strong image Collection for arbitrary R, from the three explicit finite
    resources. In particular there is no hidden arbitrary-R Separation call. -/
theorem collection (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (R : V → V → Prop) (h : Resources H R) (a : V) :
    ∃ b, (∀ y, mem y b → ∃ x, R x y) ∧
      ∀ x, mem x a → (∃ y, R x y) → ∃ y, mem y b ∧ R x y := by
  have ht := totalRank_total H hR hP R h.witnessSep
  obtain ⟨A, hA⟩ := h.rankReplacement ht a
  have hAO : ∀ c, mem c A → Ord mem c := by
    intro c hc
    obtain ⟨x, -, hT⟩ := (hA c).1 hc
    exact totalRank_ordinal H R hT
  have hβ := ord_vunion H hAO
  obtain ⟨Sβ, hSβ⟩ := isV_exists H hR hP hβ
  obtain ⟨b, hb⟩ := h.outputSep a Sβ
  refine ⟨b, fun y hy => ?_, fun x hx hxy => ?_⟩
  · obtain ⟨-, x, -, hRxy⟩ := (hb y).1 hy
    exact ⟨x, hRxy⟩
  · obtain ⟨c, hc, -⟩ := ht x
    have hL : LeastRank H R x c := hc.elim id (fun h => (h.1 hxy).elim)
    have hcA : mem c A := (hA c).2 ⟨x, hx, hc⟩
    obtain ⟨S, y, hS, hyS, hRxy⟩ := hL.2.1
    have hle := le_of_sub H hR hL.1 hβ
      (fun w hw => (vunion_spec H A w).2 ⟨c, hw, hcA⟩)
    exact ⟨y, (hb y).2
      ⟨isV_le H hR hP hβ hle hS hSβ y hyS, x, hx, hRxy⟩, hRxy⟩
end LeanProofs.ZFCinPA.CollectionResources254
