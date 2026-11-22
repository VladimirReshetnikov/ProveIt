import ConciseIPRA.PR
import Mathlib.Data.Finset.Card

/-! Imported from the packet `foundations/ipra_finite_presentations_2026-11-20`, `lean/CyclicReplay.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Finite positive rules with external assumptions. Every compiled conclusion below is
an actual sequent of ordinary iPRA. The height and rule table in this file are parameters
of the proof generator. Numerical uniformity for reflected labels is addressed in the paper. -/

namespace LeanProofs.IPRA.Foundations.ScopedReplay
open LeanProofs.ConciseIPRA
open scoped Fm

structure Rule where
  head : Nat
  needs : List Nat
  ports : List Nat
  deriving DecidableEq, Repr

abbrev Table := List Rule

/-- Positive rule firing. An empty premise list passes the membership test. -/
def enabled (available seen : List Nat) (r : Rule) : Bool :=
  r.ports.all (fun p => available.contains p) && r.needs.all (fun x => seen.contains x)

def round (rules : Table) (available seen : List Nat) : List Nat :=
  seen ++ (rules.filter (enabled available seen)).map Rule.head

/-- Rows may contain duplicates. Only membership has mathematical significance. -/
def stage (rules : Table) (available : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => round rules available (stage rules available k)

theorem enabled_spec (available seen : List Nat) (r : Rule) :
    enabled available seen r = true ↔
      (∀ p ∈ r.ports, p ∈ available) ∧ (∀ x ∈ r.needs, x ∈ seen) := by
  simp [enabled, List.all_eq_true]

theorem round_spec {rules : Table} {available seen : List Nat} {v : Nat} :
    v ∈ round rules available seen ↔
      v ∈ seen ∨ ∃ r ∈ rules, r.head = v ∧
        (∀ p ∈ r.ports, p ∈ available) ∧ (∀ w ∈ r.needs, w ∈ seen) := by
  simp only [round, List.mem_append, List.mem_map, List.mem_filter, enabled_spec]
  grind

variable {n : Nat} {Γ : List (Fm PTm n)}
variable {rules : Table} {available : List Nat} {A R : Nat → Fm PTm n}

/-- Local proofs may have arbitrary object-language formulas. The sequents apply
to exactly the guards and antecedents recorded in the rule. -/
def Local (Γ : List (Fm PTm n)) (A R : Nat → Fm PTm n) (rules : Table) : Prop :=
  ∀ r ∈ rules, Prf PRAAx (r.needs.map A ++ r.ports.map R ++ Γ) (A r.head)

theorem replay (law : Local Γ A R rules)
    (supply : ∀ p ∈ available, Prf PRAAx Γ (R p)) (k v : Nat)
    (hv : v ∈ stage rules available k) : Prf PRAAx Γ (A v) := by
  induction k generalizing v with
  | zero => simp [stage] at hv
  | succ k ih =>
    rcases round_spec.mp hv with old | ⟨r, hr, rfl, hp, hw⟩
    · exact ih _ old
    · apply (law r hr).trans
      intro F hF
      simp only [List.mem_append, List.mem_map] at hF
      rcases hF with ((⟨w, hm, rfl⟩ | ⟨p, hm, rfl⟩) | hΓ)
      · exact ih _ (hw w hm)
      · exact supply p (hp p hm)
      · exact Prf.hyp hΓ

/-- A set closed under the enabled rules contains all marked vertices. The
predicate may be any Lean proposition: this is an external certificate theorem. -/
theorem least {S : Nat → Prop}
    (closed : ∀ r ∈ rules, (∀ p ∈ r.ports, p ∈ available) →
       (∀ w ∈ r.needs, S w) → S r.head) (k v : Nat)
    (hv : v ∈ stage rules available k) : S v := by
  induction k generalizing v with
  | zero => simp [stage] at hv
  | succ k ih =>
    rcases round_spec.mp hv with old | ⟨r, hr, rfl, hp, hw⟩
    · exact ih _ old
    · exact closed r hr hp (fun w hm => ih w (hw w hm))

def marked (g : Table) (p : List Nat) (k : Nat) : Finset Nat :=
  (stage g p k).toFinset

def heads (g : Table) : Finset Nat := (g.map Rule.head).toFinset

@[simp] theorem mem_marked {g p k v} : v ∈ marked g p k ↔ v ∈ stage g p k := by
  simp [marked]

theorem increasing (g : Table) (p : List Nat) (k : Nat) :
    marked g p k ⊆ marked g p (k+1) := by
  intro v hv
  exact mem_marked.mpr (round_spec.mpr (Or.inl (mem_marked.mp hv)))

theorem bounded (g : Table) (p : List Nat) (k : Nat) :
    marked g p k ⊆ heads g := by
  intro v hv
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  apply least (S := fun x => ∃ r ∈ g, r.head = x) _ k v (mem_marked.mp hv)
  intro r hr _ _
  exact ⟨r, hr, rfl⟩

/-- The following round depends only on membership of the preceding round. -/
theorem flat_next {g : Table} {p : List Nat} {k : Nat}
    (h : marked g p k = marked g p (k+1)) :
    marked g p (k+1) = marked g p (k+2) := by
  apply Finset.Subset.antisymm (increasing _ _ _)
  intro v hv
  rcases round_spec.mp (mem_marked.mp hv) with old | ⟨r, hr, he, hp, hw⟩
  · exact mem_marked.mpr old
  · apply mem_marked.mpr
    apply round_spec.mpr
    right
    refine ⟨r, hr, he, hp, ?_⟩
    intro w hm
    apply mem_marked.mp
    rw [h]
    exact mem_marked.mpr (hw w hm)

theorem growth_or_flat (g : Table) (p : List Nat) (k : Nat) :
    k ≤ (marked g p k).card ∨ marked g p k = marked g p (k+1) := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with hg | hf
    · by_cases eq : marked g p k = marked g p (k+1)
      · exact Or.inr (flat_next eq)
      · exact Or.inl (Nat.succ_le_of_lt (lt_of_le_of_lt hg
          (Finset.card_lt_card (ssubset_of_subset_of_ne (increasing _ _ _) eq))))
    · exact Or.inr (flat_next hf)

theorem stabilized (g : Table) (p : List Nat) :
    marked g p (heads g).card = marked g p ((heads g).card + 1) := by
  rcases growth_or_flat g p (heads g).card with hg | hf
  · apply Finset.eq_of_subset_of_card_le (increasing _ _ _)
    exact le_trans (Finset.card_le_card (bounded g p _)) hg
  · exact hf

theorem all_heights {g : Table} {p : List Nat} (k v : Nat) (hv : v ∈ stage g p k) :
    v ∈ marked g p (heads g).card := by
  apply least (S := fun w => w ∈ marked g p (heads g).card) _ k v hv
  intro r hr hp hw
  rw [stabilized g p]
  exact mem_marked.mpr (round_spec.mpr (Or.inr
    ⟨r, hr, rfl, hp, fun w hm => mem_marked.mp (hw w hm)⟩))


/-- A change of the supplied proof labels preserves all successful rounds when
the old supply is included in the new one. -/
theorem stage_supply_mono {g : Table} {s t : List Nat} (hst : s ⊆ t)
    (k v : Nat) (hv : v ∈ stage g s k) : v ∈ stage g t k := by
  induction k generalizing v with
  | zero => simp [stage] at hv
  | succ k ih =>
    rcases round_spec.mp hv with old | ⟨r, hr, he, hp, hw⟩
    · exact round_spec.mpr (Or.inl (ih _ old))
    · exact round_spec.mpr (Or.inr
        ⟨r, hr, he, fun p hm => hst (hp p hm), fun w hm => ih w (hw w hm)⟩)

def succeeds (g : Table) (v : Nat) (s : Finset Nat) : Prop :=
  v ∈ marked g s.toList (heads g).card

theorem succeeds_mono {g : Table} {v : Nat} {s t : Finset Nat}
    (h : s ⊆ t) (hs : succeeds g v s) : succeeds g v t := by
  apply mem_marked.mpr
  apply stage_supply_mono (s := s.toList) _ _ _ (mem_marked.mp hs)
  intro p hp
  exact Finset.mem_toList.mpr (h (Finset.mem_toList.mp hp))

/-- Minimality is checkable using single-port deletions alone. -/
def irreducible (g : Table) (v : Nat) (s : Finset Nat) : Prop :=
  succeeds g v s ∧ ∀ p ∈ s, ¬ succeeds g v (s.erase p)

theorem irreducible_iff_minimal {g : Table} {v : Nat} {s : Finset Nat} :
    irreducible g v s ↔
      succeeds g v s ∧ ∀ t, t ⊂ s → ¬ succeeds g v t := by
  constructor
  · rintro ⟨hs, noErase⟩
    refine ⟨hs, ?_⟩
    intro t ht htGood
    obtain ⟨p, hps, hpt⟩ := Finset.exists_of_ssubset ht
    apply noErase p hps
    apply succeeds_mono _ htGood
    exact Finset.subset_erase.mpr ⟨ht.subset, hpt⟩
  · rintro ⟨hs, noStrict⟩
    exact ⟨hs, fun p hp => noStrict _ (Finset.erase_ssubset hp)⟩

theorem successful_iff_contains_support (g : Table) (v : Nat) (t : Finset Nat) :
    succeeds g v t ↔ ∃ s, s ⊆ t ∧ irreducible g v s := by
  constructor
  · intro h
    induction t using Finset.strongInductionOn with
    | _ t ih =>
      by_cases last : ∀ p ∈ t, ¬ succeeds g v (t.erase p)
      · exact ⟨t, Finset.Subset.rfl, h, last⟩
      · push Not at last
        obtain ⟨p, hp, ok⟩ := last
        obtain ⟨s, hs, irr⟩ := ih _ (Finset.erase_ssubset hp) ok
        exact ⟨s, Finset.Subset.trans hs (Finset.erase_subset _ _), irr⟩
  · rintro ⟨s, hst, hs, _⟩
    exact succeeds_mono hst hs


def exampleTable : Table :=
  [⟨0, [1], []⟩, ⟨1, [0], []⟩, ⟨0, [], [0,1]⟩, ⟨1, [], [2]⟩]

example : 0 ∈ stage exampleTable [2] 2 := by decide
example : 0 ∉ stage exampleTable [0] 2 := by decide

theorem Local.weaken {Δ : List (Fm PTm n)} (law : Local Γ A R rules) (h : Γ ⊆ Δ) :
    Local Δ A R rules := by
  intro r hr
  apply (law r hr).weaken
  intro f hf
  simp only [List.mem_append] at hf ⊢
  exact hf.imp_right (fun hf => h hf)

/-- The two minimal supports for the displayed cyclic program become an ordinary
intuitionistic disjunction. The local rule derivations are the only parameters. -/
theorem two_supports (law : Local Γ A R exampleTable) :
    Prf PRAAx Γ ((((R 0) ⋏ (R 1)) ⋎ (R 2)) ⟶ A 0) := by
  apply Prf.impI
  apply Prf.orE Prf.hyp0
  · apply replay (available := [0,1]) (k := 2) (law.weaken (by
      intro f hf
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)))
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Prf.andE₁ Prf.hyp0
      · exact Prf.andE₂ Prf.hyp0
    · decide
  · apply replay (available := [2]) (k := 2) (law.weaken (by
      intro f hf
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)))
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact Prf.hyp0
    · decide


end LeanProofs.IPRA.Foundations.ScopedReplay
