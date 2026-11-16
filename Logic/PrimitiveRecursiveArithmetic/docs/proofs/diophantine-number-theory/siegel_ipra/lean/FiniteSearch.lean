import Std

/-! Exact finite enumeration. No global height bound is assumed as an axiom. -/
namespace SiegelIPRA

def scan (p : Nat → Bool) (B : Nat) : List Nat :=
  (List.range (B+1)).filter p

theorem mem_scan (p : Nat → Bool) (B n : Nat) :
    n ∈ scan p B ↔ n ≤ B ∧ p n = true := by
  simp only [scan, List.mem_filter, List.mem_range, Nat.lt_succ_iff]

def Covers (p : Nat → Bool) (L : List Nat) : Prop :=
  ∀ n, p n = true ↔ n ∈ L

def Bounded (p : Nat → Bool) (B : Nat) : Prop :=
  ∀ n, p n = true → n ≤ B

theorem scan_covers (p : Nat → Bool) (B : Nat) (h : Bounded p B) :
    Covers p (scan p B) := by
  intro n
  rw [mem_scan]
  exact ⟨fun hp => ⟨h n hp, hp⟩, fun hn => hn.2⟩

def listBound : List Nat → Nat
  | [] => 0
  | a :: xs => max a (listBound xs)

theorem mem_le_listBound {n : Nat} {L : List Nat} (h : n ∈ L) :
    n ≤ listBound L := by
  induction L with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl hn => subst n; exact Nat.le_max_left _ _
    | inr hn => exact Nat.le_trans (ih hn) (Nat.le_max_right _ _)

theorem covers_bounded (p : Nat → Bool) (L : List Nat) (h : Covers p L) :
    Bounded p (listBound L) := by
  intro n hn
  exact mem_le_listBound ((h n).mp hn)

theorem list_iff_bound (p : Nat → Bool) :
    (∃ L, Covers p L) ↔ ∃ B, Bounded p B := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := h
    exact ⟨listBound L, covers_bounded p L hL⟩
  · intro h
    obtain ⟨B,hB⟩ := h
    exact ⟨scan p B, scan_covers p B hB⟩

/-- A bound on a supplied finite prefix is unrelated to eventual exhaustion. -/
theorem prefix_always_bounded (p : Nat → Bool) (N : Nat) :
    ∃ B, ∀ n, n ≤ N → p n = true → n ≤ B := by
  exact ⟨N, fun _ hn _ => hn⟩

theorem bound_not_unbounded (p : Nat → Bool) :
    (∃ B, Bounded p B) → ¬(∀ B, ∃ n, B < n ∧ p n = true) := by
  intro h hu
  obtain ⟨B,hB⟩ := h
  obtain ⟨n,hn,hp⟩ := hu B
  have hb := hB n hp
  omega

end SiegelIPRA
