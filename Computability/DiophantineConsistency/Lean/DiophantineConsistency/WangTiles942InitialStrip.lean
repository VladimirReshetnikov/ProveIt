import DiophantineConsistency.WangTiles942InitialHorizontal
import DiophantineConsistency.WangTiles942Periodic

/-!
# A finite initialization strip around Start in a periodic horizontal row

The two first departures from the respective initializer tails must be
seams. Horizontal periodicity supplies finite departure witnesses using
Start on the left and the head initializer on the right. No unique Start,
time evolution, machine run, or rectangular tiling premise is used.
-/

namespace DiophantineConsistency.WangTiles942InitialStrip

open WangTiles942 WangTiles942Language WangTiles942InitialHorizontal
  WangTiles942Periodic

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact wall tuples and every tile of the finite initial segment. -/
structure InitialStrip (T : ℤ → Tile) (N L R : ℕ) : Prop where
  left_pos : 0 < L
  left_le : L ≤ N
  right_min : 2 ≤ R
  right_le : R ≤ N+1
  start_at_zero : T 0 = start
  head_at_one : T 1 = ⟨3,436,4,4⟩
  left_wall : ∃ a : Fin 3, T (-(L : ℤ)) = ⟨a.val^2,437,2,437⟩
  right_wall : ∃ b : Fin 3, T (R : ℤ) = ⟨4,437,b.val,437⟩
  left_inside : ∀ j : ℕ, 1 ≤ j → j < L → T (-(j : ℤ)) = ⟨2,434,2,0⟩
  right_inside : ∀ j : ℕ, 2 ≤ j → j < R → T (j : ℤ) = ⟨4,436,4,0⟩

theorem head_after_start (T : ℤ → Tile) (hallowed : ∀ x, Allowed (T x))
    (hH : ∀ x, (T (x+1)).west = (T x).east) (hstart : T 0 = start) :
    T 1 = ⟨3,436,4,4⟩ := by
  apply (west_3_iff_initHead (hallowed 1)).mp
  have hh := hH 0
  simpa only [zero_add, hstart, start] using hh

/-- First non-initLeft to the left. Periodic Start supplies a witness byN. -/
theorem left_wall_exists (T : ℤ → Tile) (hallowed : ∀ x, Allowed (T x))
    (hH : ∀ x, (T (x+1)).west = (T x).east)
    (N : ℕ) (hN : 0 < N) (hperiod : Function.Periodic T (N : ℤ))
    (hstart : T 0 = start) :
    ∃ L : ℕ, 0 < L ∧ L ≤ N ∧
      (∃ a : Fin 3, T (-(L : ℤ)) = ⟨a.val^2,437,2,437⟩) ∧
      ∀ j : ℕ, 1 ≤ j → j < L → T (-(j : ℤ)) = ⟨2,434,2,0⟩ := by
  classical
  have hminus : T (-(N : ℤ)) = start := by
    have hh := hperiod (-(N : ℤ))
    rw [neg_add_cancel, hstart] at hh
    exact hh.symm
  have hend : T (-(N : ℤ)) ≠ (⟨2,434,2,0⟩ : Tile) := by rw [hminus]; decide
  have hex : ∃ j : ℕ, 1 ≤ j ∧ T (-(j : ℤ)) ≠ (⟨2,434,2,0⟩ : Tile) :=
    ⟨N, hN, hend⟩
  let L := Nat.find hex
  have hL : 1 ≤ L ∧ T (-(L : ℤ)) ≠ (⟨2,434,2,0⟩ : Tile) := Nat.find_spec hex
  have hLN : L ≤ N := Nat.find_min' hex ⟨hN,hend⟩
  have hinside (j : ℕ) (hj : 1 ≤ j) (hjl : j < L) :
      T (-(j : ℤ)) = (⟨2,434,2,0⟩ : Tile) := by
    by_contra hnot
    exact Nat.find_min hex hjl ⟨hj,hnot⟩
  have hright : (T (-(L : ℤ)+1)).west = 2 := by
    by_cases he : L = 1
    · rw [he]
      norm_num only [Nat.cast_one, neg_add_cancel]
      rw [hstart]
      rfl
    · have hi := hinside (L-1) (by omega) (by omega)
      have heq : -((L-1 : ℕ) : ℤ) = -(L : ℤ)+1 := by omega
      rw [heq] at hi
      rw [hi]
  have heast : (T (-(L : ℤ))).east = 2 := (hH (-(L : ℤ))).symm.trans hright
  have hs := ((east_2_iff_initLeft_or_seam (hallowed (-(L : ℤ)))).mp heast).resolve_left hL.2
  exact ⟨L, hL.1, hLN, hs, hinside⟩

/-- First non-initRight after the head. Periodic head supplies a witness byN+1. -/
theorem right_wall_exists (T : ℤ → Tile) (hallowed : ∀ x, Allowed (T x))
    (hH : ∀ x, (T (x+1)).west = (T x).east)
    (N : ℕ) (hN : 0 < N) (hperiod : Function.Periodic T (N : ℤ))
    (hhead : T 1 = ⟨3,436,4,4⟩) :
    ∃ R : ℕ, 2 ≤ R ∧ R ≤ N+1 ∧
      (∃ b : Fin 3, T (R : ℤ) = ⟨4,437,b.val,437⟩) ∧
      ∀ j : ℕ, 2 ≤ j → j < R → T (j : ℤ) = ⟨4,436,4,0⟩ := by
  classical
  have hplus : T ((N+1 : ℕ) : ℤ) = (⟨3,436,4,4⟩ : Tile) := by
    rw [Nat.cast_add, Nat.cast_one, add_comm]
    exact (hperiod 1).trans hhead
  have hend : T ((N+1 : ℕ) : ℤ) ≠ (⟨4,436,4,0⟩ : Tile) := by rw [hplus]; decide
  have hex : ∃ j : ℕ, 2 ≤ j ∧ T (j : ℤ) ≠ (⟨4,436,4,0⟩ : Tile) :=
    ⟨N+1, by omega, hend⟩
  let R := Nat.find hex
  have hR : 2 ≤ R ∧ T (R : ℤ) ≠ (⟨4,436,4,0⟩ : Tile) := Nat.find_spec hex
  have hRN : R ≤ N+1 := Nat.find_min' hex ⟨by omega,hend⟩
  have hinside (j : ℕ) (hj : 2 ≤ j) (hjr : j < R) :
      T (j : ℤ) = (⟨4,436,4,0⟩ : Tile) := by
    by_contra hnot
    exact Nat.find_min hex hjr ⟨hj,hnot⟩
  have hleft : (T ((R : ℤ)-1)).east = 4 := by
    by_cases he : R = 2
    · rw [he]
      norm_num only [Nat.cast_ofNat, Int.reduceSub]
      rw [hhead]
    · have hi := hinside (R-1) (by omega) (by omega)
      have heq : ((R-1 : ℕ) : ℤ) = (R : ℤ)-1 := by omega
      rw [heq] at hi
      rw [hi]
  have hwest : (T (R : ℤ)).west = 4 := by
    have hh := hH ((R : ℤ)-1)
    rw [sub_add_cancel] at hh
    exact hh.trans hleft
  have hs := ((west_4_iff_initRight_or_seam (hallowed (R : ℤ))).mp hwest).resolve_left hR.2
  exact ⟨R, hR.1, hRN, hs, hinside⟩

/-- A horizontally periodic allowed row containing Start has exact finite
seam walls and a complete blank-initialization segment between them. -/
theorem periodic_initial_strip (T : ℤ → Tile) (hallowed : ∀ x, Allowed (T x))
    (hH : ∀ x, (T (x+1)).west = (T x).east)
    (N : ℕ) (hN : 0 < N) (hperiod : Function.Periodic T (N : ℤ))
    (hstart : T 0 = start) : ∃ L R : ℕ, InitialStrip T N L R := by
  have hhead := head_after_start T hallowed hH hstart
  obtain ⟨L,hL,hLN,hwallL,hinsideL⟩ := left_wall_exists T hallowed hH N hN hperiod hstart
  obtain ⟨R,hR,hRN,hwallR,hinsideR⟩ := right_wall_exists T hallowed hH N hN hperiod hhead
  exact ⟨L,R,hL,hLN,hR,hRN,hstart,hhead,hwallL,hwallR,hinsideL,hinsideR⟩

theorem InitialStrip.wall_north {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R) :
    (T (-(L : ℤ))).north = 437 ∧ (T (R : ℤ)).north = 437 := by
  obtain ⟨a,ha⟩ := h.left_wall
  obtain ⟨b,hb⟩ := h.right_wall
  rw [ha,hb]
  exact ⟨rfl,rfl⟩

/-- Specialization to the actual signed plane row uses only its marked word. -/
theorem marked_initial_strip {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) :
    ∃ L R : ℕ, InitialStrip (fun x => plane N s a x 0) N L R := by
  apply periodic_initial_strip (fun x => plane N s a x 0)
    (fun x => plane_allowed N s a x 0) (fun x => plane_east_matching h x 0)
    N (NeZero.pos N) (fun x => plane_horizontal_period N s a x 0)
  exact plane_start h

end DiophantineConsistency.WangTiles942InitialStrip
