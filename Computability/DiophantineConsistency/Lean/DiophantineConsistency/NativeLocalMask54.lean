import DiophantineConsistency.NativeHighPort54
import DiophantineConsistency.NativeTemporalSupport54

/-! # Every native cell has an actual local clause-mask zero

One of the two separated targets is temporally clean for every possible
bit phase. Global temporal alignment is not used by this theorem.
-/

namespace DiophantineConsistency.NativeLocalMask54

open NativeStencil54 NativeSparseDigits54 NativeCleanBands54 NativeSourceMask
  NativeBinaryScale NativePellBootstrap NativeHighPort54 NativeTemporalSupport54
  NativeCyclicConvolution NativeCyclicRotation NativeClause54

variable {N : ℕ} [NeZero (N * cellLength)]

theorem addition_residue (b : ZMod (N * cellLength)) (e : ℕ) :
    (b + (e : ZMod (N * cellLength))).val % cellLength = (b.val + e) % cellLength := by
  have hh : (((b + (e : ZMod (N * cellLength))).val : ℕ) : ZMod (N * cellLength)) =
      ((b.val + e : ℕ) : ZMod (N * cellLength)) := by
    simp only [Nat.cast_add,ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N,by ring⟩

/-- The complete literal local coefficient sum at the base of a cell. -/
def localCell (c : ZMod (N * cellLength) → ℕ) (b : ZMod (N * cellLength)) : ℕ :=
  (NativeStencil54.entries.map fun p => p.2 * c (b + p.1)).sum

omit [NeZero (N * cellLength)] in
theorem localContribution_eq_cell (c : ZMod (N * cellLength) → ℕ)
    (b : ZMod (N * cellLength)) (t : ℕ) :
    localContribution c (b + t) t = localCell c b := by
  unfold localContribution localCell
  congr 1
  apply List.map_congr_left
  intro p _
  congr 2
  abel

/-- A positive literal source zero produces valid local clause-mask tests
in every cell. No zero temporal phase, one-hot selection or accepted
local clause is supplied as a hypothesis. -/
theorem source_local_masks (ports : Fin 4 → ℤ)
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort (highPort radix))
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (hq : sourceQ ports x = (2 ^ (89 * cellLength)) ^ N)
    (hK : (ports 1).toNat = rawWord radix) :
    ∃ c : ZMod (N * cellLength) → ℕ,
      word radix c = gap ports x ∧ c 0 = 1 ∧
      (∀ k, c k < 2 ^ periodicBits k) ∧
      ∀ b, b.val % cellLength = 0 → localCell c b &&& clauseMask = 0 := by
  obtain ⟨c,hC,h0,hbits,hleft,hright⟩ := source_clause_masks ports h x hx hs hq hK
  refine ⟨c,hC,h0,hbits,?_⟩
  intro b hb
  let l := b + (2409 : ZMod (N * cellLength))
  let r := b + (3015 : ZMod (N * cellLength))
  have hl : l.val % cellLength = 2409 := by
    dsimp [l]
    rw [show (2409 : ZMod (N * cellLength)) = ((2409 : ℕ) : ZMod (N * cellLength)) by norm_num,
      addition_residue]
    simp only [Nat.add_mod,hb,Nat.zero_add]
    decide
  have hr : r.val % cellLength = 3015 := by
    dsimp [r]
    rw [show (3015 : ZMod (N * cellLength)) = ((3015 : ℕ) : ZMod (N * cellLength)) by norm_num,
      addition_residue]
    simp only [Nat.add_mod,hb,Nat.zero_add]
    decide
  have ht : NativeWindowConvolution54.temporalDigits x c l = 0 ∨
      NativeWindowConvolution54.temporalDigits x c r = 0 :=
    clause_pair_one_zero ((nativeRank x).toNat - 89 * (N * cellLength)) c hbits l r (by dsimp [l,r]; ring)
  rcases ht with ht | ht
  · have hm := hleft l hl
    rw [ht,add_zero] at hm
    change localContribution c (b + (2409 : ℕ)) 2409 &&& clauseMask = 0 at hm
    rwa [localContribution_eq_cell] at hm
  · have hm := hright r hr
    rw [ht,add_zero] at hm
    change localContribution c (b + (3015 : ℕ)) 3015 &&& clauseMask = 0 at hm
    rwa [localContribution_eq_cell] at hm

end DiophantineConsistency.NativeLocalMask54
