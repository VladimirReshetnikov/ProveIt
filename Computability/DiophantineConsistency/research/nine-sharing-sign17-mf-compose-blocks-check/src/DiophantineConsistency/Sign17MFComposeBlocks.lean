import DiophantineConsistency.Sign17MCComposeCore
import DiophantineConsistency.Sign17MFRadixDigits
import DiophantineConsistency.Sign17MFChunks

/-! SOURCE-ONLY: compose the MF source-port digit/byte block patterns. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MFComposeBlocks
open CurrentMasks2011 Sign17MCComposeCore

def digitsA : List ℕ := List.replicate 1 3 ++ List.replicate 7 8
def bytesA : List ℕ := [3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0]

theorem alignedA : aligned digitsA bytesA := by
  refine ⟨by simp [digitsA], by decide, ?_⟩
  simpa [digitsA, bytesA, List.replicate] using Sign17MFChunks.first

def digitsB : List ℕ := List.replicate 8 8
def bytesB : List ℕ := [8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0]

theorem alignedB : aligned digitsB bytesB := by
  refine ⟨by simp [digitsB], by decide, ?_⟩
  simpa [digitsB, bytesB, List.replicate] using Sign17MFChunks.eights

def digitsC : List ℕ := List.replicate 5 8 ++ List.replicate 3 0
def bytesC : List ℕ := [8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem alignedC : aligned digitsC bytesC := by
  refine ⟨by simp [digitsC], by decide, ?_⟩
  simpa [digitsC, bytesC, List.replicate] using Sign17MFChunks.end_eights

def digitsD : List ℕ := List.replicate 8 0
def bytesD : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem alignedD : aligned digitsD bytesD := by
  refine ⟨by simp [digitsD], by decide, ?_⟩
  simpa [digitsD, bytesD, List.replicate] using Sign17MFChunks.zeros

def digitsE : List ℕ := List.replicate 8 1
def bytesE : List ℕ := [1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]

theorem alignedE : aligned digitsE bytesE := by
  refine ⟨by simp [digitsE], by decide, ?_⟩
  simpa [digitsE, bytesE, List.replicate] using Sign17MFChunks.ones

def digitsF : List ℕ := List.replicate 1 1 ++ List.replicate 7 0
def bytesF : List ℕ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem alignedF : aligned digitsF bytesF := by
  refine ⟨by simp [digitsF], by decide, ?_⟩
  simpa [digitsF, bytesF, List.replicate] using Sign17MFChunks.end_ones

def digitsG : List ℕ := List.replicate 3 0 ++ List.replicate 5 1
def bytesG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]

theorem alignedG : aligned digitsG bytesG := by
  refine ⟨by simp [digitsG], by decide, ?_⟩
  simpa [digitsG, bytesG, List.replicate] using Sign17MFChunks.start_ones

def digitsH : List ℕ := List.replicate 3 1 ++ List.replicate 5 0
def bytesH : List ℕ := [1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem alignedH : aligned digitsH bytesH := by
  refine ⟨by simp [digitsH], by decide, ?_⟩
  simpa [digitsH, bytesH, List.replicate] using Sign17MFChunks.end_ones2

def digitsI : List ℕ := List.replicate 4 0 ++ [1, 2 ^ 45 - 4] ++ List.replicate 2 0
def bytesI : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 224, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem alignedI : aligned digitsI bytesI := by
  refine ⟨by simp [digitsI], by decide, ?_⟩
  simpa [digitsI, bytesI, List.replicate] using Sign17MFChunks.marker

def digitsJ : List ℕ := List.replicate 3 0 ++ List.replicate 1 1
def bytesJ : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32]

theorem tail_value : Nat.ofDigits radix digitsJ = Nat.ofDigits 256 bytesJ := by
  simpa [digitsJ, bytesJ, List.replicate] using Sign17MFChunks.tail

def digitBlocks : List (List ℕ) :=
  [digitsA] ++ List.replicate 113 digitsB ++ [digitsC] ++ List.replicate 5 digitsD ++
    [digitsE, digitsF, digitsD, digitsG, digitsH, digitsI] ++ List.replicate 125 digitsD

def byteBlocks : List (List ℕ) :=
  [bytesA] ++ List.replicate 113 bytesB ++ [bytesC] ++ List.replicate 5 bytesD ++
    [bytesE, bytesF, bytesD, bytesG, bytesH, bytesI] ++ List.replicate 125 bytesD

theorem blocks_aligned : List.Forall₂ aligned digitBlocks byteBlocks := by
  unfold digitBlocks byteBlocks
  apply aligned_append (List.Forall₂.cons alignedA List.Forall₂.nil)
  apply aligned_append (aligned_repeat digitsB bytesB alignedB 113)
  apply aligned_append (List.Forall₂.cons alignedC List.Forall₂.nil)
  apply aligned_append (aligned_repeat digitsD bytesD alignedD 5)
  apply aligned_append (List.Forall₂.cons alignedE (List.Forall₂.cons alignedF
    (List.Forall₂.cons alignedD (List.Forall₂.cons alignedG
      (List.Forall₂.cons alignedH (List.Forall₂.cons alignedI List.Forall₂.nil))))))
  exact aligned_repeat digitsD bytesD alignedD 125

theorem blocks_value :
    Nat.ofDigits radix (digitBlocks.flatten ++ digitsJ) =
      Nat.ofDigits 256 (byteBlocks.flatten ++ bytesJ) :=
  flatten_tail blocks_aligned digitsJ bytesJ tail_value

end DiophantineConsistency.Sign17MFComposeBlocks
#print axioms DiophantineConsistency.Sign17MFComposeBlocks.blocks_aligned
#print axioms DiophantineConsistency.Sign17MFComposeBlocks.blocks_value
