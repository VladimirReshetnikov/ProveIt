import DiophantineConsistency.Sign17MCComposeCore

/-! SOURCE-ONLY: compose the six checked MC digit/byte block patterns. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCComposeBlocks
open CurrentMasks2011 Sign17MCComposeCore

def digitsA : List ℕ := List.replicate 8 (radix - 2)
def bytesA : List ℕ := [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 191, 255, 255, 255, 255, 255, 223, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 247, 255, 255, 255, 255, 255, 251, 255, 255, 255, 255, 255, 253, 255, 255, 255, 255, 255]

theorem alignedA : aligned digitsA bytesA := by
  refine ⟨by simp [digitsA], by decide, ?_⟩
  simpa [digitsA, bytesA, List.replicate] using Sign17MCChunks.all_selected

def digitsB : List ℕ := List.replicate 7 (radix - 2) ++ List.replicate 1 (radix - 1)
def bytesB : List ℕ := [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 191, 255, 255, 255, 255, 255, 223, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 247, 255, 255, 255, 255, 255, 251, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

theorem alignedB : aligned digitsB bytesB := by
  refine ⟨by simp [digitsB], by decide, ?_⟩
  simpa [digitsB, bytesB, List.replicate] using Sign17MCChunks.boundary_951

def digitsC : List ℕ := List.replicate 8 (radix - 1)
def bytesC : List ℕ := [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

theorem alignedC : aligned digitsC bytesC := by
  refine ⟨by simp [digitsC], by decide, ?_⟩
  simpa [digitsC, bytesC, List.replicate] using Sign17MCChunks.all_unselected

def digitsD : List ℕ := List.replicate 2 (radix - 2) ++ List.replicate 6 (radix - 1)
def bytesD : List ℕ := [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

theorem alignedD : aligned digitsD bytesD := by
  refine ⟨by simp [digitsD], by decide, ?_⟩
  simpa [digitsD, bytesD, List.replicate] using Sign17MCChunks.boundary_986

def digitsE : List ℕ := List.replicate 4 (radix - 1) ++ List.replicate 1 (radix - 2) ++ List.replicate 3 (radix - 1)
def bytesE : List ℕ := [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

theorem alignedE : aligned digitsE bytesE := by
  refine ⟨by simp [digitsE], by decide, ?_⟩
  simpa [digitsE, bytesE, List.replicate] using Sign17MCChunks.marker_1004

def digitsF : List ℕ := List.replicate 3 (radix - 1)
def bytesF : List ℕ := [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 31]

theorem tail_value : Nat.ofDigits radix digitsF = Nat.ofDigits 256 bytesF := by
  simpa [digitsF, bytesF, List.replicate] using Sign17MCChunks.final_3

def digitBlocks : List (List ℕ) :=
  List.replicate 118 digitsA ++ [digitsB, digitsC] ++ List.replicate 3 digitsA ++
    [digitsD, digitsC, digitsE] ++ List.replicate 125 digitsC

def byteBlocks : List (List ℕ) :=
  List.replicate 118 bytesA ++ [bytesB, bytesC] ++ List.replicate 3 bytesA ++
    [bytesD, bytesC, bytesE] ++ List.replicate 125 bytesC

theorem blocks_aligned : List.Forall₂ aligned digitBlocks byteBlocks := by
  unfold digitBlocks byteBlocks
  apply aligned_append (aligned_repeat digitsA bytesA alignedA 118)
  apply aligned_append (List.Forall₂.cons alignedB (List.Forall₂.cons alignedC List.Forall₂.nil))
  apply aligned_append (aligned_repeat digitsA bytesA alignedA 3)
  apply aligned_append (List.Forall₂.cons alignedD
    (List.Forall₂.cons alignedC (List.Forall₂.cons alignedE List.Forall₂.nil)))
  exact aligned_repeat digitsC bytesC alignedC 125

theorem blocks_value :
    Nat.ofDigits radix (digitBlocks.flatten ++ digitsF) =
      Nat.ofDigits 256 (byteBlocks.flatten ++ bytesF) :=
  flatten_tail blocks_aligned digitsF bytesF tail_value

end DiophantineConsistency.Sign17MCComposeBlocks
#print axioms DiophantineConsistency.Sign17MCComposeBlocks.blocks_aligned
#print axioms DiophantineConsistency.Sign17MCComposeBlocks.blocks_value
