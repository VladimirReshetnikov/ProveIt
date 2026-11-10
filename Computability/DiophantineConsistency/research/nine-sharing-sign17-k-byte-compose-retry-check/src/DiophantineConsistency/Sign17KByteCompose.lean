import DiophantineConsistency.Sign17KByteAlignment00
import DiophantineConsistency.Sign17KByteAlignment01
import DiophantineConsistency.Sign17KByteAlignment02
import DiophantineConsistency.Sign17KByteAlignment03
import DiophantineConsistency.Sign17KByteAlignment04
import DiophantineConsistency.Sign17KByteAlignment05
import DiophantineConsistency.Sign17KByteAlignment06
import DiophantineConsistency.Sign17KByteAlignment07

/-! SOURCE ONLY. Compose block fixtures with the independently checked tail. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KByteCompose

theorem radix_alignment : CurrentKernel2011.radix ^ 8 = (256 : ℕ) ^ 47 := by
  decide +kernel

theorem aligned_append {as bs cs ds : List (List ℕ)}
    (h₁ : List.Forall₂ Sign17KByteAlignmentCore.aligned as bs)
    (h₂ : List.Forall₂ Sign17KByteAlignmentCore.aligned cs ds) :
    List.Forall₂ Sign17KByteAlignmentCore.aligned (as ++ cs) (bs ++ ds) := by
  induction h₁ with
  | nil => exact h₂
  | cons h ht ih => exact .cons h ih

theorem flatten_tail {as bs : List (List ℕ)}
    (h : List.Forall₂ Sign17KByteAlignmentCore.aligned as bs)
    (xs ys : List ℕ)
    (ht : Nat.ofDigits CurrentKernel2011.radix xs = Nat.ofDigits 256 ys) :
    Nat.ofDigits CurrentKernel2011.radix (as.flatten ++ xs) =
      Nat.ofDigits 256 (bs.flatten ++ ys) := by
  induction h with
  | nil => simpa using ht
  | cons hhead hrest ih =>
    rcases hhead with ⟨ha, hb, hv⟩
    simp only [Nat.ofDigits_append] at ih
    simp only [List.flatten_cons, List.append_assoc, Nat.ofDigits_append]
    rw [ha, hb, hv, radix_alignment, ih]

def digitBlocks : List (List ℕ) := Sign17KByteAlignment00.digitBlocks ++ (Sign17KByteAlignment01.digitBlocks ++ (Sign17KByteAlignment02.digitBlocks ++ (Sign17KByteAlignment03.digitBlocks ++ (Sign17KByteAlignment04.digitBlocks ++ (Sign17KByteAlignment05.digitBlocks ++ (Sign17KByteAlignment06.digitBlocks ++ (Sign17KByteAlignment07.digitBlocks)))))))
def byteBlocks : List (List ℕ) := Sign17KByteAlignment00.byteBlocks ++ (Sign17KByteAlignment01.byteBlocks ++ (Sign17KByteAlignment02.byteBlocks ++ (Sign17KByteAlignment03.byteBlocks ++ (Sign17KByteAlignment04.byteBlocks ++ (Sign17KByteAlignment05.byteBlocks ++ (Sign17KByteAlignment06.byteBlocks ++ (Sign17KByteAlignment07.byteBlocks)))))))

theorem all_aligned : List.Forall₂ Sign17KByteAlignmentCore.aligned digitBlocks byteBlocks := by
  exact aligned_append Sign17KByteAlignment00.aligned (aligned_append Sign17KByteAlignment01.aligned (aligned_append Sign17KByteAlignment02.aligned (aligned_append Sign17KByteAlignment03.aligned (aligned_append Sign17KByteAlignment04.aligned (aligned_append Sign17KByteAlignment05.aligned (aligned_append Sign17KByteAlignment06.aligned (Sign17KByteAlignment07.aligned)))))))

def digitList : List ℕ := digitBlocks.flatten ++ [0, 0, 0, 0, 1]
def byteList : List ℕ := byteBlocks.flatten ++
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16]

theorem fixture_value : Nat.ofDigits CurrentKernel2011.radix digitList =
    Nat.ofDigits 256 byteList := by
  have ht : Nat.ofDigits CurrentKernel2011.radix [0, 0, 0, 0, 1] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
    decide +kernel
  exact flatten_tail all_aligned _ _ ht

end DiophantineConsistency.Sign17KByteCompose
#print axioms DiophantineConsistency.Sign17KByteCompose.fixture_value
