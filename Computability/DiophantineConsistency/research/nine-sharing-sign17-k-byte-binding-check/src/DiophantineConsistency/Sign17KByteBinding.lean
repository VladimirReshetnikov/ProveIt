import DiophantineConsistency.Sign17KStreamCompare00
import DiophantineConsistency.Sign17KStreamCompare01
import DiophantineConsistency.Sign17KStreamCompare02
import DiophantineConsistency.Sign17KStreamCompare03
import DiophantineConsistency.Sign17KStreamCompare04
import DiophantineConsistency.Sign17KStreamCompare05
import DiophantineConsistency.Sign17KStreamCompare06
import DiophantineConsistency.Sign17KStreamCompare07

/-! SOURCE ONLY. Assemble bounded comparisons into an in-Lean K byte value. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KByteBinding
open CurrentKernel2011

def actualDigits : List ℕ := Sign17KRadixStream.lowPrefix ++
  (Sign17KStreamExplicit.coefficientsReversed.set 984 30099357829123 ++
    Sign17KRadixStream.suffix)

theorem actual_ends : actualDigits.drop 2048 = [] := by
  decide +kernel

theorem fixture_ends : Sign17KByteCompose.digitList.drop 2048 = [] := by
  decide +kernel

theorem take_drop_ext {α : Type} (n : ℕ) (xs ys : List α)
    (ht : xs.take n = ys.take n) (hd : xs.drop n = ys.drop n) : xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [ht, hd]
    _ = ys := List.take_append_drop n ys

theorem fixture_digits : actualDigits = Sign17KByteCompose.digitList := by
  have h8 : actualDigits.drop 2048 = Sign17KByteCompose.digitList.drop 2048 := by
    rw [actual_ends, fixture_ends]
  have h7 : actualDigits.drop 1792 = Sign17KByteCompose.digitList.drop 1792 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare07.chunk
    · simpa only [List.drop_drop] using h8
  have h6 : actualDigits.drop 1536 = Sign17KByteCompose.digitList.drop 1536 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare06.chunk
    · simpa only [List.drop_drop] using h7
  have h5 : actualDigits.drop 1280 = Sign17KByteCompose.digitList.drop 1280 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare05.chunk
    · simpa only [List.drop_drop] using h6
  have h4 : actualDigits.drop 1024 = Sign17KByteCompose.digitList.drop 1024 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare04.chunk
    · simpa only [List.drop_drop] using h5
  have h3 : actualDigits.drop 768 = Sign17KByteCompose.digitList.drop 768 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare03.chunk
    · simpa only [List.drop_drop] using h4
  have h2 : actualDigits.drop 512 = Sign17KByteCompose.digitList.drop 512 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare02.chunk
    · simpa only [List.drop_drop] using h3
  have h1 : actualDigits.drop 256 = Sign17KByteCompose.digitList.drop 256 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare01.chunk
    · simpa only [List.drop_drop] using h2
  have h0 : actualDigits.drop 0 = Sign17KByteCompose.digitList.drop 0 := by
    apply take_drop_ext 256
    · exact Sign17KStreamCompare00.chunk
    · simpa only [List.drop_drop] using h1
  simpa only [List.drop_zero] using h0

theorem K_bytes : Nat.ofDigits 256 Sign17KByteCompose.byteList = K := by
  calc
    Nat.ofDigits 256 Sign17KByteCompose.byteList =
        Nat.ofDigits radix Sign17KByteCompose.digitList := Sign17KByteCompose.fixture_value.symm
    _ = Nat.ofDigits radix actualDigits := by rw [fixture_digits]
    _ = Nat.ofDigits radix (Nat.digits radix K) := by
      rw [Sign17KStreamExplicit.digits_explicit]
    _ = K := Nat.ofDigits_digits radix K

end DiophantineConsistency.Sign17KByteBinding
#print axioms DiophantineConsistency.Sign17KByteBinding.fixture_digits
#print axioms DiophantineConsistency.Sign17KByteBinding.K_bytes
