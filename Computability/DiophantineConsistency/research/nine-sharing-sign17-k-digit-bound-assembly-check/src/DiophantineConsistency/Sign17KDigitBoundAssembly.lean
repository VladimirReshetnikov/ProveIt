import DiophantineConsistency.Sign17KDigitBoundProbe
import DiophantineConsistency.Sign17KDigitBoundBlock01
import DiophantineConsistency.Sign17KDigitBoundBlock02
import DiophantineConsistency.Sign17KDigitBoundBlock03
import DiophantineConsistency.Sign17KDigitBoundBlock04
import DiophantineConsistency.Sign17KDigitBoundBlock05
import DiophantineConsistency.Sign17KDigitBoundBlock06
import DiophantineConsistency.Sign17KDigitBoundBlock07
import DiophantineConsistency.Sign17KDigitBoundBlock08
import DiophantineConsistency.Sign17KDigitBoundBlock09
import DiophantineConsistency.Sign17KDigitBoundBlock10
import DiophantineConsistency.Sign17KDigitBoundBlock11
import DiophantineConsistency.Sign17KDigitBoundBlock12
import DiophantineConsistency.Sign17KDigitBoundBlock13
import DiophantineConsistency.Sign17KDigitBoundBlock14

/-! SOURCE ONLY. Assemble finite coefficient bounds and specialize the stream. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KDigitBoundAssembly
open CurrentKernel2011

theorem append_bound {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i + 1 < radix) (hb : ∀ i, b i + 1 < radix) :
    ∀ i, (Fin.append a b) i + 1 < radix := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using ha j
  · intro j
    simpa only [Fin.append_right] using hb j

theorem coefficients_bound (i : Fin 986) :
    Sign17KLiteralCoefficients.literal i + 1 < radix := by
  have h96 : ∀ i : Fin 96, Sign17KTileCoeffUnion96.literal i + 1 < radix :=
    append_bound Sign17KTileCoefficients00.literal Sign17KTileCoefficients01.literal
      Sign17KDigitBoundProbe.first_block_bound Sign17KDigitBoundBlock01.bound
  have h160 : ∀ i : Fin 160, Sign17KTileCoeffUnion224.literal160 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion96.literal Sign17KTileCoefficients02.literal
      h96 Sign17KDigitBoundBlock02.bound
  have h224 : ∀ i : Fin 224, Sign17KTileCoeffUnion224.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion224.literal160 Sign17KTileCoefficients03.literal
      h160 Sign17KDigitBoundBlock03.bound
  have h288 : ∀ i : Fin 288, Sign17KTileCoeffUnion352.literal288 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion224.literal Sign17KTileCoefficients04.literal
      h224 Sign17KDigitBoundBlock04.bound
  have h352 : ∀ i : Fin 352, Sign17KTileCoeffUnion352.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion352.literal288 Sign17KTileCoefficients05.literal
      h288 Sign17KDigitBoundBlock05.bound
  have h416 : ∀ i : Fin 416, Sign17KTileCoeffUnion480.literal416 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion352.literal Sign17KTileCoefficients06.literal
      h352 Sign17KDigitBoundBlock06.bound
  have h480 : ∀ i : Fin 480, Sign17KTileCoeffUnion480.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion480.literal416 Sign17KTileCoefficients07.literal
      h416 Sign17KDigitBoundBlock07.bound
  have h544 : ∀ i : Fin 544, Sign17KTileCoeffUnion608.literal544 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion480.literal Sign17KTileCoefficients08.literal
      h480 Sign17KDigitBoundBlock08.bound
  have h608 : ∀ i : Fin 608, Sign17KTileCoeffUnion608.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion608.literal544 Sign17KTileCoefficients09.literal
      h544 Sign17KDigitBoundBlock09.bound
  have h672 : ∀ i : Fin 672, Sign17KTileCoeffUnion736.literal672 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion608.literal Sign17KTileCoefficients10.literal
      h608 Sign17KDigitBoundBlock10.bound
  have h736 : ∀ i : Fin 736, Sign17KTileCoeffUnion736.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion736.literal672 Sign17KTileCoefficients11.literal
      h672 Sign17KDigitBoundBlock11.bound
  have h800 : ∀ i : Fin 800, Sign17KTileCoeffUnion864.literal800 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion736.literal Sign17KTileCoefficients12.literal
      h736 Sign17KDigitBoundBlock12.bound
  have h864 : ∀ i : Fin 864, Sign17KTileCoeffUnion864.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion864.literal800 Sign17KTileCoefficients13.literal
      h800 Sign17KDigitBoundBlock13.bound
  have h928 : ∀ i : Fin 928, Sign17KTileCoeffUnion942.literal928 i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion864.literal Sign17KTileCoefficients14.literal
      h864 Sign17KDigitBoundBlock14.bound
  have h942 : ∀ i : Fin 942, Sign17KTileCoeffUnion942.literal i + 1 < radix :=
    append_bound Sign17KTileCoeffUnion942.literal928 Sign17KTileCoefficients15.literal
      h928 Sign17KDigitBoundProbe.tail_block_bound
  exact append_bound Sign17KTileCoeffUnion942.literal Sign17KControlBlocks.literal
    h942 Sign17KDigitBoundProbe.control_block_bound i

theorem actual_digits_bound (d : ℕ)
    (hd : d ∈ Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal) :
    d < radix :=
  Sign17KDigitBoundProbe.stream_bound Sign17KLiteralCoefficients.literal
    coefficients_bound d hd

end DiophantineConsistency.Sign17KDigitBoundAssembly
#print axioms DiophantineConsistency.Sign17KDigitBoundAssembly.coefficients_bound
#print axioms DiophantineConsistency.Sign17KDigitBoundAssembly.actual_digits_bound
