import DiophantineConsistency.CurrentWordTopBounds2011
import DiophantineConsistency.CurrentWordLowMask2011

/-!
# Positive scalar witnesses from the actual constructed words

The normalization is first constructed without a high mask or controller.
Its proved size bounds supply alpha and strong slack; its exact modular
transport supplies z. The printed transport factor is one, not zero.
This is a partial scalar construction, not a full source-system solution.
-/

namespace DiophantineConsistency.CurrentWordScalarWitness2011

open CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
open CurrentWordTopBounds2011 CurrentWordLowMask2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- The actual radix window, retaining its full product length. -/
def q (N : ℕ) : ℕ := radix^(N*2011)

def source {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) : ℕ :=
  NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker)

def normalized {N : ℕ} [NeZero N] (digits : ZMod (N*2011) → ℕ) : ℕ :=
  NativeCyclicConvolution.word radix digits

def multiplier (s : ℕ) : ℕ := 2^(displacement s)

def alpha (q C F : ℕ) : ℕ := q-C-F

def quotientWitness (q A : ℕ) : ℕ := A/(q-1)+1

/-- A generic strict bound from the same one-digit-short prefixes. -/
theorem slack_of_prefix {q C F P ρ : ℕ} (hq : q=P*ρ)
    (hC : C<P) (hF : F<P) (hρ : 9 ≤ ρ) : 3*(2*C+F)<q := by
  have hm := Nat.mul_le_mul_left P hρ
  nlinarith

/-- No lower bound on the quotient is needed: its successor is positive. -/
theorem quotientWitness_pos (q A : ℕ) : 0 < quotientWitness q A := by
  exact Nat.zero_lt_succ _

/-- The strict representative turns congruence into the actual quotient identity. -/
theorem quotient_transport {q A F : ℕ} (hF : F<q-1)
    (hcong : A ≡ F [MOD q-1]) :
    A = F+(quotientWitness q A-1)*(q-1) := by
  have hr : A%(q-1)=F := by
    change A%(q-1)=F%(q-1) at hcong
    simpa only [Nat.mod_eq_of_lt hF] using hcong
  have he := Nat.mod_add_div A (q-1)
  rw [hr] at he
  unfold quotientWitness
  simpa only [Nat.add_sub_cancel, Nat.mul_comm] using he.symm

/-- Signed arithmetic is the literal displayed transport factor. -/
theorem transport_factor_eq_one {q A F z : ℕ} (hq : 0<q) (hz : 0<z)
    (ht : A=F+(z-1)*(q-1)) :
    (A : ℤ)+((q : ℤ)-F)-z*((q : ℤ)-1)=1 := by
  have hh := congrArg (fun n : ℕ => (n : ℤ)) ht
  push_cast [Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_sub (by omega : 1 ≤ q)] at hh
  linarith

/-- Only the scalar conclusions actually constructed in this packet. -/
structure ScalarFacts (q C F w alpha z : ℕ) : Prop where
  q_pos : 0<q
  source_pos : 0<C
  normalized_pos : 0<F
  multiplier_pos : 0<w
  alpha_pos : 0<alpha
  quotient_pos : 0<z
  balance : C+F+alpha=q
  strong_slack : 3*(2*C+F)<q
  source_recovery : q-F-alpha=C
  signed_source_recovery : (q : ℤ)-F-alpha=C
  transport : (CurrentKernel2011.K+w)*C=F+(z-1)*(q-1)
  transport_unit : ((CurrentKernel2011.K : ℤ)+w)*C+((q : ℤ)-F)-z*((q : ℤ)-1)=1

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem q_pos : 0<q N := pow_pos (by decide : 0<radix) _

theorem q_prefix : q N=radix^(N*2011-1)*radix := by
  have hn : N*2011=(N*2011-1)+1 := by
    have := wordLength_pos (N := N)
    omega
  unfold q
  conv_lhs => rw [hn,pow_succ]

/-- Both bounds refer to the actual source and the same normalized word. -/
theorem strong_slack (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    3*(2*source a dummy marker+normalized digits)<q N := by
  have hC := source_word_bound a dummy marker hd hm
  have hp := Nat.pow_le_pow_right (n := radix) (by decide : 1≤radix)
    (show N*2011-1006 ≤ N*2011-1 by omega)
  have hF := normalized_word_top_bound a dummy marker hd hm s k digits hf
  exact slack_of_prefix q_prefix (hC.trans_le hp) hF (by decide : 9≤radix)

/-- Construct positive alpha and z from the exact words and normalization.
The only tile premise is Start at the origin; matching and high masks are
not inputs. The whole low-mask condition is supplied as a conclusion. -/
theorem scalar_witness (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (ha : a 0=0) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    ScalarFacts (q N) (source a dummy marker) (normalized digits) (multiplier s)
      (alpha (q N) (source a dummy marker) (normalized digits))
      (quotientWitness (q N) ((CurrentKernel2011.K+multiplier s)*source a dummy marker)) ∧
    (source a dummy marker-1) &&&
      (lowPort*NativeMaskPopulation.repunit width N+1)=0 := by
  have hC := (assembled_source_bounds a dummy marker hd hm ha).1
  obtain ⟨hF,hFlt⟩ := normalized_word_strict a dummy marker hd hm s k digits hf
  have hs := strong_slack a dummy marker hd hm s k digits hf
  have hab : source a dummy marker+normalized digits < q N := by omega
  have hapos : 0<alpha (q N) (source a dummy marker) (normalized digits) := by
    unfold alpha
    omega
  have hbalance : source a dummy marker+normalized digits+
      alpha (q N) (source a dummy marker) (normalized digits)=q N := by
    unfold alpha
    omega
  have ht := quotient_transport hFlt hf.transport
  have hz := quotientWitness_pos (q N)
    ((CurrentKernel2011.K+multiplier s)*source a dummy marker)
  have hu := transport_factor_eq_one (q_pos (N := N)) hz ht
  refine ⟨⟨q_pos,hC,hF,pow_pos (by decide : 0<2) _,hapos,hz,
    hbalance,hs,?_,?_,ht,?_⟩,assembled_low_mask a dummy marker hd hm ha⟩
  · omega
  · omega
  · simpa only [source,normalized,multiplier,CurrentKernel2011.radix,
      CurrentMasks2011.radix,Nat.cast_mul,Nat.cast_add] using hu

/-- No normalization or desired quotient/slack conclusion is assumed here. -/
theorem exists_scalar_witness (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (ha : a 0=0) (s : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits ∧
      ScalarFacts (q N) (source a dummy marker) (normalized digits) (multiplier s)
        (alpha (q N) (source a dummy marker) (normalized digits))
        (quotientWitness (q N) ((CurrentKernel2011.K+multiplier s)*source a dummy marker)) ∧
      (source a dummy marker-1) &&&
        (lowPort*NativeMaskPopulation.repunit width N+1)=0 := by
  obtain ⟨k,digits,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a dummy marker hd hm (displacement s)
  exact ⟨k,digits,hf,scalar_witness a dummy marker hd hm ha s k digits hf⟩

end DiophantineConsistency.CurrentWordScalarWitness2011
