import DiophantineConsistency.DegreeSeparatedCoding
import DiophantineConsistency.MaskPopulation
import DiophantineConsistency.SparseBorrowCarry
import DiophantineConsistency.SplitCoefficientBounds

/-!
# The two-block contract for degree-separated source words

All hypotheses are numerical bounds or explicit polynomial evaluation
identities. No source predicate or machine interpretation occurs here.
-/

namespace DiophantineConsistency.SplitCarry

open Polynomial Finset Jones1982
open scoped BigOperators

set_option maxRecDepth 12000
set_option maxHeartbeats 300000

/-- The low code and nonnegative signed high word, separated by one base block. -/
def word (B len g : ℕ) (J : ℤ) : ℕ := g+B^len*J.toNat

def packedMask {m : ℕ} (B b len : ℕ) (w : Fin m → ℕ) (targets : Finset ℕ) : ℕ :=
  LowMaskCoding.indexedMask B b len w+B^len*SparseBorrowCarry.mask B targets

/-- The same mask as the independently population-counted literal expression. -/
theorem packedMask_eq {m : ℕ} (B b len : ℕ) (w : Fin m → ℕ) (targets : Finset ℕ) :
    packedMask B b len w targets=
      MaskPopulation.packedMask B b len (LowMaskCoding.positions w) targets := by
  unfold packedMask MaskPopulation.packedMask LowMaskCoding.indexedMask
    SparseBorrowCarry.mask MaskPopulation.highMask
  ring

theorem lowMask_lt {m B b len k t : ℕ} (w : Fin m → ℕ) (hw : ∀ i,w i<len)
    (hb : b=2^k) (hB : B=2^t) (ht : 1≤t) (hbB : b≤B) :
    LowMaskCoding.indexedMask B b len w<B^len := by
  have hkt : k≤t := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [← hb,← hB] using hbB
  simpa only [LowMaskCoding.indexedMask,hb,hB] using
    MaskPopulation.low_mask_lt ht hkt (LowMaskCoding.positions w) (LowMaskCoding.positions_subset hw)

/-- Binary disjointness splits using only the low-word ranges. -/
theorem tau_word_iff {m B b len g k t : ℕ} (w : Fin m → ℕ) (hw : ∀ i,w i<len)
    (hb : b=2^k) (hB : B=2^t) (ht : 1≤t) (hbB : b≤B) (hg : g<B^len)
    (J : ℤ) (targets : Finset ℕ) :
    τ 2 (word B len g J) (packedMask B b len w targets)=0 ↔
      τ 2 g (LowMaskCoding.indexedMask B b len w)=0 ∧
        τ 2 J.toNat (SparseBorrowCarry.mask B targets)=0 := by
  have hpow : B^len=2^(t*len) := by rw [hB,pow_mul]
  have hlow := lowMask_lt w hw hb hB ht hbB
  have h := SelectiveCarry.tau_packTwo_iff (ell:=t*len)
    (by rw [← hpow]; exact hg) (by rw [← hpow]; exact hlow)
    J.toNat (SparseBorrowCarry.mask B targets)
  simpa only [word,packedMask,SelectiveCarry.packTwo,hpow,mul_comm] using h

theorem tau_low_iff {m B b len g k t : ℕ} (w : Fin m → ℕ)
    (hw : Function.Injective w) (hwlen : ∀ i,w i<len)
    (hb : b=2^k) (hB : B=2^t) (ht : 1≤t) (hbB : b≤B) (hg : g<B^len) :
    τ 2 g (LowMaskCoding.indexedMask B b len w)=0 ↔
      ∃ z : Fin m → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z := by
  have hB1 : 1<B := by rw [hB]; exact Nat.one_lt_two_pow_iff.mpr (by omega)
  have h := LowMaskCoding.indexed_mask_code_iff hw hwlen hb hB hB1 hbB (g:=g)
  constructor
  · intro hz
    exact h.mp ⟨hg,(τ_two_eq_zero_iff _ _).mp hz⟩
  · intro hz
    exact (τ_two_eq_zero_iff _ _).mpr (h.mpr hz).2

/-- A fixed high polynomial can be decoded jointly with the bounded low digits. -/
theorem tau_polynomial_iff {m B b lowLen highLen g k t : ℕ}
    (w : Fin m → ℕ) (hw : Function.Injective w) (hwlen : ∀ i,w i<lowLen)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^lowLen)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<highLen)
    (p : ℤ[X]) (hp : p.natDegree<highLen)
    (hc : ∀ i<highLen,|p.coeff i|<(B:ℤ)/4)
    (hJ : 0≤2*p.eval (B:ℤ)+∑ i∈targets,(B:ℤ)^i) :
    τ 2 (word B lowLen g (2*p.eval (B:ℤ)+∑ i∈targets,(B:ℤ)^i))
      (packedMask B b lowLen w targets)=0 ↔
      ∃ z : Fin m → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ i∈targets,p.coeff i=0 := by
  rw [tau_word_iff w hwlen hb hB (by omega) hbB hg,
    tau_low_iff w hw hwlen hb hB (by omega) hbB hg,SparseBorrowCarry.mask,
    SparseBorrowCarry.tau_polynomial_iff hB ht targets hTargets p hp hc hJ]
  constructor
  · rintro ⟨⟨z,hz,hcode⟩,hcoeff⟩
    exact ⟨z,hz,hcode,hcoeff⟩
  · rintro ⟨z,hz,hcode,hcoeff⟩
    exact ⟨⟨z,hz,hcode⟩,hcoeff⟩

/-- A polynomial family depending on decoded digits needs only its explicit
high-word evaluation identity and coefficient/degree bounds on bounded digits. -/
theorem tau_family_iff {m B b lowLen highLen g k t : ℕ}
    (w : Fin m → ℕ) (hw : Function.Injective w) (hwlen : ∀ i,w i<lowLen)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^lowLen)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<highLen)
    (P : (Fin m → ℕ) → ℤ[X])
    (hp : ∀ z,(∀ i,z i<b) → (P z).natDegree<highLen)
    (hc : ∀ z,(∀ i,z i<b) → ∀ i<highLen,|(P z).coeff i|<(B:ℤ)/4)
    (J : ℤ) (hJ : 0≤J)
    (heval : ∀ z,(∀ i,z i<b) → g=LowMaskCoding.indexedCode B w z →
      J=2*(P z).eval (B:ℤ)+∑ i∈targets,(B:ℤ)^i) :
    τ 2 (word B lowLen g J) (packedMask B b lowLen w targets)=0 ↔
      ∃ z : Fin m → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ i∈targets,(P z).coeff i=0 := by
  rw [tau_word_iff w hwlen hb hB (by omega) hbB hg]
  constructor
  · rintro ⟨hlow,hhigh⟩
    obtain ⟨z,hz,hcode⟩ := (tau_low_iff w hw hwlen hb hB (by omega) hbB hg).mp hlow
    have he := heval z hz hcode
    rw [he] at hhigh
    refine ⟨z,hz,hcode,?_⟩
    exact (SparseBorrowCarry.tau_polynomial_iff hB ht targets hTargets (P z) (hp z hz)
      (hc z hz) (by rw [← he]; exact hJ)).mp hhigh
  · rintro ⟨z,hz,hcode,hcoeff⟩
    refine ⟨(tau_low_iff w hw hwlen hb hB (by omega) hbB hg).mpr ⟨z,hz,hcode⟩,?_⟩
    have he := heval z hz hcode
    rw [he]
    exact (SparseBorrowCarry.tau_polynomial_iff hB ht targets hTargets (P z) (hp z hz)
      (hc z hz) (by rw [← he]; exact hJ)).mpr hcoeff

/-- A decoded low word plus the fixed +1 digits is exactly the positive word. -/
theorem eval_encoded_add_one {m : ℕ} (B : ℕ) (w : Fin (m+1) → ℕ)
    (z : Fin (m+1) → ℕ) :
    (SelectiveQuadraticCoding.encoded w (fun i => (z i:ℤ)+1)).eval (B:ℤ)=
      (∑ i,(B:ℤ)^w i)+(LowMaskCoding.indexedCode B w z:ℤ) := by
  simp only [SelectiveQuadraticCoding.encoded,eval_finsetSum,eval_monomial]
  unfold LowMaskCoding.indexedCode
  push_cast
  simp_rw [add_mul,one_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- The generic split-kernel high integer, with no source interpretation. -/
noncomputable def highInt {m : ℕ} (B g : ℕ) (w : Fin (m+1) → ℕ)
    (D0 D1 D2 : ℤ[X]) (targets : Finset ℕ) : ℤ :=
  let U := (∑ i,(B:ℤ)^w i)+(g:ℤ)
  2*(U^2*D2.eval (B:ℤ)+U*D1.eval (B:ℤ)+D0.eval (B:ℤ))+∑ i∈targets,(B:ℤ)^i

theorem highInt_eq_eval_product {m B g : ℕ} (w : Fin (m+1) → ℕ)
    (D0 D1 D2 : ℤ[X]) (targets : Finset ℕ) (z : Fin (m+1) → ℕ)
    (hcode : g=LowMaskCoding.indexedCode B w z) :
    highInt B g w D0 D1 D2 targets=
      2*(SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).eval (B:ℤ)+
        ∑ i∈targets,(B:ℤ)^i := by
  simp only [highInt,SplitCoefficientBounds.product,eval_add,eval_mul,eval_pow,
    eval_encoded_add_one,← hcode]

/-- The split-kernel specialization derives the required coefficient magnitude
from the 31 bounded positive digits and the generic 993 bound. -/
theorem tau_product_iff_31 {B b lowLen highLen g k t : ℕ}
    (w : Fin 31 → ℕ) (hw : Function.Injective w) (hwlen : ∀ i,w i<lowLen)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^lowLen)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<highLen)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t)
    (hp : ∀ z : Fin 31 → ℕ,(∀ i,z i<b) →
      (SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).natDegree<highLen)
    (hJ : 0≤highInt B g w D0 D1 D2 targets) :
    τ 2 (word B lowLen g (highInt B g w D0 D1 D2 targets))
      (packedMask B b lowLen w targets)=0 ↔
      ∃ z : Fin 31 → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ i∈targets,(SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).coeff i=0 := by
  have hBint : (B:ℤ)=(2:ℤ)^t := by exact_mod_cast hB
  apply tau_family_iff w hw hwlen hb hB ht hbB hg targets hTargets
    (fun z => SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2) hp
  · intro z hz i _
    have hbound := SplitCoefficientBounds.quarter_base_div_bound_31 w
      (fun i => z i+1) D0 D1 D2 hH hD0 hD1 hD2
        (show 0<b by rw [hb]; positivity) ht (fun i => by have h:=hz i; omega) hbase i
    simpa only [Nat.cast_add,Nat.cast_one,hBint] using hbound
  · exact hJ
  · intro z _ hcode
    exact highInt_eq_eval_product w D0 D1 D2 targets z hcode

/-- Exact external population calibration turns the same two-block contract
into a central-binomial divisibility test. All range assumptions stay explicit. -/
theorem calibrated_family_iff {m B b lowLen highLen g k t u v : ℕ}
    (w : Fin m → ℕ) (hw : Function.Injective w) (hwlen : ∀ i,w i<lowLen)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^lowLen)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<highLen)
    (P : (Fin m → ℕ) → ℤ[X])
    (hp : ∀ z,(∀ i,z i<b) → (P z).natDegree<highLen)
    (hc : ∀ z,(∀ i,z i<b) → ∀ i<highLen,|(P z).coeff i|<(B:ℤ)/4)
    (J : ℤ) (hJ : 0≤J)
    (heval : ∀ z,(∀ i,z i<b) → g=LowMaskCoding.indexedCode B w z →
      J=2*(P z).eval (B:ℤ)+∑ i∈targets,(B:ℤ)^i)
    (hword : word B lowLen g J<2^u)
    (hcal : u+σ 2 (packedMask B b lowLen w targets)=2*v) :
    (2^v)^2 ∣ (2*ReducedRankCarry.rank (2^u) (word B lowLen g J)
      (packedMask B b lowLen w targets)).choose
        (ReducedRankCarry.rank (2^u) (word B lowLen g J) (packedMask B b lowLen w targets)) ↔
      ∃ z : Fin m → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ i∈targets,(P z).coeff i=0 :=
  (ReducedRankCarry.calibrated_iff hword hcal).trans
    (tau_family_iff w hw hwlen hb hB ht hbB hg targets hTargets P hp hc J hJ heval)

end DiophantineConsistency.SplitCarry
