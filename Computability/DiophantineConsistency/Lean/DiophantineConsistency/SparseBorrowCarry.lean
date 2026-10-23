import DiophantineConsistency.MultiTargetCarry

/-!
# Sparse +1 padding with signed borrows

A coefficient word is normalized with an explicit one-bit borrow recurrence.
The resulting monitored digits are 0 or 1 exactly when the signed coefficient
is zero. No dense half-base bias is introduced.
-/

namespace DiophantineConsistency.SparseBorrowCarry

open Polynomial Finset Jones1982
open scoped BigOperators

set_option maxRecDepth 12000
set_option maxHeartbeats 300000

/-- Incoming borrow, normalized to -1 or 0 by an explicit sign test. -/
def borrow (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i+1 => if a i+borrow a i<0 then -1 else 0

/-- The normalized integer digit. Bounds below certify that this lies in [0,B). -/
def digit (B : ℕ) (a : ℕ → ℤ) (i : ℕ) : ℤ :=
  a i+borrow a i-(B:ℤ)*borrow a (i+1)

def word (B n : ℕ) (a : ℕ → ℤ) : ℕ :=
  Nat.ofDigits B ((List.range n).map fun i => (digit B a i).toNat)

/-- The sparse padding bit is added only at monitored positions. -/
def raw (S : Finset ℕ) (h : ℕ → ℤ) (i : ℕ) : ℤ :=
  2*h i+if i∈S then 1 else 0

def value (B n : ℕ) (S : Finset ℕ) (h : ℕ → ℤ) : ℤ :=
  ∑ i∈range n, raw S h i*(B:ℤ)^i

def mask (B : ℕ) (S : Finset ℕ) : ℕ := (B-2)*∑ i∈S,B^i

def maskList (B n : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i∈S then B-2 else 0

theorem borrow_cases (a : ℕ → ℤ) (i : ℕ) : borrow a i = -1 ∨ borrow a i=0 := by
  cases i with
  | zero => simp [borrow]
  | succ i => simp only [borrow]; split_ifs <;> simp

theorem digit_bounds {B : ℕ} (_hB : 0<B) (a : ℕ → ℤ) (i : ℕ)
    (ha : -(B:ℤ)<a i ∧ a i<(B:ℤ)) : 0≤digit B a i ∧ digit B a i<(B:ℤ) := by
  have hc : -1≤borrow a i ∧ borrow a i≤0 := by
    rcases borrow_cases a i with hc | hc <;> rw [hc] <;> norm_num
  have hstep : borrow a (i+1) = if a i+borrow a i<0 then -1 else 0 := rfl
  rw [digit,hstep]
  split_ifs with hn <;> omega

/-- Coefficient magnitude controls all raw digits, including unmonitored cells. -/
theorem raw_bounds {B : ℕ} (hB : 4≤B) (S : Finset ℕ) (h : ℕ → ℤ) (i : ℕ)
    (hh : 4*|h i|<(B:ℤ)) : -(B:ℤ)<raw S h i ∧ raw S h i<(B:ℤ) := by
  have hlo := neg_abs_le (h i)
  have hhi := le_abs_self (h i)
  unfold raw
  split_ifs <;> omega

/-- The arithmetic recurrence telescopes before any nonnegativity assumption. -/
theorem digit_sum (B n : ℕ) (a : ℕ → ℤ) :
    (∑ i∈range n,digit B a i*(B:ℤ)^i)+(B:ℤ)^n*borrow a n =
      ∑ i∈range n,a i*(B:ℤ)^i := by
  induction n with
  | zero => simp [borrow]
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,pow_succ]
    rw [show digit B a n=a n+borrow a n-(B:ℤ)*borrow a (n+1) from rfl]
    linear_combination ih

/-- Casting the normalized finite word introduces no truncation in its digits. -/
theorem word_cast {B n : ℕ} (hB : 0<B) (a : ℕ → ℤ)
    (ha : ∀ i<n,-(B:ℤ)<a i ∧ a i<(B:ℤ)) :
    (word B n a:ℤ)=∑ i∈range n,digit B a i*(B:ℤ)^i := by
  rw [word,ofDigits_map_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.toNat_of_nonneg (digit_bounds hB a i (ha i (mem_range.mp hi))).1]

theorem word_lt {B n : ℕ} (hB : 1<B) (a : ℕ → ℤ)
    (ha : ∀ i<n,-(B:ℤ)<a i ∧ a i<(B:ℤ)) : word B n a<B^n := by
  unfold word
  have hd : ∀ x∈(List.range n).map (fun i => (digit B a i).toNat),x<B := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hb := digit_bounds (by omega) a i (ha i (List.mem_range.mp hi))
    exact (Int.toNat_lt hb.1).mpr (by simpa using hb.2)
  simpa using Nat.ofDigits_lt_base_pow_length hB hd

/-- A nonnegative signed value has no outstanding final borrow. -/
theorem word_eq_toNat {B n : ℕ} (hB : 1<B) (a : ℕ → ℤ)
    (ha : ∀ i<n,-(B:ℤ)<a i ∧ a i<(B:ℤ))
    (hvalue : 0≤∑ i∈range n,a i*(B:ℤ)^i) :
    word B n a=(∑ i∈range n,a i*(B:ℤ)^i).toNat := by
  have hs := digit_sum B n a
  rw [← word_cast (by omega) a ha] at hs
  have hlt : (word B n a:ℤ)<(B:ℤ)^n := by exact_mod_cast word_lt hB a ha
  have hc : borrow a n=0 := by
    rcases borrow_cases a n with hc | hc
    · rw [hc] at hs
      nlinarith only [hs,hlt,hvalue]
    · exact hc
  rw [hc,mul_zero,add_zero] at hs
  rw [← hs,Int.toNat_natCast]

/-- At a marked cell the only mask-free digits are exactly the zero coefficient. -/
theorem marked_digit_lt_two_iff {B : ℕ} (hB : 4≤B) (S : Finset ℕ) (h : ℕ → ℤ)
    (i : ℕ) (hi : i∈S) (hh : 4*|h i|<(B:ℤ)) :
    (digit B (raw S h) i).toNat<2 ↔ h i=0 := by
  have hb := digit_bounds (by omega) (raw S h) i (raw_bounds hB S h i hh)
  rw [Int.toNat_lt hb.1]
  have hc : -1≤borrow (raw S h) i ∧ borrow (raw S h) i≤0 := by
    rcases borrow_cases (raw S h) i with hc | hc <;> rw [hc] <;> norm_num
  have hlo := neg_abs_le (h i)
  have hhi := le_abs_self (h i)
  have hraw : raw S h i=2*h i+1 := by simp only [raw,if_pos hi]
  unfold digit
  rw [show borrow (raw S h) (i+1) =
    if raw S h i+borrow (raw S h) i<0 then -1 else 0 from rfl,hraw]
  split_ifs with hn <;> push_cast <;> omega

private theorem map_range_getD (f : ℕ → ℕ) {n i : ℕ} (hi : i<n) :
    ((List.range n).map f).getD i 0=f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem maskList_value (B n : ℕ) (S : Finset ℕ) (hS : ∀ i∈S,i<n) :
    Nat.ofDigits B (maskList B n S)=mask B S := by
  rw [maskList,ofDigits_map_range]
  simp only [ite_mul,zero_mul]
  rw [← Finset.sum_filter]
  have hs : (range n).filter (fun i => i∈S)=S := by
    ext i
    simp only [mem_filter,mem_range]
    exact ⟨fun h => h.2,fun hi => ⟨hS i hi,hi⟩⟩
  rw [hs,mask,Finset.mul_sum]

/-- Generic finite signed-word decoder, with sparse +1 padding and B-2 mask. -/
theorem tau_sparse_iff {B t n : ℕ} (hB : B=2^t) (ht : 2≤t)
    (S : Finset ℕ) (hS : ∀ i∈S,i<n) (h : ℕ → ℤ)
    (hh : ∀ i<n,4*|h i|<(B:ℤ)) (hvalue : 0≤value B n S h) :
    τ 2 (value B n S h).toNat (mask B S)=0 ↔ ∀ i∈S,h i=0 := by
  have hB4 : 4≤B := by
    rw [hB]
    calc 4=2^2 := rfl
         _≤2^t := Nat.pow_le_pow_right (by decide) ht
  have hB1 : 1<B := by omega
  have ha : ∀ i<n,-(B:ℤ)<raw S h i ∧ raw S h i<(B:ℤ) :=
    fun i hi => raw_bounds hB4 S h i (hh i hi)
  have hword := word_eq_toNat hB1 (raw S h) ha hvalue
  change word B n (raw S h)=(value B n S h).toNat at hword
  rw [← hword,← maskList_value B n S hS]
  have hd : ∀ x∈(List.range n).map (fun i => (digit B (raw S h) i).toNat),x<B := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hb := digit_bounds (by omega) (raw S h) i (ha i (List.mem_range.mp hi))
    exact (Int.toNat_lt hb.1).mpr (by simpa using hb.2)
  have hm : ∀ x∈maskList B n S,x<B := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    split_ifs <;> omega
  rw [word,tau_ofDigits_iff (n:=n) hB hd hm (by simp) (by simp [maskList])]
  constructor
  · intro htau i hi
    have hc := htau i (hS i hi)
    rw [map_range_getD _ (hS i hi),maskList,map_range_getD _ (hS i hi),if_pos hi] at hc
    have hdB : (digit B (raw S h) i).toNat<2^t := by rw [← hB]; exact hd _ (List.mem_map.mpr ⟨i,List.mem_range.mpr (hS i hi),rfl⟩)
    rw [τ_comm] at hc
    have hsmall : (digit B (raw S h) i).toNat<2 :=
      (lemma_2_7 (k:=1) (K:=t) (by omega) hdB).mpr (by simpa only [pow_one,hB] using hc)
    exact (marked_digit_lt_two_iff hB4 S h i hi (hh i (hS i hi))).mp hsmall
  · intro hz i hi
    rw [map_range_getD _ hi,maskList,map_range_getD _ hi]
    by_cases hip : i∈S
    · rw [if_pos hip]
      have hsmall := (marked_digit_lt_two_iff hB4 S h i hip (hh i hi)).mpr (hz i hip)
      rw [τ_comm]
      have hdB : (digit B (raw S h) i).toNat<2^t := by
        rw [← hB]
        exact hd _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
      have hc := (lemma_2_7 (k:=1) (K:=t) (by omega) hdB).mp hsmall
      simpa only [pow_one,← hB] using hc
    · rw [if_neg hip]
      exact τ_zero_right _

/-- The finite signed word is the full polynomial value plus sparse padding. -/
theorem value_eq_polynomial (B n : ℕ) (S : Finset ℕ) (hS : ∀ i∈S,i<n)
    (p : ℤ[X]) (hp : p.natDegree<n) :
    value B n S p.coeff=2*p.eval (B:ℤ)+∑ i∈S,(B:ℤ)^i := by
  have hs : (range n).filter (fun i => i∈S)=S := by
    ext i
    simp only [mem_filter,mem_range]
    exact ⟨fun h => h.2,fun hi => ⟨hS i hi,hi⟩⟩
  calc
    value B n S p.coeff = 2*(∑ i∈range n,p.coeff i*(B:ℤ)^i)+
        ∑ i∈range n,if i∈S then (B:ℤ)^i else 0 := by
      unfold value raw
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _=2*p.eval (B:ℤ)+∑ i∈S,(B:ℤ)^i := by
      rw [← eval_eq_sum_range' hp,← Finset.sum_filter,hs]

/-- The exact polynomial form of the sparse +1 decoder. The strict quarter-base
bound covers every coefficient, including unmonitored collisions. -/
theorem tau_polynomial_iff {B t n : ℕ} (hB : B=2^t) (ht : 2≤t)
    (S : Finset ℕ) (hS : ∀ i∈S,i<n) (p : ℤ[X]) (hp : p.natDegree<n)
    (hh : ∀ i<n,|p.coeff i|<(B:ℤ)/4)
    (hvalue : 0≤2*p.eval (B:ℤ)+∑ i∈S,(B:ℤ)^i) :
    τ 2 (2*p.eval (B:ℤ)+∑ i∈S,(B:ℤ)^i).toNat ((B-2)*∑ i∈S,B^i)=0 ↔
      ∀ i∈S,p.coeff i=0 := by
  have hb : ∀ i<n,4*|p.coeff i|<(B:ℤ) := by
    intro i hi
    have h := hh i hi
    omega
  have hv : 0≤value B n S p.coeff := by rw [value_eq_polynomial B n S hS p hp]; exact hvalue
  have h := tau_sparse_iff hB ht S hS p.coeff hb hv
  simpa only [value_eq_polynomial B n S hS p hp,mask] using h

end DiophantineConsistency.SparseBorrowCarry
