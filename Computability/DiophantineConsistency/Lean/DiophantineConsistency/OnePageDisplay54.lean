import DiophantineConsistency.OnePageTuple54
import DiophantineConsistency.NativeHighPort54
import Mathlib.Algebra.Field.GeomSum

/-! # The literal geometric and rational coefficient display on the one-page equation -/

namespace DiophantineConsistency.OnePageDisplay54

open scoped BigOperators
open OnePageTuple54 OnePageModes54

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The page's fixed finite geometric sum. -/
def G (m : ℕ) (x : ℚ) : ℚ := ∑ j ∈ Finset.range m, x^j

theorem geometric_fraction (m : ℕ) {x : ℚ} (hx : x ≠ 1) :
    G m x = (x^m-1)/(x-1) := geom_sum_eq hx m

/-- A finite ordinary polynomial specified by natural coefficient-position pairs. -/
def entryValue (l : List (ℕ × ℕ)) (x : ℚ) : ℚ :=
  (l.map fun p => (p.2 : ℚ)*x^p.1).sum

theorem entryValue_append (l₁ l₂ : List (ℕ × ℕ)) (x : ℚ) :
    entryValue (l₁++l₂) x = entryValue l₁ x + entryValue l₂ x := by
  simp only [entryValue,List.map_append,List.sum_append]

theorem target_factor {r : ℚ} (hr : r ≠ 0) (T : ℕ)
    (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 ≤ T) :
    r^T * entryValue l r⁻¹ = (l.map fun p => (p.2 : ℚ)*r^(T-p.1)).sum := by
  induction l with
  | nil => simp only [entryValue,List.map_nil,List.sum_nil,mul_zero]
  | cons p l ih =>
    simp only [entryValue,List.map_cons,List.sum_cons,mul_add] at *
    rw [ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    rw [pow_sub₀ r hr (hl p (List.mem_cons_self)),inv_pow]
    ring

private theorem block_value (m a c : ℕ) (x : ℚ) :
    entryValue ((List.range m).map fun j => (a+j,c*2^j)) x =
      (c : ℚ)*x^a*G m (2*x) := by
  unfold entryValue
  rw [List.map_map]
  change ((List.range m).map fun j => ((c*2^j : ℕ) : ℚ)*x^(a+j)).sum = _
  rw [← List.sum_toFinset _ (show (List.range m).Nodup from List.nodup_range)]
  simp only [List.toFinset_range,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add,
    mul_pow,G,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem anchored_block (m a c d : ℕ) (hm : 0 < m) (x : ℚ) :
    entryValue ((List.range m).map fun j => (a+j,c*2^j+(if j=0 then d else 0))) x =
      (c : ℚ)*x^a*G m (2*x)+(d : ℚ)*x^a := by
  unfold entryValue
  rw [List.map_map]
  change ((List.range m).map fun j =>
    ((c*2^j+(if j=0 then d else 0) : ℕ) : ℚ)*x^(a+j)).sum = _
  rw [← List.sum_toFinset _ (show (List.range m).Nodup from List.nodup_range)]
  simp only [List.toFinset_range,Nat.cast_add,add_mul,Finset.sum_add_distrib]
  have hb := block_value m a c x
  unfold entryValue at hb
  rw [List.map_map] at hb
  change ((List.range m).map fun j => ((c*2^j : ℕ) : ℚ)*x^(a+j)).sum = _ at hb
  rw [← List.sum_toFinset _ (show (List.range m).Nodup from List.nodup_range)] at hb
  simp only [List.toFinset_range] at hb
  rw [hb]
  congr 1
  simp only [Nat.cast_ite,Nat.cast_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_range,hm,if_true,Nat.add_zero]

/-- The auxiliary part of the compact Phi printed on the page. -/
def auxiliaryPhi (x : ℚ) : ℚ :=
  2^29 * ((x^539+2^21*x^517)*G 11 (2*x) +
    (2^11*x^528+2^32*x^495)*G 10 (2*x) +
    2^42*(x^539+x^1203+x^1807)) +
  ((2^9+2^29*(2+2^33))*x^567 +
    (2^18+2^29*(2^22+2^33))*x^575)*G 8 (2*x) +
  (2^27+2^29*(2^11+2^32))*x^583

private theorem auxiliaryEntries_blocks : auxiliaryEntries =
    ((List.range 11).map fun j => (539+j,2^29*2^j+(if j=0 then 2^71 else 0))) ++
    ((List.range 10).map fun j => (528+j,2^40*2^j)) ++
    ((List.range 11).map fun j => (517+j,2^50*2^j)) ++
    ((List.range 10).map fun j => (495+j,2^61*2^j)) ++
    ((List.range 8).map fun j => (567+j,(2^9+2^29*(2+2^33))*2^j)) ++
    ((List.range 8).map fun j => (575+j,(2^18+2^29*(2^22+2^33))*2^j)) ++
    [(583,2^27+2^29*(2^11+2^32)),(1203,2^71),(1807,2^71),(507,0),(508,0)] := by
  simp only [auxiliaryEntries,pow_add]

theorem auxiliaryPhi_eq (x : ℚ) : auxiliaryPhi x = entryValue auxiliaryEntries x := by
  rw [auxiliaryEntries_blocks]
  simp only [entryValue_append]
  rw [anchored_block 11 539 (2^29) (2^71) (by decide),
    block_value 10 528 (2^40),block_value 11 517 (2^50),block_value 10 495 (2^61),
    block_value 8 567 _,block_value 8 575 _]
  simp only [entryValue,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,
    Nat.cast_zero,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  unfold auxiliaryPhi
  ring

/-- This is exactly the page's rational Phi expression, including its signed c_i. -/
def Phi (x : ℚ) : ℚ :=
  (∑ i : Fin 457, (integerCoefficient i : ℚ)*x^(arithmeticRank i))+auxiliaryPhi x

attribute [local irreducible] auxiliaryEntries integerCoefficient coefficient arithmeticRank
  OnePageModes54.unsortedMode NativeModesData54.mode NativeModesData54.modeList

private theorem coefficient_cast (i : Fin 457) :
    (integerCoefficient i : ℚ) = (coefficient i : ℚ) := by
  rw [integerCoefficient_eq,coefficient_eq]
  norm_cast

private theorem auxiliary_positions (p : ℕ × ℕ) (hp : p ∈ auxiliaryEntries) : p.1 ≤ 1807 := by
  have h : auxiliaryEntries.all (fun q => decide (q.1 ≤ 1807)) = true := by
    unfold auxiliaryEntries
    rfl
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

private theorem selector_factor {r : ℚ} (hr : r ≠ 0) {T : ℕ} (hT : 457 ≤ T) :
    r^T * (∑ i : Fin 457, (integerCoefficient i : ℚ)*r⁻¹^(arithmeticRank i)) =
      ∑ i : Fin 457, (coefficient i : ℚ)*r^(T-arithmeticRank i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficient_cast,pow_sub₀ r hr (by have h := arithmeticRank_lt i; omega),inv_pow]
  ring

def displayedK (r : ℚ) : ℚ :=
  r^33+r^68+r^664+r^1268+r^4877+(r^2409+r^3015)*Phi r⁻¹

theorem displayedK_eq (r : ℕ) (hr : r ≠ 0) :
    displayedK r = (NativeStencil54.rawWord r : ℚ) := by
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  rw [← stencilWord_eq_rawWord]
  unfold displayedK Phi
  rw [auxiliaryPhi_eq,add_mul,mul_add,mul_add,
    selector_factor hr' (by decide : 457 ≤ 2409),
    selector_factor hr' (by decide : 457 ≤ 3015),
    target_factor hr' 2409 _ (fun p hp => le_trans (auxiliary_positions p hp) (by decide)),
    target_factor hr' 3015 _ (fun p hp => le_trans (auxiliary_positions p hp) (by decide))]
  simp only [stencilWord,selectorWord,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_sum,Nat.cast_list_sum,List.map_map,Function.comp_def]
  have hl (l : List (ℕ × ℕ)) :
      (l.map (fun p => (p.2 : ℚ)*(r:ℚ)^(2409-p.1))).sum +
      (l.map (fun p => (p.2 : ℚ)*(r:ℚ)^(3015-p.1))).sum =
      (l.map (fun p => (p.2 : ℚ)*((r:ℚ)^(2409-p.1)+(r:ℚ)^(3015-p.1)))).sum := by
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons]; rw [mul_add]; linarith
  rw [← hl auxiliaryEntries]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

/-- The exact interval union S printed on the page, as a finite list. -/
def displayPositions : List ℕ :=
  List.range 457 ++ ((List.range 10).map (495+·)) ++ [507,508] ++
  ((List.range 21).map (517+·)) ++ ((List.range 11).map (539+·)) ++
  ((List.range 17).map (567+·)) ++ [1203,1807]

def support : Finset ℕ := displayPositions.toFinset

theorem displayPositions_perm : assignmentPositions.Perm displayPositions := by
  have h21 : ((List.range 21).map (517+·)) =
      ((List.range 11).map (517+·)) ++ ((List.range 10).map (528+·)) := by rfl
  have h17 : ((List.range 17).map (567+·)) =
      ((List.range 8).map (567+·)) ++ ((List.range 8).map (575+·)) ++ [583] := by rfl
  apply List.perm_iff_count.mpr
  intro x
  simp only [displayPositions,h21,h17,assignmentPositions,List.count_append,
    List.count_cons,List.count_nil]
  omega

attribute [local irreducible] assignmentPositions displayPositions support

theorem support_eq : support = assignmentPositions.toFinset := by
  unfold support
  ext e
  simp only [List.mem_toFinset]
  exact displayPositions_perm.mem_iff.symm

private theorem mem_block (a m e : ℕ) :
    e ∈ ((List.range m).map (a+·)) ↔ a ≤ e ∧ e < a+m := by
  simp only [List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨e-a,by omega,by omega⟩

/-- Exactly the set union S displayed on the page. -/
theorem support_recipe : support =
    Finset.Icc 0 456 ∪ Finset.Icc 495 504 ∪ {507,508} ∪
    Finset.Icc 517 537 ∪ Finset.Icc 539 549 ∪
    Finset.Icc 567 583 ∪ {1203,1807} := by
  ext e
  simp only [support,displayPositions,List.mem_toFinset,List.mem_append,List.mem_range,
    mem_block,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton]
  omega

private theorem cleared_sum (r : ℕ) :
    (∑ e ∈ support.erase 1, (r : ℚ)^e) =
      ((((assignmentPositions.filter (fun e => e != 1)).map fun e => r^e).sum : ℕ) : ℚ) := by
  have he : support.erase 1 = (assignmentPositions.filter (fun e => e != 1)).toFinset := by
    rw [support_eq]
    ext e
    simp [and_comm]
  rw [he,List.sum_toFinset _ (assignmentPositions_nodup.filter _)]
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_pow]

def displayedMC (r : ℚ) : ℚ :=
  r^4831-1-(∑ e ∈ support.erase 1, r^e)-2*r^507

/-- The ordinary rational subtraction on the page is exactly the nonnegative
native MC. Its proof uses the native exact subtraction theorem. -/
theorem displayedMC_eq : displayedMC NativeStencil54.radix = (NativeLowPort54.lowPort : ℚ) := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) NativeLowPort54.lowPort_exact
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow] at h
  have hm : (NativeLowPort54.removedWord NativeStencil54.radix : ℚ) =
      (∑ e ∈ support.erase 1, (NativeStencil54.radix : ℚ)^e)+
        2*(NativeStencil54.radix : ℚ)^507 := by
    unfold NativeLowPort54.removedWord NativeLowPort54.positions
    rw [← assignmentPositions_eq]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,cleared_sum]
  rw [hm] at h
  unfold displayedMC NativeStencil54.cellLength at *
  linarith

/-- The literal clause-mask coefficient mu printed on the page. -/
def mu : ℕ := 510+2^17+2^26+2^28+2^29*(2^44-1)

theorem mu_eq : mu = NativeClause54.clauseMask := NativeClause54.clauseMask_eq.symm

private theorem geometric_cast (r m : ℕ) :
    (NativeHighPort54.geometric r m : ℚ) = G m r := by
  simp only [NativeHighPort54.geometric,G,Nat.cast_sum,Nat.cast_pow]

def displayedBeta (r : ℚ) : ℚ := r^4831-1

def displayedMF (r : ℚ) : ℚ :=
  displayedBeta r+4+(mu : ℚ)*(r^2409+r^3015)+
    r^528*G 10 r+r^585*G 11 r+r^1203+r^1807+
    (2^87-1)*r^4823*G 4 r+(2^38-1)*r^4827

/-- MF on the page contains beta once in addition to the native high mask. -/
theorem displayedMF_eq (r : ℕ) :
    displayedMF r = displayedBeta r+(NativeHighPort54.highPort r : ℚ) := by
  have h87 : ((2^87-1 : ℕ) : ℚ) = 2^87-1 := by norm_num
  have h38 : ((2^38-1 : ℕ) : ℚ) = 2^38-1 := by norm_num
  rw [NativeHighPort54.highPort_recipe]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,geometric_cast,
    h87,h38,← mu_eq]
  unfold displayedMF
  ring

theorem displayedBeta_eq {r : ℕ} (hr : 1 ≤ r) :
    displayedBeta r = ((r^4831-1 : ℕ) : ℚ) := by
  have hp : 1 ≤ r^4831 := one_le_pow₀ hr
  simp only [displayedBeta,Nat.cast_sub hp,Nat.cast_pow,Nat.cast_one]

/-- The beta shift is an exact ordinary integer sum for every positive radix. -/
theorem displayedMF_source_eq {r : ℕ} (hr : 1 ≤ r) :
    displayedMF r = ((r^4831-1+NativeHighPort54.highPort r : ℕ) : ℚ) := by
  rw [displayedMF_eq,displayedBeta_eq hr]
  simp only [Nat.cast_add]

/-- All four displayed coefficients use the same whole compact54 tuple. -/
theorem displayedMF_source : displayedMF NativeStencil54.radix =
    ((NativeStencil54.radix^NativeStencil54.cellLength-1+
      NativeHighPort54.highPort NativeStencil54.radix : ℕ) : ℚ) := by
  simpa only [NativeStencil54.cellLength] using
    displayedMF_source_eq (by decide : 1 ≤ NativeStencil54.radix)

end DiophantineConsistency.OnePageDisplay54
