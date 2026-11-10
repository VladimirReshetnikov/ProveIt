import DiophantineConsistency.Source34.Source34CleanCarry
import DiophantineConsistency.Mixed121.Mixed121Single
import Mathlib.Tactic.FinCases

/-! # One decoded clause band at the clean target, at the source34 ports

`Mixed121Single` at the source34 tuple. The geometry is re-established for the
source34 offsets; the hull is still `Mixed121Clean.Bad`.

* `Allowed` now covers the tile rows, the stride-two copy range `960..1038`
  (it contains every copy position `960 + 2u`) and the anchors. The foreign
  sources `t ∓ 1102 + j` of an allowed `j` avoid the hull (`shifted_safe`,
  by `omega`): `j − 1102 mod 8801` lands in `7699..8641` (rows), `8659..8737`
  (copies), `8794, 8795, 1093, 2194` (anchors), and `j + 1102` in
  `1102..2044`, `2062..2140`, `2197, 2198, 3297, 4398`.
* The bare offsets are `40, 41, 1100, 2200, 8802`; their sources at
  `4393` are `4353, 4352, 3293, 2193, 4392` and at `5495` are
  `5455, 5454, 4395, 3295, 5494`, all outside the hull (`bare_safe`).

`Mixed121Single.source_zero` is generic and used directly. `foreign`, `bare`,
`foreign_and_bare`, `decoderBand` (with the source34 copy digits) and
`graph_single_band` are re-declared. The finite facts were first checked
by an exhaustive scan outside Lean; here they are proved by `omega` and
`norm_num`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Single
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open ArithmeticStandardCasts CompactHeterogeneousCarry CompactGenericAlignedMass
open Source34Rotation Source34Flatten ModelDigitTransfer
open Mixed121Rotation (selectorOffset coefficient word cap)
open Mixed121Flatten (selectors copies)
open Mixed121Clean (BadNat Bad bad_cast)

/-- Support positions of either source34 band: tile rows, the copy range and
anchors. -/
def Allowed (j : ℕ) : Prop :=
  j<943 ∨ (960≤j ∧ j≤1038) ∨ j=1095 ∨ j=1096 ∨ j=2195 ∨ j=3296

theorem shifted_safe (j : ℕ) (hj : Allowed j) :
    ¬BadNat ((4393+8801-(5495-j)%8801)%8801) ∧
    ¬BadNat ((5495+8801-(4393-j)%8801)%8801) := by
  unfold Allowed at hj
  unfold BadNat
  omega

theorem extra_allowed : ∀ j ∈ Source34Kernel.extraPositions, Allowed j := by
  intro j hj
  unfold Source34Kernel.extraPositions at hj
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  unfold Allowed
  rcases hj with ((((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | h) <;> omega

theorem copy_allowed (k : Fin 44) : Allowed (Source34Kernel.extraPos k) :=
  extra_allowed _ (List.get_mem _ _)

theorem bare_safe (j : Fin 5) :
    ¬BadNat ((4393+8801-(![40,41,1100,2200,8802] j)%8801)%8801) ∧
    ¬BadNat ((5495+8801-(![40,41,1100,2200,8802] j)%8801)%8801) := by
  fin_cases j <;> norm_num [BadNat]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

private theorem cyc_cast (t q : ℕ) :
    cyc (8801:V) (t:V) (q:V) = (((t+8801-q%8801)%8801:ℕ):V) := by
  have hle : q%8801≤t+8801 := by have := Nat.mod_lt q (by omega : 0<8801); omega
  have hc : ((t+8801-q%8801:ℕ):V)=(t:V)+8801-((q%8801:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8801 = ((q%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8801).symm
  unfold cyc
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8801-q%8801) 8801).symm

theorem foreign (j : ℕ) (hj : Allowed j) :
    ¬Bad (cyc 8801 4393 (((5495-j):ℕ):V)) ∧
    ¬Bad (cyc 8801 5495 (((4393-j):ℕ):V)) := by
  have hf := shifted_safe j hj
  have h1 : cyc (8801:V) 4393 (((5495-j):ℕ):V) =
      (((4393+8801-(5495-j)%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 4393 (5495-j))
  have h2 : cyc (8801:V) 5495 (((4393-j):ℕ):V) =
      (((5495+8801-(4393-j)%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 5495 (4393-j))
  rw [h1,h2,bad_cast,bad_cast]
  exact hf

theorem bare (j : Fin 5) :
    ¬Bad (cyc 8801 4393 (bareOffset j:V)) ∧
    ¬Bad (cyc 8801 5495 (bareOffset j:V)) := by
  have hf := bare_safe j
  have h1 : cyc (8801:V) 4393 (bareOffset j:V) =
      (((4393+8801-(![40,41,1100,2200,8802] j)%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,bareOffset] using
      (cyc_cast (V:=V) 4393 (![40,41,1100,2200,8802] j))
  have h2 : cyc (8801:V) 5495 (bareOffset j:V) =
      (((5495+8801-(![40,41,1100,2200,8802] j)%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,bareOffset] using
      (cyc_cast (V:=V) 5495 (![40,41,1100,2200,8802] j))
  rw [h1,h2,bad_cast,bad_cast]
  exact hf

theorem foreign_and_bare (N C : V) (hN : 0<N) (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0) :
    columnBand 5495 (8801*N) C 4393=0 ∧
    columnBand 4393 (8801*N) C 5495=0 ∧
    bareColumn (8801*N) C 4393=0 ∧
    bareColumn (8801*N) C 5495=0 := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht₁ : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht₂ : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hs₁ (j : Fin 943) : dig 121 (rot 121 n C (selectorOffset 5495 j%n)) 4393=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 4393 (selectorOffset 5495 j) hN (by norm_num) hzero
      (foreign j.val (Or.inl j.isLt)).1
  have hs₂ (j : Fin 943) : dig 121 (rot 121 n C (selectorOffset 4393 j%n)) 5495=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 5495 (selectorOffset 4393 j) hN (by norm_num) hzero
      (foreign j.val (Or.inl j.isLt)).2
  have hc₁ (j : Fin 44) : dig 121 (rot 121 n C (copyOffset 5495 j%n)) 4393=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 4393 (copyOffset 5495 j) hN (by norm_num) hzero
      (foreign (Source34Kernel.extraPos j) (copy_allowed j)).1
  have hc₂ (j : Fin 44) : dig 121 (rot 121 n C (copyOffset 4393 j%n)) 5495=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 5495 (copyOffset 4393 j) hN (by norm_num) hzero
      (foreign (Source34Kernel.extraPos j) (copy_allowed j)).2
  have hb₁ (j : Fin 5) : dig 121 (rot 121 n C (bareOffset j%n)) 4393=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 4393 (bareOffset j) hN (by norm_num) hzero (bare j).1
  have hb₂ (j : Fin 5) : dig 121 (rot 121 n C (bareOffset j%n)) 5495=0 := by
    rw [dig_rot 121 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact Mixed121Single.source_zero N C 5495 (bareOffset j) hN (by norm_num) hzero (bare j).2
  refine ⟨?_,?_,?_,?_⟩
  · change columnBand 5495 n C 4393=0
    simp only [columnBand,hs₁,hc₁,mul_zero,Finset.sum_const_zero,add_zero]
  · change columnBand 4393 n C 5495=0
    simp only [columnBand,hs₂,hc₂,mul_zero,Finset.sum_const_zero,add_zero]
  · change bareColumn n C 4393=0
    simp only [bareColumn,hb₁,Finset.sum_const_zero]
  · change bareColumn n C 5495=0
    simp only [bareColumn,hb₂,Finset.sum_const_zero]

/-- The decoder input of the source34 band reflected at `T`, read at cell `k`. -/
def decoderBand (T : ℕ) (n C k : V) : V :=
  (∑ i, Mixed121Band.selDigit n C k T i *
      (1 + Exp.exp 10 * dsum (Exp.exp 2)
        (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
    Exp.exp 10 * dsum (Exp.exp 2) (Source34Band.copyDigit n C k T) 44

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_single_band (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let T := Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      dig 121 T t=0 ∧ dig 121 T (cyc (8801*N) t 1)≤Exp.exp 120 ∧
      carry 121 (8801*N) a X (cyc (8801*N) t 1)=0 ∧
      ((t=4393 ∧ dig 121 (v 1) t=decoderBand 4393 (8801*N) C t) ∨
       (t=5495 ∧ dig 121 (v 1) t=decoderBand 5495 (8801*N) C t)) := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hc,hraw⟩ :=
    Source34CleanCarry.graph_clean_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0,hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let T : V := Mixed121Temporal.temporalWord n (R-121*n) C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have ht₁ : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht₂ : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hband := decoder_bands n C T t hn ht hC
  rw [hTzero,add_zero] at hband
  have hbands : dig 121 (v 1) t = decoderBand 4393 n C t + decoderBand 5495 n C t +
      bareColumn n C t := by
    rw [hraw]
    simpa only [decoderBand] using hband
  obtain ⟨hf₁,hf₂,hb₁,hb₂⟩ := foreign_and_bare N C hN hC hzero
  have hd₁ : decoderBand 5495 n C 4393=0 := by
    have h := band_column 5495 n C 4393 hn ht₁ hC
    change columnBand 5495 n C 4393 = decoderBand 5495 n C 4393 at h
    rw [hf₁] at h
    exact h.symm
  have hd₂ : decoderBand 4393 n C 5495=0 := by
    have h := band_column 4393 n C 5495 hn ht₂ hC
    change columnBand 4393 n C 5495 = decoderBand 4393 n C 5495 at h
    rw [hf₂] at h
    exact h.symm
  refine ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,hcarry,hTzero,hTpred,hc,?_⟩
  rcases htcase with ht' | ht'
  · left
    refine ⟨ht',?_⟩
    rw [ht'] at hbands ⊢
    rw [hd₁,hb₁,add_zero,add_zero] at hbands
    exact hbands
  · right
    refine ⟨ht',?_⟩
    rw [ht'] at hbands ⊢
    rw [hd₂,hb₂,zero_add,add_zero] at hbands
    exact hbands
end Source34Single
#print axioms Source34Single.shifted_safe
#print axioms Source34Single.copy_allowed
#print axioms Source34Single.bare_safe
#print axioms Source34Single.foreign
#print axioms Source34Single.bare
#print axioms Source34Single.foreign_and_bare
#print axioms Source34Single.graph_single_band
