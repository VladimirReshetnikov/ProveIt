import DiophantineConsistency.Mixed121.Mixed121Carry
import DiophantineConsistency.Compact44.CleanGeometry

/-! # Clean support geometry at the 121x8801 ports

This is the 121x8801 counterpart of Compact44's `CleanGeometry`,
`CleanMaskClasses`, `CleanModelSupport` and
`FixedGraphSupportCarry.graph_support_carry_facts`.

`Bad x` is `x ≤ 1065` or `x ∈ {1095, 1096, 2195, 3296}`. That is the hull of
the support `E`, plus the cell `1065`. With `1065` included, both cyclic
predecessors of a safe cell avoid the dummy `1063` (`Mixed121Source`).
Compact44's set also uses `≤ 1065`, but omits `1096`, the second anchor here.
The clause-target shift `1102` maps no element of the set into the set modulo
`8801` (`finite_disjoint`, checked by `omega`).

`graph_support_carry` is the next link of the `LeafFacts` halting chain. It
gives the `CarryInput` of `Mixed121Carry` together with three facts about the
native word: `dig C 0 = 1`, cells outside the hull are zero, and every cell
off the dummy `1063` is Boolean. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Clean
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten
open CompactListMask ArithmeticMaskConstants

def BadNat (x : ℕ) : Prop := x≤1065 ∨ x=1095 ∨ x=1096 ∨ x=2195 ∨ x=3296

theorem finite_disjoint (x : ℕ) (hx : x<8801) :
    ¬ (BadNat x ∧ BadNat ((x+1102)%8801)) := by
  unfold BadNat
  omega

theorem support_subset_bad (j : ℕ) (hj : j ∈ Mixed121Ports.maskSupport) : BadNat j := by
  unfold Mixed121Ports.maskSupport at hj
  rw [List.mem_toFinset, List.mem_filter] at hj
  have h := hj.1
  unfold Mixed121Kernel.support at h
  simp only [List.mem_append, List.mem_range, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with ((h | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | h <;> unfold BadNat <;> omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Bad (x : V) : Prop := x≤1065 ∨ x=1095 ∨ x=1096 ∨ x=2195 ∨ x=3296

theorem bad_cast (j : ℕ) : Bad (j:V) ↔ BadNat j := by
  unfold Bad BadNat
  exact_mod_cast (Iff.rfl : (j≤1065 ∨ j=1095 ∨ j=1096 ∨ j=2195 ∨ j=3296) ↔ _)

theorem model_disjoint (x : V) (hx : x<8801) :
    ¬ (Bad x ∧ Bad ((x+1102)%8801)) := by
  obtain ⟨j,hj,rfl⟩ := CleanGeometry.bounded_standard 8801 x hx
  have hc : (((j+1102)%8801 : ℕ):V) = ((j:V)+1102)%8801 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (DiophantineConsistency.ArithmeticStandardCasts.cast_mod (V:=V) (j+1102) 8801)
  rw [← hc, bad_cast, bad_cast]
  exact finite_disjoint j hj

private theorem sub_cast (r : ℕ) (hr : r ≤ 2^121) :
    ((Mixed121Ports.radix-r : ℕ):V)=Exp.exp (121:V)-(r:V) := by
  unfold Mixed121Ports.radix
  have h1 : 2^121-r+r=2^121 := Nat.sub_add_cancel hr
  have h2 : ((2^121-r : ℕ):V)+(r:V)=((2^121:ℕ):V) := by exact_mod_cast h1
  have h3 : ((2^121:ℕ):V)=Exp.exp (121:V) := by
    simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 121).symm
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

private theorem low_dig (j : ℕ) (hj : j<8801) :
    dig 121 ((Mixed121Ports.lowNat:ℕ):V) (j:V) =
      ((digit Mixed121Ports.radix 1063 Mixed121Ports.maskSupport j : ℕ) : V) := by
  have hd := dig_ofDigits (V:=V) 121
    (digits Mixed121Ports.radix 8801 1063 Mixed121Ports.maskSupport)
    Mixed121Masks.low_digit_lt j
  rw [digits_getD _ _ _ _ hj] at hd
  rw [Mixed121Masks.lowNat_eq]
  exact hd

theorem ordinary_mask_digit (j : ℕ) (hj : j<8801)
    (hmem : j ∈ Mixed121Ports.maskSupport) (hspecial : j≠1063) :
    dig 121 ((Mixed121Ports.lowNat:ℕ):V) (j:V)=Exp.exp 121-2 := by
  rw [low_dig j hj]
  simp only [digit, if_neg hspecial, if_pos hmem]
  rw [sub_cast 2 (by norm_num), Nat.cast_ofNat]

theorem absent_mask_digit (j : ℕ) (hj : j<8801)
    (hmem : j ∉ Mixed121Ports.maskSupport) (hspecial : j≠1063) :
    dig 121 ((Mixed121Ports.lowNat:ℕ):V) (j:V)=Exp.exp 121-1 := by
  rw [low_dig j hj]
  simp only [digit, if_neg hspecial, if_neg hmem]
  rw [sub_cast 1 (by norm_num), Nat.cast_one]

theorem zero_outside (n C : V)
    (hslots : ∀ k<n, 0<k →
      NoCarry (dig 121 C k) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (k%8801))) :
    ∀ k<n, ¬Bad (k%8801) → dig 121 C k=0 := by
  intro k hi hbad
  have hi0 : 0<k := by
    by_contra hz
    have he : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hz)
    subst k
    apply hbad
    left
    simp
  have hmod : k%8801<8801 := mod_lt _ (by norm_num)
  obtain ⟨j,hj,hjv⟩ := CleanGeometry.bounded_standard 8801 (k%8801) hmod
  have hbadnat : ¬BadNat j := by
    intro hb
    apply hbad
    rw [hjv,bad_cast]
    exact hb
  have hmem : j ∉ Mixed121Ports.maskSupport := by
    intro hm
    exact hbadnat (support_subset_bad j hm)
  have hspecial : j≠1063 := by
    intro he
    apply hbadnat
    unfold BadNat
    rw [he]
    left
    omega
  have hn := hslots k hi hi0
  rw [hjv,absent_mask_digit j hj hmem hspecial] at hn
  exact Mixed121Increment.forbidden_zero _ (dig_lt 121 C k) hn

theorem boolean_away_special (n C : V) (h0 : dig 121 C 0≤1)
    (hslots : ∀ k<n, 0<k →
      NoCarry (dig 121 C k) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (k%8801))) :
    ∀ k<n, k%8801≠1063 → dig 121 C k≤1 := by
  intro k hi hspecial
  by_cases hi0 : k=0
  · simpa only [hi0] using h0
  · have hipos : 0<k := by
      by_contra hz
      exact hi0 (nonpos_iff_eq_zero.mp (not_lt.mp hz))
    have hmod : k%8801<8801 := mod_lt _ (by norm_num)
    obtain ⟨j,hj,hjv⟩ := CleanGeometry.bounded_standard 8801 (k%8801) hmod
    have hjsp : j≠1063 := by
      intro he
      apply hspecial
      rw [hjv,he]
      norm_num
    have hn := hslots k hi hipos
    by_cases hmem : j ∈ Mixed121Ports.maskSupport
    · rw [hjv,ordinary_mask_digit j hj hmem hjsp] at hn
      exact Mixed121Increment.ordinary_le_one _ (dig_lt 121 C k) hn
    · rw [hjv,absent_mask_digit j hj hmem hjsp] at hn
      have hz := Mixed121Increment.forbidden_zero _ (dig_lt 121 C k) hn
      rw [hz]
      norm_num

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_support_carry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
        (coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (word 121 (8801*N) C bandOffsets
          (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)) ∧
      dig 121 C 0=1 ∧
      (∀ k<8801*N, ¬Bad (k%8801) → dig 121 C k=0) ∧
      (∀ k<8801*N, k%8801≠1063 → dig 121 C k≤1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry⟩ := Mixed121Carry.graph_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hv5',hcongr',h0,hslots,hhigh⟩ :=
    Mixed121Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,?_,?_⟩
  · exact zero_outside _ _ hslots
  · apply boolean_away_special _ _ ?_ hslots
    rw [h0]
end Mixed121Clean
#print axioms Mixed121Clean.finite_disjoint
#print axioms Mixed121Clean.support_subset_bad
#print axioms Mixed121Clean.model_disjoint
#print axioms Mixed121Clean.ordinary_mask_digit
#print axioms Mixed121Clean.absent_mask_digit
#print axioms Mixed121Clean.zero_outside
#print axioms Mixed121Clean.boolean_away_special
#print axioms Mixed121Clean.graph_support_carry
