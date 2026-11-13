import DiophantineConsistency.Mixed121.Mixed121Single

/-! # The decoded selection at the 121x8801 clean target

These are the 121x8801 counterparts of Compact44's `SelectedBandInputs`,
`HighMaskLocal`, `FixedGraphSelectedInputs`, `FixedGraphLocalNoCarry` and
the decoding step of `FixedGraphSelectedDecoder`.

* At a clause target `T`, the band's source cells are the support positions
  themselves (`cyc n T (T − e) = e`). None of them is the dummy `1063`, so
  every selector and copy digit is Boolean (`selected_inputs`).
* `MF_native` has the digit `μ` at both clause targets. The high-mask
  saturation then gives `NoCarry F_T μ` (`local_nocarry`).
* `graph_selected_decode` applies `Mixed121Decoder.decode` at the clean target
  `t` of `Mixed121Single`. Either the band is empty, or exactly one tile `i`
  is selected and all 44 copy and anchor digits equal its radix-four digits. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Selected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord ArithmeticMaskConstants CompactHeterogeneousCarry
open CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten ModelDigitTransfer

theorem high_target4393 : Mixed121Ports.highDigits.getD 4393 0 = Mixed121Ports.mu := rfl
theorem high_target5495 : Mixed121Ports.highDigits.getD 5495 0 = Mixed121Ports.mu := rfl
theorem high_origin : Mixed121Ports.highDigits.getD 0 0 = 4 := rfl

theorem extra_ne_dummy : ∀ j ∈ Mixed121Kernel.extraPositions, j ≠ 1063 := by
  intro j hj
  have h := Mixed121Single.extra_allowed j hj
  unfold Mixed121Single.Allowed at h
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `μ` in a model, in the decoder's mask form. -/
theorem mu_model : ((Mixed121Ports.mu : ℕ) : V) =
    (Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44 :=
  Mixed121Digits.mu_cast

theorem model_target (k : ℕ) (hk : Mixed121Ports.highDigits.getD k 0 = Mixed121Ports.mu) :
    dig 121 ((Mixed121Ports.highNat : ℕ) : V) (k:V) =
      (Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44 := by
  have h := dig_ofDigits (V:=V) 121 Mixed121Ports.highDigits Mixed121Masks.high_digit_lt k
  rw [hk, mu_model] at h
  rw [Mixed121Masks.highNat_eq]
  exact h

theorem model_origin : dig 121 ((Mixed121Ports.highNat : ℕ) : V) 0 = 4 := by
  have h := dig_ofDigits (V:=V) 121 Mixed121Ports.highDigits Mixed121Masks.high_digit_lt 0
  rw [high_origin] at h
  rw [Mixed121Masks.highNat_eq]
  simp only [Nat.cast_zero, Nat.cast_ofNat] at h
  exact h

theorem local_nocarry (N F : V) (hN : 0<N)
    (hhigh : NoCarry F (((Mixed121Ports.highNat : ℕ) : V)*rep (121*8801) N-1)) :
    NoCarry (dig 121 F 4393) ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) ∧
      NoCarry (dig 121 F 5495) ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) := by
  have hnge : (8801:V)≤8801*N := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [mul_one] using h
  have hd0 : 1≤dig 121 ((Mixed121Ports.highNat:ℕ):V) 0 := by rw [model_origin]; norm_num
  have hh := high_mask_digits 121 8801 N F ((Mixed121Ports.highNat:ℕ):V) (by norm_num) hN
    Mixed121Masks.model_high_lt hd0 hhigh
  constructor
  · have h := hh.2 4393 (lt_of_lt_of_le (by norm_num) hnge) (by norm_num)
    rw [mod_eq_self_of_lt (by norm_num : (4393:V)<8801)] at h
    have ht := model_target (V:=V) 4393 high_target4393
    simp only [Nat.cast_ofNat] at ht
    rw [ht] at h
    exact h
  · have h := hh.2 5495 (lt_of_lt_of_le (by norm_num) hnge) (by norm_num)
    rw [mod_eq_self_of_lt (by norm_num : (5495:V)<8801)] at h
    have ht := model_target (V:=V) 5495 high_target5495
    simp only [Nat.cast_ofNat] at ht
    rw [ht] at h
    exact h

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

/-- A source cell of the band reflected at `T` is the support position itself. -/
theorem source_cell (n : V) (T e : ℕ) (hT : (T:V)<n) (he : e ≤ T) :
    cyc n (T:V) (((T-e:ℕ)):V) = (e:V) := by
  have hle : ((T-e:ℕ):V) ≤ (T:V) := by exact_mod_cast Nat.sub_le T e
  rw [cyc_of_le hT (lt_of_le_of_lt hle hT) hle, cast_sub T e he]
  have hev : (e:V) ≤ (T:V) := by exact_mod_cast he
  exact tsub_tsub_cancel_of_le hev

/-- The selector and copy digits of a clause band are Boolean. -/
theorem selected_inputs (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (hbool : ∀ k<n, k%8801≠1063 → dig 121 C k≤1) :
    (∀ i : Fin 943, Mixed121Band.selDigit n C (T:V) T i≤1) ∧
    (∀ j < 44, Mixed121Band.copyDigit n C (T:V) T j≤1) := by
  constructor
  · intro i
    unfold Mixed121Band.selDigit
    have hi : i.val ≤ T := by have := i.isLt; omega
    rw [source_cell n T i.val ht hi]
    apply hbool _ (lt_of_le_of_lt (by exact_mod_cast hi) ht)
    rw [mod_eq_self_of_lt (by exact_mod_cast (show i.val < 8801 by omega))]
    intro h
    have : i.val = 1063 := by exact_mod_cast h
    have := i.isLt
    omega
  · intro j hj
    unfold Mixed121Band.copyDigit
    have hmem : Mixed121Band.extraPosN j ∈ Mixed121Kernel.extraPositions := by
      unfold Mixed121Band.extraPosN
      rw [dif_pos hj]
      exact List.get_mem _ _
    have hall := Mixed121Single.extra_allowed _ hmem
    have hne := extra_ne_dummy _ hmem
    have hle : Mixed121Band.extraPosN j ≤ T := by
      unfold Mixed121Single.Allowed at hall
      omega
    rw [source_cell n T _ ht hle]
    apply hbool _ (lt_of_le_of_lt (by exact_mod_cast hle) ht)
    have hlt : Mixed121Band.extraPosN j < 8801 := by
      unfold Mixed121Single.Allowed at hall
      omega
    rw [mod_eq_self_of_lt (by exact_mod_cast hlt)]
    intro h
    exact hne (by exact_mod_cast h)

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

/-- The decoded selection of one band at the clean target. -/
def Decoded (n C : V) (T : ℕ) : Prop :=
  ((∀ i, Mixed121Band.selDigit n C (T:V) T i = 0) ∧
      ∀ j < 44, Mixed121Band.copyDigit n C (T:V) T j = 0) ∨
    ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C (T:V) T) i ∧
      ∀ j < 44, Mixed121Band.copyDigit n C (T:V) T j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V)

theorem graph_selected_decode (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N t : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      ((t=4393 ∧ Decoded (8801*N) C 4393) ∨ (t=5495 ∧ Decoded (8801*N) C 5495)) := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,hcarry,hTzero,hTpred,hc,hband⟩ :=
    Mixed121Single.graph_single_band v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0,hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0'',hslots,hhigh⟩ :=
    Mixed121Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let n : V := 8801*N
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht₁ : ((4393:ℕ):V)<n := by simpa using lt_of_lt_of_le (by norm_num : (4393:V)<8801) hnge
  have ht₂ : ((5495:ℕ):V)<n := by simpa using lt_of_lt_of_le (by norm_num : (5495:V)<8801) hnge
  have hhigh' : NoCarry (v 1) (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
    rw [←hJ]; exact hhigh
  obtain ⟨hl₁, hl₂⟩ := local_nocarry N (v 1) hN hhigh'
  refine ⟨N,t,hN,hq,hJ,?_⟩
  rcases hband with ⟨ht,hb⟩ | ⟨ht,hb⟩
  · left
    refine ⟨ht, ?_⟩
    obtain ⟨hs, hcp⟩ := selected_inputs n _ 4393 ht₁ (by norm_num) hbool
    have hnc := hl₁
    rw [← ht, hb, ht] at hnc
    have hnc' : NoCarry (Mixed121Single.decoderBand 4393 n
        (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) ((4393:ℕ):V))
        ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) := by
      simpa only [Nat.cast_ofNat] using hnc
    exact Mixed121Decoder.decode _ (fun i d => (Mixed121Digits.digit (Compact943Data.row i) d : V))
      _ 44 (Compact943Decoder.count_bound _ hs)
      (fun i d _ => by exact_mod_cast Mixed121Digits.digit_le_one _ d) hcp hnc'
  · right
    refine ⟨ht, ?_⟩
    obtain ⟨hs, hcp⟩ := selected_inputs n _ 5495 ht₂ (by norm_num) hbool
    have hnc := hl₂
    rw [← ht, hb, ht] at hnc
    have hnc' : NoCarry (Mixed121Single.decoderBand 5495 n
        (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) ((5495:ℕ):V))
        ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) := by
      simpa only [Nat.cast_ofNat] using hnc
    exact Mixed121Decoder.decode _ (fun i d => (Mixed121Digits.digit (Compact943Data.row i) d : V))
      _ 44 (Compact943Decoder.count_bound _ hs)
      (fun i d _ => by exact_mod_cast Mixed121Digits.digit_le_one _ d) hcp hnc'
end Mixed121Selected
#print axioms Mixed121Selected.high_target4393
#print axioms Mixed121Selected.local_nocarry
#print axioms Mixed121Selected.source_cell
#print axioms Mixed121Selected.selected_inputs
#print axioms Mixed121Selected.graph_selected_decode
