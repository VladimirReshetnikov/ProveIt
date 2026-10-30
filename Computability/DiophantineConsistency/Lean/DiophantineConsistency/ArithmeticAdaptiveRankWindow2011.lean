import DiophantineConsistency.ArithmeticAdaptivePellIndices2011

/-! An actual-zero rank window for the unrestricted adaptive carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem one_le_of_pos {x : V} (h : 0<x) : 1≤x := by
  simpa using lt_iff_succ_le.mp h
private theorem add_le_right {x y : V} (h : x≤y) (z : V) : x+z≤y+z :=
  _root_.add_le_add h (le_refl z)
private theorem slack_equation (q r t G L M Z : V)
    (hr : r+1=q) (ht : t+1=q*q)
    (hG : G+L+q+1=q*q) (hM : M+Z+q+1=r*(1+2*q)) :
    G*t+M+L*t+Z+q^3+q+1=q^4 := by
  have ht' : t=r*r+2*r := by
    apply add_right_cancel (b:=(1:V))
    calc
      t+1=q*q := ht
      _=(r*r+2*r)+1 := by rw [←hr]; ring
  apply add_right_cancel (b:=(q+1)*t+(q+1))
  calc
    (G*t+M+L*t+Z+q^3+q+1)+((q+1)*t+(q+1))=
      (G+L+q+1)*t+(M+Z+q+1)+q^3+q+1 := by ring
    _=q*q*t+r*(1+2*q)+q^3+q+1 := by rw [hG,hM]
    _=q^4+((q+1)*t+(q+1)) := by rw [ht',←hr]; ring

/-- Pure scalar rank bound. The only gap is derived from the first carrier. -/
theorem scalar_rank_window (q beta MC MF J F alpha : V)
    (hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1)
    (hgap : F+alpha<q) :
    24≤((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J ∧
    (((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J)+q^3+q+1≤q^4 := by
  have hq2 : 2≤q := by
    rw [hq]
    have h:=add_le_right (one_le_mul (one_le_of_pos hbeta) (one_le_of_pos hJ)) 1
    simpa only [one_add_one_eq_two] using h
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (le_trans (by simp : (1:V)≤2) hq2)
  have hFq : F≤q := le_trans (by simp : F≤F+alpha) (le_of_lt hgap)
  let v:=q-F
  let C:=v-alpha
  have hv : v+F=q := tsub_add_cancel_of_le hFq
  have ha : alpha<v := by
    apply (add_lt_add_iff_right F).mp
    rw [hv,add_comm alpha F]
    exact hgap
  have hC : 0<C := tsub_pos_iff_lt.mpr ha
  have hCv : C+alpha=v := tsub_add_cancel_of_le (le_of_lt ha)
  have hq3 : 3≤q := by
    have h2 : (2:V)≤F+alpha := by
      simpa only [one_add_one_eq_two] using add_le_add (one_le_of_pos hF) (one_le_of_pos halpha)
    have h:=le_trans (add_le_right h2 1) (lt_iff_succ_le.mp hgap)
    simpa only [show (2:V)+1=3 by ring] using h
  let G:=(q-1)*v+alpha
  let M:=(MC+q*MF)*J
  let R:=G*(q^2-1)+M
  have hGlo : q≤G := calc
    q=q-1+1 := hq1.symm
    _≤(q-1)*v+alpha := add_le_add
      (le_mul_of_one_le_right (by simp) (one_le_of_pos (lt_of_lt_of_le halpha (le_of_lt ha))))
      (one_le_of_pos halpha)
  have hsq9 : (9:V)≤q^2 := by
    simpa only [pow_two,show (3:V)*3=9 by ring] using mul_le_mul hq3 hq3 (by simp) (by simp)
  have hsq1 : q^2-1+1=q^2 := tsub_add_cancel_of_le (le_trans (by simp : (1:V)≤9) hsq9)
  have ht8 : (8:V)≤q^2-1 := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hsq1,show (8:V)+1=9 by ring]
    exact hsq9
  have hlo : (24:V)≤R := calc
    24=3*8 := by ring
    _≤q*(q^2-1) := mul_le_mul hq3 ht8 (by simp) (by simp)
    _≤G*(q^2-1) := mul_le_mul_of_nonneg_right hGlo (by simp)
    _≤R := by dsimp [R]; simp
  have hF0 : F-1+1=F := tsub_add_cancel_of_le (one_le_of_pos hF)
  have hC0 : C-1+1=C := tsub_add_cancel_of_le (one_le_of_pos hC)
  have hJ0 : J-1+1=J := tsub_add_cancel_of_le (one_le_of_pos hJ)
  have hMC0 : MC+(beta-MC-1)+1=beta := calc
    MC+(beta-MC-1)+1=(beta-MC-1+1)+MC := by ring
    _=(beta-MC)+MC := by rw [tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_iff_lt.mpr hMC))]
    _=beta := tsub_add_cancel_of_le (le_of_lt hMC)
  have hMF0 : MF+(2*beta-MF-1)+1=2*beta := calc
    MF+(2*beta-MF-1)+1=(2*beta-MF-1+1)+MF := by ring
    _=(2*beta-MF)+MF := by rw [tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_iff_lt.mpr hMF))]
    _=2*beta := tsub_add_cancel_of_le (le_of_lt hMF)
  let L:=q*(F-1)+(C-1)
  let Z:=(q+1)*(J-1)+J*((beta-MC-1)+q*(2*beta-MF-1))
  have hGsum : G+L+q+1=q*q := calc
    G+L+q+1=(q-1)*v+q*(F-1+1)+(C-1+1+alpha) := by dsimp [G,L]; ring
    _=(q-1)*v+q*F+v := by rw [hF0,hC0,hCv]
    _=(q-1+1)*v+q*F := by ring
    _=q*(v+F) := by rw [hq1]; ring
    _=q*q := by rw [hv]
  have hbetaJ : beta*J=q-1 := by
    apply add_right_cancel (b:=(1:V))
    exact hq.symm.trans hq1.symm
  have hMsum : M+Z+q+1=(q-1)*(1+2*q) := calc
    M+Z+q+1=(MC+q*MF)*J+(q+1)*(J-1+1)+J*((beta-MC-1)+q*(2*beta-MF-1)) := by dsimp [M,Z]; ring
    _=J*((MC+(beta-MC-1)+1)+q*(MF+(2*beta-MF-1)+1)) := by rw [hJ0]; ring
    _=beta*J*(1+2*q) := by rw [hMC0,hMF0]; ring
    _=(q-1)*(1+2*q) := by rw [hbetaJ]
  have hslack : R+L*(q^2-1)+Z+q^3+q+1=q^4 := by
    exact slack_equation q (q-1) (q^2-1) G L M Z hq1 (by simpa only [pow_two] using hsq1) hGsum hMsum
  have hupper : R+q^3+q+1≤q^4 := by
    have hh : R≤R+L*(q^2-1)+Z := by simp
    have hh' := add_le_right (add_le_right (add_le_right hh (q^3)) q) 1
    exact le_of_le_of_eq hh' hslack
  exact ⟨hlo,hupper⟩

def RankWindow (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  24≤R ∧ R+q^3+q+1≤q^4

theorem expressionAt_rank_window (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) :
    RankWindow p v := by
  have hg := (expressionAt_transport_positive p v hb hv hz).2
  have hgap : v 1+v 2<1+v 0*(p 0:V) := tsub_pos_iff_lt.mp hg
  exact scalar_rank_window _ _ _ _ _ _ _ hb (hv 0) (hv 1) (hv 2) hl hh (by ring) hgap

private theorem power_left_step (r n : ℕ) : r*r^n=r^(n+1) := by
  rw [pow_succ,Nat.mul_comm]

private theorem two_power_bound (r n m : ℕ) (hr : 2≤r) (hn : n+1≤m) :
    2*r^n≤r^m := calc
  _≤r*r^n:=Nat.mul_le_mul_right _ hr
  _=r^(n+1):=power_left_step r n
  _≤r^m:=Nat.pow_le_pow_right (by omega) hn

private theorem pow_extends (r n : ℕ) (hn : n≠0) : r≤r^n := Nat.le_self_pow hn r

theorem current_bounds_nat :
    15≤CurrentMasks2011.beta ∧ CurrentMasks2011.lowPort<CurrentMasks2011.beta ∧
      CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta := by
  have hr : 16≤CurrentMasks2011.radix:=by unfold CurrentMasks2011.radix; decide
  have hr1 : 1<CurrentMasks2011.radix:=by omega
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011:=
    pow_extends _ _ (by decide)
  have hb : 15≤CurrentMasks2011.beta:=by unfold CurrentMasks2011.beta; omega
  have hz : 0∈CurrentMasks2011.lowSupport:=by
    rw [CurrentMasks2011.lowSupport_def]
    simp
  have hm : 1≤LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport:=by
    simpa only [LowMaskCoding.supportValue,pow_zero] using Finset.single_le_sum (fun j _ => Nat.zero_le (_^j)) hz
  have hl : CurrentMasks2011.lowPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.lowPort LowMaskCoding.mask
    rw [←CurrentMasks2011.beta]
    simp only [show (2:ℕ)-1=1 by decide,one_mul]
    exact Nat.sub_lt (by omega : 0<CurrentMasks2011.beta) (by omega : 0<LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport)
  have hlen : CurrentMasks2011.highPrefix.length=1006:=by
    simp only [CurrentMasks2011.highPrefix,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  have hd : ∀x∈CurrentMasks2011.highPrefix,x<CurrentMasks2011.radix:=by
    intro x hx
    simp only [CurrentMasks2011.highPrefix,List.mem_cons,List.mem_append,List.mem_replicate,
      List.not_mem_nil,or_false] at hx
    norm_num [CurrentMasks2011.radix] at hx ⊢
    omega
  have hhigh : CurrentMasks2011.highPort<CurrentMasks2011.radix^1006:=by
    unfold CurrentMasks2011.highPort CurrentMasks2011.highDigits
    rw [Nat.ofDigits_append_replicate_zero]
    simpa only [hlen] using Nat.ofDigits_lt_base_pow_length hr1 hd
  have hpow : 2*CurrentMasks2011.radix^1006≤CurrentMasks2011.radix^2011:=
    two_power_bound _ _ _ (by omega) (by decide)
  have hpowpos : 0<CurrentMasks2011.radix^1006:=pow_pos (by omega) _
  have hh : CurrentMasks2011.highPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.beta
    omega
  exact ⟨hb,hl,by omega⟩

theorem current_rank_window (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : RankWindow currentPorts v := by
  obtain ⟨hb15,hlNat,hhNat⟩ := current_bounds_nat
  have hbNat : 0<CurrentMasks2011.beta := by omega
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast hbNat
  have hl : (CurrentMasks2011.lowPort:V)<(CurrentMasks2011.beta:V) := by exact_mod_cast hlNat
  have hh : ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)<2*(CurrentMasks2011.beta:V) := by exact_mod_cast hhNat
  apply expressionAt_rank_window currentPorts v
  · simpa only [currentPorts,Matrix.cons_val_zero] using hb
  · change (CurrentMasks2011.lowPort:V)<(CurrentMasks2011.beta:V); exact hl
  · change ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)<2*(CurrentMasks2011.beta:V); exact hh
  · exact hv
  · rw [currentPorts_cast]; exact hz

theorem current_natural_rank_window (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    RankWindow currentPorts (fun j => v j+1) :=
  current_rank_window _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
