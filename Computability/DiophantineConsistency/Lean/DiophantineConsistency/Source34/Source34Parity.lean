import DiophantineConsistency.Source34.Source34Occupied
import DiophantineConsistency.Mixed121.Mixed121Parity
import Mathlib.Tactic.FinCases

/-! # Anchor-phase parity at the source34 ports

`Mixed121Parity` at the source34 tuple. Shared and used directly: the phase
function `Mixed121Parity.phase`, the selector geometry `selectors_geometry` /
`selectors_model` (the 943 selector offsets `4393 − j`, `5495 − j` are
unchanged), `noCarry_one_even`, `raw_plus_incoming_even`, `selectorsAt` and
`source_zero`.

What changes is the bare part `ρ^40 + ρ^41 + ρ^1100 + ρ^2200 + ρ^8802`. At
phase `2195` its sources are `2155, 2154, 1095, 8796, 2194`; at phase `3296`
they are `3256, 3255, 2196, 1096, 3295`. So, as for 121x8801, only offset
`1100` at `2195` (anchor `1095`) and offset `2200` at `3296` (anchor `1096`)
read the hull (`bare2195_geometry`, `bare3296_geometry`). The `MF_native`
digits at `2195` and `3296` are still `1`. Re-declared: those geometry facts and
their model forms, `model_high`, `output_even`, `raw_mod_two`, `expand`,
`at2195`, `at3296` and the chain link `graph_simple_parity`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Parity
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord ArithmeticMaskConstants ArithmeticStandardCasts
open CompactHeterogeneousCarry CompactGenericAlignedMass
open Source34Rotation Source34Flatten ModelDigitTransfer
open Mixed121Rotation (selectorOffset coefficient word cap)
open Mixed121Flatten (selectors copies)
open Mixed121Clean (BadNat Bad bad_cast)
open Mixed121Parity (phase selectors_model noCarry_one_even raw_plus_incoming_even selectorsAt
  source_zero)

/-! ## Finite phase geometry -/

theorem bare2195_geometry (j : Fin 5) (hj : j≠⟨2, by decide⟩) :
    ¬BadNat (phase 2195 (![40,41,1100,2200,8802] j)) := by
  fin_cases j <;> norm_num [phase,BadNat] at *

theorem bare3296_geometry (j : Fin 5) (hj : j≠⟨3, by decide⟩) :
    ¬BadNat (phase 3296 (![40,41,1100,2200,8802] j)) := by
  fin_cases j <;> norm_num [phase,BadNat] at *

theorem high2195 : Source34Ports.highDigits.getD 2195 0 = 1 := rfl
theorem high3296 : Source34Ports.highDigits.getD 3296 0 = 1 := rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

private theorem cyc_cast (t q : ℕ) :
    cyc (8801:V) (t:V) (q:V) = ((phase t q:ℕ):V) := by
  have hle : q%8801≤t+8801 := by have := Nat.mod_lt q (by omega : 0<8801); omega
  have hc : ((t+8801-q%8801:ℕ):V)=(t:V)+8801-((q%8801:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8801 = ((q%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (ArithmeticStandardCasts.cast_mod (V:=V) q 8801).symm
  unfold cyc phase
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (ArithmeticStandardCasts.cast_mod (V:=V) (t+8801-q%8801) 8801).symm

theorem bare2195_model (j : Fin 5) (hj : j≠⟨2,by decide⟩) :
    ¬Bad (cyc 8801 2195 (bareOffset j:V)) := by
  have he : cyc (8801:V) 2195 (bareOffset j:V) =
      (phase 2195 (![40,41,1100,2200,8802] j):V) := by
    simpa only [bareOffset,Nat.cast_ofNat] using
      (cyc_cast (V:=V) 2195 (![40,41,1100,2200,8802] j))
  rw [he,bad_cast]
  exact bare2195_geometry j hj

theorem bare3296_model (j : Fin 5) (hj : j≠⟨3,by decide⟩) :
    ¬Bad (cyc 8801 3296 (bareOffset j:V)) := by
  have he : cyc (8801:V) 3296 (bareOffset j:V) =
      (phase 3296 (![40,41,1100,2200,8802] j):V) := by
    simpa only [bareOffset,Nat.cast_ofNat] using
      (cyc_cast (V:=V) 3296 (![40,41,1100,2200,8802] j))
  rw [he,bad_cast]
  exact bare3296_geometry j hj

/-! ## Parity of the graph digit and of the raw column -/

theorem model_high (k : ℕ) (hk : Source34Ports.highDigits.getD k 0 = 1) :
    dig 121 ((Source34Ports.highNat : ℕ) : V) (k:V) = 1 := by
  have h := dig_ofDigits (V:=V) 121 Source34Ports.highDigits Source34Masks.high_digit_lt k
  rw [hk, Nat.cast_one] at h
  rw [Source34Masks.highNat_eq]
  exact h

theorem output_even (N F target : V) (hN : 0<N) (ht : target<8801*N)
    (ht0 : 0<target) (hphase : target%8801=2195 ∨ target%8801=3296)
    (hhigh : NoCarry F (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1)) :
    dig 121 F target%2=0 := by
  have hd0 : 1≤dig 121 ((Source34Ports.highNat:ℕ):V) 0 := by
    rw [Source34Selected.model_origin]; norm_num
  have hh := high_mask_digits 121 8801 N F ((Source34Ports.highNat:ℕ):V) (by norm_num) hN
    Source34Masks.model_high_lt hd0 hhigh
  have h := hh.2 target ht ht0
  have e1 := model_high (V:=V) 2195 high2195
  have e2 := model_high (V:=V) 3296 high3296
  simp only [Nat.cast_ofNat] at e1 e2
  rcases hphase with hp | hp
  · rw [hp,e1] at h
    exact noCarry_one_even _ h
  · rw [hp,e2] at h
    exact noCarry_one_even _ h

private theorem sum_split (s D : Fin 943 → V) (E : V) :
    (∑ i, s i * (1 + E * D i)) = (∑ i, s i) + E * ∑ i, s i * D i := by
  rw [Finset.sum_congr rfl (fun i _ => show s i * (1 + E * D i) = s i + E * (s i * D i) by ring),
    Finset.sum_add_distrib, ← Finset.mul_sum]

theorem raw_mod_two (n C T k : V) (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n)) :
    raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k % 2 =
      (selectorsAt n C k 4393 + selectorsAt n C k 5495 + bareColumn n C k + dig 121 T k)%2 := by
  rw [decoder_bands n C T k hn hk hC, sum_split, sum_split]
  dsimp only [selectorsAt]
  have he : Exp.exp (10:V)=Exp.exp 9*2 := by
    rw [show (10:V)=9+1 by norm_num, exp_succ]
    ring
  rw [he]
  have heq (a b c d e f g h : V) :
      ((a+(Exp.exp 9*2)*b+(Exp.exp 9*2)*c)+(d+(Exp.exp 9*2)*e+(Exp.exp 9*2)*f)+g+h)%2 =
      (a+d+g+h)%2 := by
    have hr : (a+(Exp.exp 9*2)*b+(Exp.exp 9*2)*c)+(d+(Exp.exp 9*2)*e+(Exp.exp 9*2)*f)+g+h =
        (a+d+g+h)+(Exp.exp 9*(b+c+e+f))*2 := by ring
    rw [hr,mod_add_mul _ _ (by norm_num : (0:V)<2)]
  apply heq

theorem expand (n C T k c : V) (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n))
    (hpar : (raw 121 (coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)))
      (word 121 n C bandOffsets T) k + c)%2=0) :
    (selectorsAt n C k 4393 + selectorsAt n C k 5495 + bareColumn n C k + dig 121 T k + c)%2=0 := by
  have h := raw_mod_two n C T k hn hk hC
  rw [mod_add (by norm_num : (0:V)<2), h, ←mod_add (by norm_num : (0:V)<2)] at hpar
  exact hpar

/-! ## The anchor-phase columns -/

theorem at2195 (N C k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=2195) :
    selectorsAt (8801*N) C k 4393=0 ∧ selectorsAt (8801*N) C k 5495=0 ∧
    bareColumn (8801*N) C k=dig 121 C (cyc (8801*N) k 1100) := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  refine ⟨?_,?_,?_⟩
  · unfold selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    apply source_zero N C k (((4393-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (selectors_model j.val j.isLt).1
  · unfold selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    apply source_zero N C k (((5495-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (selectors_model j.val j.isLt).2.1
  · unfold bareColumn
    rw [Finset.sum_eq_single ⟨2, by decide⟩]
    · rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      simp [bareOffset]
    · intro j _ hj
      rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      apply source_zero N C k (bareOffset j) hN hzero
      rw [hp]
      exact bare2195_model j hj
    · intro hh; exact (hh (Finset.mem_univ _)).elim

theorem at3296 (N C k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=3296) :
    selectorsAt (8801*N) C k 4393=0 ∧ selectorsAt (8801*N) C k 5495=0 ∧
    bareColumn (8801*N) C k=dig 121 C (cyc (8801*N) k 2200) := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  refine ⟨?_,?_,?_⟩
  · unfold selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    apply source_zero N C k (((4393-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (selectors_model j.val j.isLt).2.2.1
  · unfold selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    apply source_zero N C k (((5495-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (selectors_model j.val j.isLt).2.2.2
  · unfold bareColumn
    rw [Finset.sum_eq_single ⟨3, by decide⟩]
    · rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      simp [bareOffset]
    · intro j _ hj
      rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      apply source_zero N C k (bareOffset j) hN hzero
      rw [hp]
      exact bare3296_model j hj
    · intro hh; exact (hh (Finset.mem_univ _)).elim

/-! ## The chain links -/

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_simple_parity (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let T := Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      (∀ t<8801*N, 0<t → (t%8801=2195 ∨ t%8801=3296) →
        carry 121 (8801*N) a X (cyc (8801*N) t 1)≤1 ∧
        ((t%8801=2195 → (dig 121 C (cyc (8801*N) t 1100) + dig 121 T t +
            carry 121 (8801*N) a X (cyc (8801*N) t 1))%2=0) ∧
         (t%8801=3296 → (dig 121 C (cyc (8801*N) t 2200) + dig 121 T t +
            carry 121 (8801*N) a X (cyc (8801*N) t 1))%2=0))) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hv5',hcongr',h0',hslots,hhigh⟩ :=
    Source34Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hhigh' : NoCarry (v 1) (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
    rw [←hJ]; exact hhigh
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro t ht ht0 hphase
  have heven := output_even N (v 1) t hN ht ht0 hphase hhigh'
  obtain ⟨hb, hraw⟩ := raw_plus_incoming_even _ _ _ _ _ hcarry t ht heven
  have hpar' := expand n C _ t _ hn ht hC hraw
  refine ⟨hb,?_,?_⟩
  · intro htphase
    obtain ⟨hs1,hs2,hbare⟩ := at2195 N C t hN ht hC hzero htphase
    rw [hs1,hs2,hbare] at hpar'
    simpa only [zero_add] using hpar'
  · intro htphase
    obtain ⟨hs1,hs2,hbare⟩ := at3296 N C t hN ht hC hzero htphase
    rw [hs1,hs2,hbare] at hpar'
    simpa only [zero_add] using hpar'
end Source34Parity
#print axioms Source34Parity.bare2195_geometry
#print axioms Source34Parity.bare3296_geometry
#print axioms Source34Parity.output_even
#print axioms Source34Parity.raw_mod_two
#print axioms Source34Parity.at2195
#print axioms Source34Parity.at3296
#print axioms Source34Parity.graph_simple_parity
