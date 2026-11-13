import DiophantineConsistency.BFS943.Q170Syntax74
import DiophantineConsistency.BFS943.Q170Units
import DiophantineConsistency.BFS943.Q170Residue
import DiophantineConsistency.BFS943.Carrier65BFSSource
import DiophantineConsistency.BFS943.ProductRoot
import DiophantineConsistency.BFS943.AdjacentInteger
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelCarrierScaled

/-! # Soundness of package 170's 74/438 rational carrier

In every model of `𝗜𝚺₁`, a positive zero `v` of `Q170Form74.value74` (in the
model's ring of differences) at ports with `31 ≤ β`, `MC < β`, `MF < 2β`
gives a positive solution of Carrier65's five equations
(`ArithmeticCarrierSoundness2011.Equations`), at

  `u = (J, F, α, z, f, τ m, T, s, w, N, η, ζ, y, γ)`, `m = i (a + 2) D`

(`FIXED_CARRIER_PROOF.md` §7.1–§7.2):

1. the three factors are units, so `N1 = Nt = 1` and `B = 0`:
   `(Q - 1) t² = E² A F2 (Q V² - 1)`, `t = E n + k - R - 1`;
2. `A` and `F2` are each coprime to `Q - 1` and to `Q V² - 1` (explicit
   Bézout identities in the ring of differences, using `D² = 1 + Δ c²`,
   `Δ + 1 = (a+2)²` and `(a + 2) D ∣ W = F2 - 1`), so
   `TenPositiveScaledSquare.scaled_product_factor_square` makes `A F2` a square,
   and `ModelProductPell.pp_square_of_coprime` gives `A = τ²`, `F2 = f²`;
3. the rational adjacent-Pell integrality
   `TenPositiveAdjacentInteger.quotient_of_scaled_norm` gives `|t| = E τ f y`
   and `Q V² - (Q - 1) y² = 1`; `t > 0`, so `E ∣ k - R - 1`, i.e.
   `k ≡ R + 1 (mod E)`;
4. `Q170Residue.carrier_of_residue` gives `E N + k = τ + R` with `N > 0`.

`zero_halts` composes with `Carrier65BFSSource.equations_halt`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace Q170Sound74
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
  Q170Form74 Q170Units ArithmeticPellRecurrence ArithmeticOddOrdinateResidue ArithmeticGcdNormalization
open ArithmeticCarrierSoundness2011 (Equations)
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat
  lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A Bézout identity in the ring of differences is a natural unit certificate. -/
theorem bez_of_ring (a b : V) (X Y : DiffRing V) (h : ι a*X+ι b*Y=1) : Bez a b 1 := by
  obtain ⟨x1,x2,rfl⟩ := exists_mk X
  obtain ⟨y1,y2,rfl⟩ := exists_mk Y
  refine ⟨x2,y2,x1,y1,?_⟩
  apply ι_injective
  rw [mk_eq_sub,mk_eq_sub] at h
  simp only [map_add,map_mul,map_one]
  linear_combination -h

theorem ring_of_bez {a b : V} (h : Bez a b 1) : ∃ X Y : DiffRing V, ι a*X+ι b*Y=1 := by
  obtain ⟨u,v,w,z,he⟩ := h
  refine ⟨ι w-ι u,ι z-ι v,?_⟩
  have h1 := congrArg ι he
  simp only [map_add,map_mul,map_one] at h1
  linear_combination -h1

/-- Unit certificates multiply in the second argument. -/
theorem bez_mul {x a b : V} (h1 : Bez x a 1) (h2 : Bez x b 1) : Bez x (a*b) 1 := by
  obtain ⟨X1,Y1,e1⟩ := ring_of_bez h1
  obtain ⟨X2,Y2,e2⟩ := ring_of_bez h2
  apply bez_of_ring x (a*b) (X1+X2-ι x*X1*X2) (Y1*Y2)
  rw [map_mul]
  linear_combination (ι b*Y2)*e1+(1-ι x*X1)*e2

theorem units_three {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (hd : Discrete R) {a b c : R} (h : a*b*c=1) (ha : a≠-1) (hb : b≠-1) :
    a=1 ∧ b=1 ∧ c=1 := by
  have ha1 : a=1 := by
    rcases eq_one_or_neg_one_of_mul_eq_one hd (show a*(b*c)=1 by rw [←h]; ring) with h1|h1
    · exact h1
    · exact absurd h1 ha
  subst ha1
  have hb1 : b=1 := by
    rcases eq_one_or_neg_one_of_mul_eq_one hd (show b*c=1 by rw [←h]; ring) with h1|h1
    · exact h1
    · exact absurd h1 hb
  subst hb1
  exact ⟨rfl,rfl,by simpa using h⟩

section Defs
variable (p : Fin 4 → ℕ) (v : Fin 12 → V)
/-- The natural registers of a positive assignment. -/
def q : V := (p 0:V)*v 0+1
def X : V := v 8*q p v
def Y : V := v 7*q p v^3
def E : V := X p v*Y p v
def k : V := v 9+v 10
def c : V := k v*Y p v+v 9
def a : V := E p v+Y p v
def A : V := (E p v*k v*Y p v)*((E p v*k v*Y p v)+k v)+1
def D : V := X p v+a p v*c p v+v 11*(4*a p v+3)
def m : V := v 5*(a p v+2)*D p v
def W0 : V := (m p v*(c p v*c p v))*(m p v*(delta (a p v)*(c p v*c p v)))
def W : V := A p v*W0 p v
def F2 : V := 1+W p v
def Q : V := delta (a p v)*W p v
def R : V := ((q p v-1)*(q p v-v 1)+v 2)*(q p v^2-1)+((p 2:V)+q p v*(p 3:V))*v 0
end Defs

theorem A_first (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    A p v=1+((X p v*Y p v)*Y p v)*((X p v*Y p v)*Y p v+1)*k v*k v := by
  unfold A E; ring

/-- **Soundness of the 74 carrier**: a positive zero gives the five Carrier65 equations. -/
theorem equations_of_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j, 0<v j)
    (hz : value74 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0) :
    ∃ u : Fin 14 → V, (∀ j, 0<u j) ∧ Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) u := by
  have hb0 : (0:V)<(p 0:V) := lt_of_lt_of_le (by norm_num) hb31
  -- positivity of the natural registers
  have hq32 : (32:V)≤q p v := by
    unfold q
    calc (32:V)=31*1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := add_le_add (mul_le_mul hb31 (pos_iff_one_le.mp (hv 0)) (by simp)
          (by simp)) le_rfl
  have hq1 : 1≤q p v := le_trans (by norm_num) hq32
  have hX16 : (16:V)≤X p v := le_trans (le_trans (by norm_num) hq32)
    (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 8)))
  have hY4 : (4:V)≤Y p v := by
    have h1 : q p v≤q p v^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hq1 (by norm_num : 1≤3)
    exact le_trans (le_trans (by norm_num) hq32) (le_trans h1
      (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 7))))
  have hX0 : 0<X p v := lt_of_lt_of_le (by norm_num) hX16
  have hY0 : 0<Y p v := lt_of_lt_of_le (by norm_num) hY4
  have hE0 : 0<E p v := mul_pos hX0 hY0
  have hketa : v 9<k v := lt_add_of_pos_right _ (hv 10)
  have hk2 : 2≤k v := by
    unfold k
    simpa only [one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 9))
      (pos_iff_one_le.mp (hv 10))
  have hc0 : 0<c p v := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 9)
  have hA0 : 0<A p v := by unfold A; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hD0 : 0<D p v := by
    unfold D; exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hX0 (Arithmetic.zero_le _))
      (Arithmetic.zero_le _)
  have hm0 : 0<m p v := by
    unfold m
    exact mul_pos (mul_pos (hv 5) (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))) hD0
  have hd0 : 0<delta (a p v) := by
    unfold delta
    exact mul_pos (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
      (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
  have hW00 : 0<W0 p v := by
    unfold W0; exact mul_pos (mul_pos hm0 (mul_pos hc0 hc0)) (mul_pos hm0 (mul_pos hd0 (mul_pos hc0 hc0)))
  have hW0 : 0<W p v := mul_pos hA0 hW00
  have hQ0 : 0<Q p v := mul_pos hd0 hW0
  have hQ1 : 1≤Q p v := pos_iff_one_le.mp hQ0
  -- the factorization of the circuit in the ring of differences
  obtain ⟨R0,hR0⟩ : ∃ x : DiffRing V, x=(((p 0:ℕ):DiffRing V)*ι (v 0)*(ι (q p v)-ι (v 1))+
      ι (v 2))*(ι (q p v)*ι (q p v)-1)+(((p 2:ℕ):DiffRing V)+ι (q p v)*((p 3:ℕ):DiffRing V))*
      ι (v 0) := ⟨_,rfl⟩
  obtain ⟨t,ht⟩ : ∃ x : DiffRing V, x=ι (E p v)*ι (v 4)+(ι (k v)-R0-1) := ⟨_,rfl⟩
  obtain ⟨Nt,hNt⟩ : ∃ x : DiffRing V, x=(((p 1:ℕ):DiffRing V)+ι (v 8))*
      (ι (q p v)-ι (v 1)-ι (v 2))+(ι (q p v)-ι (v 1))-ι (v 3)*(((p 0:ℕ):DiffRing V)*ι (v 0)) :=
    ⟨_,rfl⟩
  obtain ⟨Vr,hVr⟩ : ∃ x : DiffRing V, x=ι (F2 p v)*(ι (c p v)*ι (v 6)-R0)-ι (c p v) :=
    ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃ x : DiffRing V, x=ι (delta (a p v))*ι (W p v)*
      (t*t-ι (E p v)*ι (E p v)*(ι (A p v)*ι (F2 p v))*(Vr*Vr))-t*t+
      ι (E p v)*ι (E p v)*(ι (A p v)*ι (F2 p v)) := ⟨_,rfl⟩
  have hqι : ι (q p v)=((p 0:ℕ):DiffRing V)*ι (v 0)+1 := by
    simp only [q,map_add,map_mul,map_one,map_natCast]
  rw [value74_factors (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j)) (ι (q p v)) (ι (X p v))
    (ι (Y p v)) (ι (E p v)) (ι (k v)) (ι (A p v)) (ι (c p v)) (ι (a p v)) (ι (4*a p v+3))
    (ι (delta (a p v))) (ι (D p v)) R0 t Nt (ι (m p v)) (ι (m p v*(delta (a p v)*(c p v*c p v))))
    (ι (m p v*(c p v*c p v))) (ι (W p v)) (ι (F2 p v)) Vr (ι (A p v)*ι (F2 p v)) B hqι
    (by simp only [X,map_mul]) (by simp only [Y,map_mul,map_pow]; ring)
    (by simp only [E,map_mul]) (by simp only [k,map_add])
    (by simp only [A,map_add,map_mul,map_one]; ring) (by simp only [c,map_add,map_mul])
    (by simp only [a,map_add]) (by simp only [map_add,map_mul,map_ofNat])
    (by simp only [delta,map_add,map_mul,map_one,map_ofNat]; ring)
    (by simp only [D,map_add,map_mul,map_ofNat]) hR0 ht hNt
    (by simp only [m,map_mul,map_add,map_ofNat]) (by simp only [map_mul]) (by simp only [map_mul])
    (by simp only [W,W0,map_mul]) (by simp only [F2,map_add,map_one]) hVr rfl hB] at hz
  -- the three factors are units
  obtain ⟨φ⟩ : Nonempty (DiffRing V →+* ZMod 4) := ⟨mod4⟩
  have hDelta : ι (delta (a p v))=(ι (a p v)+2)^2-1 := by
    simp only [delta,map_add,map_mul,map_one,map_ofNat]; ring
  have hN1ne : ι (D p v)*ι (D p v)-ι (delta (a p v))*(ι (c p v)*ι (c p v))≠-1 := by
    rw [hDelta,show ι (D p v)*ι (D p v)-((ι (a p v)+2)^2-1)*(ι (c p v)*ι (c p v))=
      ι (D p v)^2-((ι (a p v)+2)^2-1)*ι (c p v)^2 by ring]
    exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _
  have hprod : (ι (D p v)*ι (D p v)-ι (delta (a p v))*(ι (c p v)*ι (c p v)))*(3*B+1)*Nt=1 := by
    linear_combination hz
  obtain ⟨hN1,h3B,hNt1⟩ := units_three model_discrete hprod hN1ne
    (three_mul_add_one_ne model_discrete B)
  have hB0 : B=0 := by
    have h3 : (3:DiffRing V)*B=0 := by linear_combination h3B
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  -- the main norm, the transport unit and the scalar window
  have hmain : D p v*D p v=1+delta (a p v)*c p v*c p v := by
    apply ι_injective
    simp only [map_mul,map_add,map_one]
    linear_combination hN1
  have hqb : q p v-1=(p 0:V)*v 0 := by unfold q; exact add_tsub_cancel_right _ _
  have htrans : ((p 1:V)+v 8)*q p v+q p v=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*(q p v-1)+1 := by
    apply ι_injective
    rw [hqb]
    simp only [map_mul,map_add,map_one,map_natCast]
    rw [hNt] at hNt1
    linear_combination hNt1
  obtain ⟨hgap,hR24,hRE⟩ := ArithmeticPellFirstIndex.scalar_window (q p v) (p 0:V) (p 1:V)
    (p 2:V) (p 3:V) (v 0) (v 1) (v 2) (v 3) (v 8) (v 7) hb0 (hv 0) (hv 1) (hv 2) (hv 3)
    (hv 8) (hv 7) hl hh rfl htrans
  have hmask : v 1+v 2<q p v := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hFq : v 1≤q p v := le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) (le_of_lt hmask)
  have hRE' : R p v+2<E p v := by
    have he : v 8*v 7*q p v^4=E p v := by unfold E X Y; ring
    rw [←he]; exact hRE
  have hq21 : 1≤q p v^2 := one_le_pow₀ hq1
  have hRι : ι (R p v)=R0 := by
    rw [hR0]
    simp only [R,map_add,map_mul,map_natCast,ι_tsub hq1,ι_tsub hFq,ι_tsub hq21,map_pow,map_one]
    rw [hqι]
    ring
  -- the cleared rational relation `(Q - 1) t² = E² A F2 (Q V² - 1)`
  have hVι : Vr=ι (F2 p v*c p v*v 6)-ι (F2 p v*R p v+c p v) := by
    rw [hVr,←hRι]; simp only [map_mul,map_add]; ring
  obtain ⟨Vb,hVbdef⟩ : ∃ x : V,
      x=ArithmeticPellHalfIndex.absdiff (F2 p v*c p v*v 6) (F2 p v*R p v+c p v) := ⟨_,rfl⟩
  have hVb : ι Vb=|Vr| := by rw [hVbdef,hVι]; exact ι_absdiff _ _
  have hQW : ι (Q p v)=ι (delta (a p v))*ι (W p v) := by simp only [Q,map_mul]
  have hBrel : (ι (Q p v)-1)*(t*t)=ι (E p v)*ι (E p v)*(ι (A p v)*ι (F2 p v))*
      (ι (Q p v)*(Vr*Vr)-1) := by
    rw [hB] at hB0
    rw [hQW]
    linear_combination hB0
  have hQι1 : (1:DiffRing V)≤ι (Q p v) := by simpa only [map_one] using ι_le_ι.mpr hQ1
  have hF20 : 0<F2 p v := lt_of_lt_of_le _root_.zero_lt_one le_self_add
  have hVr0 : Vr≠0 := by
    intro h0
    rw [h0] at hBrel
    have h1 : 0≤(ι (Q p v)-1)*(t*t) := mul_nonneg (by linarith) (mul_self_nonneg t)
    have h2 : (0:DiffRing V)<ι (E p v)*ι (E p v)*(ι (A p v)*ι (F2 p v)) :=
      mul_pos (mul_pos (ι_pos hE0) (ι_pos hE0)) (mul_pos (ι_pos hA0) (ι_pos hF20))
    nlinarith
  have hVb1 : 1≤Vb := by
    have h := abs_ge_one model_discrete hVr0
    rw [←hVb] at h
    exact ι_le_ι.mp (by simpa only [map_one] using h)
  have hVV : ι Vb*ι Vb=Vr*Vr := by rw [hVb]; exact abs_mul_abs_self Vr
  obtain ⟨T0,hT0⟩ := nonneg_iff.mp (abs_nonneg t)
  have hQV1 : 1≤Q p v*Vb*Vb := one_le_mul (one_le_mul hQ1 hVb1) hVb1
  have hVnat : (Q p v-1)*(T0*T0)=(E p v*E p v)*((A p v*F2 p v)*(Q p v*Vb*Vb-1)) := by
    apply ι_injective
    have hTT : |t| * |t|=t*t := abs_mul_abs_self t
    simp only [map_mul,ι_tsub hQ1,ι_tsub hQV1,map_one,←hT0]
    linear_combination hBrel+(ι (Q p v)-1)*hTT-
      ι (E p v)*ι (E p v)*(ι (A p v)*ι (F2 p v))*ι (Q p v)*hVV
  -- coprimality of `A` and `F2` with `Q - 1` and `Q V² - 1`
  have hQA : ι (Q p v)=ι (A p v)*ι (delta (a p v)*W0 p v) := by
    simp only [Q,W,map_mul]; ring
  have hAδ : Bez (A p v) (Q p v-1) 1 := by
    apply bez_of_ring _ _ (ι (delta (a p v)*W0 p v)) (-1)
    rw [ι_tsub hQ1,map_one,hQA]; ring
  have hAD : Bez (A p v) (Q p v*Vb*Vb-1) 1 := by
    apply bez_of_ring _ _ (ι (delta (a p v)*W0 p v)*ι Vb*ι Vb) (-1)
    rw [ι_tsub hQV1,map_one,show ι (Q p v*Vb*Vb)=ι (Q p v)*ι Vb*ι Vb by simp only [map_mul],hQA]
    ring
  -- `(a + 2) D L = W = F2 - 1`, so `D` and `a + 2` are units modulo `F2`
  obtain ⟨L,hL⟩ : ∃ x : V, x=v 5*(c p v*c p v)*A p v*(m p v*(delta (a p v)*(c p v*c p v))) :=
    ⟨_,rfl⟩
  have hF2ι : ι (F2 p v)=1+ι (W p v) := by simp only [F2,map_add,map_one]
  have hW' : ι (F2 p v)-1=(ι (a p v)+2)*ι (D p v)*ι L := by
    rw [hF2ι,hL]; simp only [W,W0,m,map_mul,map_add,map_ofNat]; ring
  have hWF : ι (W p v)=ι (F2 p v)-1 := by rw [hF2ι]; ring
  have hDeltaa : ι (delta (a p v))+1=(ι (a p v)+2)*(ι (a p v)+2) := by rw [hDelta]; ring
  have hFδ : Bez (F2 p v) (Q p v-1) 1 := by
    apply bez_of_ring _ _ (ι (delta (a p v))*(ι (D p v)*ι L)*(ι (D p v)*ι L)-ι (F2 p v)+2)
      (-((ι (D p v)*ι L)*(ι (D p v)*ι L)))
    rw [ι_tsub hQ1,map_one,hQW,hWF]
    linear_combination (ι (D p v)*ι L)*(ι (D p v)*ι L)*hDeltaa+
      (-(ι (F2 p v)-1+(ι (a p v)+2)*(ι (D p v)*ι L)))*hW'
  have hFD : Bez (F2 p v) (Q p v*Vb*Vb-1) 1 := by
    obtain ⟨u,hu⟩ : ∃ x : DiffRing V, x=ι (c p v)*ι (v 6)-R0 := ⟨_,rfl⟩
    obtain ⟨Mp,hMp⟩ : ∃ x : DiffRing V, x=(ι (a p v)+2)*ι L := ⟨_,rfl⟩
    obtain ⟨Z,hZ⟩ : ∃ x : DiffRing V, x=ι (delta (a p v))*(ι (F2 p v)*ι (F2 p v)*u*u-
      2*ι (F2 p v)*u*ι (c p v)+ι (c p v)*ι (c p v)-ι (F2 p v)*u*u+2*u*ι (c p v)) := ⟨_,rfl⟩
    apply bez_of_ring _ _ (Z*(Mp*Mp)-ι (F2 p v)+2) (-(Mp*Mp))
    rw [ι_tsub hQV1,map_one,map_mul,map_mul,mul_assoc (ι (Q p v)),hVV,hQW,hWF,hVr,←hu,hZ]
    have hW'' : ι (F2 p v)-1=ι (D p v)*Mp := by rw [hW',hMp]; ring
    linear_combination (-(ι (D p v)*Mp+ι (F2 p v)-1))*hW''+(-(Mp*Mp))*hN1
  have hBG : Bez (A p v*F2 p v) ((Q p v-1)*(Q p v*Vb*Vb-1)) 1 :=
    ModelProductPell.pp_bez_symm (bez_mul (ModelProductPell.pp_bez_symm (bez_mul hAδ hAD))
      (ModelProductPell.pp_bez_symm (bez_mul hFδ hFD)))
  obtain ⟨g,hg⟩ := TenPositiveScaledSquare.scaled_product_factor_square (Q p v-1) T0 (E p v)
    (A p v*F2 p v) (Q p v*Vb*Vb-1) hE0 hBG hVnat
  have hAF : Bez (A p v) (F2 p v) 1 := ModelProductPell.pp_bez_one_add (A p v) (W0 p v)
  obtain ⟨tau,htauA⟩ := ModelProductPell.pp_square_of_coprime (A p v) (F2 p v) g hAF hg
  obtain ⟨f,hfF⟩ := ModelProductPell.pp_square_of_coprime (F2 p v) (A p v) g
    (ModelProductPell.pp_bez_symm hAF) (by rw [mul_comm]; exact hg)
  have htau0 : 0<tau := pos_of_mul_pos_left (by rw [←htauA]; exact hA0) (Arithmetic.zero_le _)
  have hf0 : 0<f := pos_of_mul_pos_left (by rw [←hfF]; exact hF20) (Arithmetic.zero_le _)
  -- rational adjacent-Pell integrality: `|t| = E τ f y`
  have hQ2 : 2≤Q p v := by
    have hd3 : (3:V)≤delta (a p v) := by
      unfold delta
      simpa only [one_mul] using mul_le_mul (show (1:V)≤a p v+1 by simp)
        (show (3:V)≤a p v+3 by simp) (by simp) (by simp)
    exact le_trans (by norm_num) (le_trans hd3 (le_mul_of_one_le_right (Arithmetic.zero_le _)
      (pos_iff_one_le.mp hW0)))
  have hB1 : 0<Q p v-1 := tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) hQ2)
  obtain ⟨y,hT0y,hnorm⟩ := TenPositiveAdjacentInteger.quotient_of_scaled_norm (Q p v-1)
    (E p v*tau*f) Vb T0 hB1 (mul_pos (mul_pos hE0 htau0) hf0) (lt_of_lt_of_le _root_.zero_lt_one hVb1)
    (by
      apply ι_injective
      have h := congrArg ι hVnat
      simp only [map_mul,map_add,ι_tsub hQ1,ι_tsub hQV1,map_one] at h ⊢
      rw [htauA,hfF] at h
      simp only [map_mul] at h
      linear_combination -h)
  rw [add_tsub_cancel_of_le hQ1] at hnorm
  have hy0 : 0<y := by
    rcases eq_zero_or_pos y with h0|h0
    · exfalso
      rw [h0,mul_zero,mul_zero] at hnorm
      have h4 : (2:V)≤Q p v*(Vb*Vb) := by
        calc (2:V)=2*(1*1) := by norm_num
          _≤Q p v*(Vb*Vb) := mul_le_mul hQ2 (mul_le_mul hVb1 hVb1 (by simp) (by simp))
            (by simp) (by simp)
      rw [hnorm] at h4
      exact absurd h4 (by norm_num)
    · exact h0
  -- `t > 0`, so `t = E τ f y` and `k ≡ R + 1 (mod E)`
  have htpos : 0<t := by
    rw [ht,←hRι]
    have h1 : (1:DiffRing V)≤ι (v 4) := by simpa only [map_one] using ι_le_ι.mpr (pos_iff_one_le.mp (hv 4))
    have h2 : (2:DiffRing V)≤ι (k v) := two_le_ι hk2
    have h3 : ι (R p v)+2<ι (E p v) := by simpa only [map_add,map_ofNat] using ι_lt_ι.mpr hRE'
    have h4 : (0:DiffRing V)≤ι (E p v) := ι_nonneg _
    nlinarith
  have htι : t=ι (E p v)*ι tau*ι f*ι y := by
    rw [←abs_of_pos htpos,hT0,hT0y]; simp only [map_mul]
  have hRlt : R p v+1<E p v := lt_trans (lt_add_one _) (by
    simpa only [add_assoc,one_add_one_eq_two] using hRE')
  have hkmod : k v%E p v=R p v+1 := by
    apply mod_of_cong hE0 hRlt
    refine ⟨ι tau*ι f*ι y-ι (v 4),?_⟩
    simp only [map_add,map_one]
    rw [ht,←hRι] at htι
    linear_combination htι
  -- the Carrier65 carrier
  have hfirst : tau*tau=1+((X p v*Y p v)*Y p v)*((X p v*Y p v)*Y p v+1)*k v*k v := by
    rw [←htauA]; exact A_first p v
  have hmainR : D p v*D p v=1+delta (X p v*Y p v+Y p v)*(k v*Y p v+v 9)*(k v*Y p v+v 9) :=
    hmain
  have hstrict : f*f=1+delta (a p v)*((tau*m p v)*c p v*c p v)*((tau*m p v)*c p v*c p v) := by
    rw [←hfF]; unfold F2 W W0; rw [htauA]; ring
  have hII : Q p v=(delta (a p v)*(tau*m p v)*c p v*c p v)*(delta (a p v)*(tau*m p v)*c p v*c p v) := by
    unfold Q W W0; rw [htauA]; ring
  have haux : (delta (a p v)*(tau*m p v)*c p v*c p v)*(delta (a p v)*(tau*m p v)*c p v*c p v)*
      ArithmeticPellHalfIndex.absdiff (f*f*c p v*v 6) (f*f*R p v+c p v)*
      ArithmeticPellHalfIndex.absdiff (f*f*c p v*v 6) (f*f*R p v+c p v)+y*y=
      1+(delta (a p v)*(tau*m p v)*c p v*c p v)*(delta (a p v)*(tau*m p v)*c p v*c p v)*y*y := by
    rw [←hfF,←hVbdef,←hII]
    have h1 : (Q p v-1)*(y*y)+y*y=Q p v*(y*y) := by
      rw [←add_one_mul,tsub_add_cancel_of_le hQ1]
    calc Q p v*Vb*Vb+y*y=Q p v*(Vb*Vb)+y*y := by ring
      _=1+(Q p v-1)*(y*y)+y*y := by rw [hnorm]
      _=1+Q p v*(y*y) := by rw [add_assoc,h1]
      _=1+Q p v*y*y := by ring
  have hτm0 : 0<tau*m p v := mul_pos htau0 hm0
  obtain ⟨N,hN0,hN⟩ := Q170Residue.carrier_of_residue (X p v) (Y p v) (k v) (v 9) (D p v)
    f (tau*m p v) (R p v) y (v 6) tau (E p v) hX16 hY4 (hv 9) hketa hf0 hτm0 hy0 hR24
    hRE' (dvd_refl _) hfirst hmainR hstrict haux (Or.inl hkmod)
  have hN' : E p v*N+k v=tau+R p v := hN
  have htauN : E p v*N+k v-R p v=tau := by rw [hN']; exact add_tsub_cancel_right _ _
  refine ⟨![v 0,v 1,v 2,v 3,f,tau*m p v,v 6,v 7,v 8,N,v 9,v 10,y,v 11],?_,?_⟩
  · intro j
    fin_cases j
    exacts [hv 0,hv 1,hv 2,hv 3,hf0,hτm0,hv 6,hv 7,hv 8,hN0,hv 9,hv 10,hy0,hv 11]
  · refine ⟨htrans,?_,hmain,hstrict,haux⟩
    change (E p v*N+k v-R p v)*(E p v*N+k v-R p v)=1+(E p v*Y p v)*(E p v*Y p v+1)*k v*k v
    rw [htauN]
    exact hfirst

/-- **Zero ⇒ halt** for the 74 carrier at the direct-BFS943 ports. -/
theorem zero_halts (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀ j, 0<v j)
    (hz : value74 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  obtain ⟨u,hu,he⟩ := equations_of_zero p v h31 hl hh hv hz
  exact Carrier65BFSSource.equations_halt p u hp0 hp1 hp2 hp3 hu he

#print axioms Q170Sound74.bez_of_ring
#print axioms Q170Sound74.equations_of_zero
#print axioms Q170Sound74.zero_halts
end Q170Sound74
