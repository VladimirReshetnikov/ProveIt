import DiophantineConsistency.BFS943.Q170Syntax72
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
import DiophantineConsistency.BFS943.Q170Units
import DiophantineConsistency.BFS943.Q170Residue
import DiophantineConsistency.BFS943.Carrier65BFSSource
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelCarrierScaled

/-! # Soundness of package 170's 72/154 q⁴ residue carrier

In every model of `𝗜𝚺₁`, a positive zero `v` of `Q170Form72.value72` (in the
model's ring of differences) at ports with `31 ≤ β`, `MC < β`, `MF < 2β`
gives a positive solution of Carrier65's five equations
(`ArithmeticCarrierSoundness2011.Equations`), at

  `u = (J, F, α, z, f, m, T, s, w, N, η, ζ, y, γ)`, `m = q² i A`,

(`FIXED_CARRIER_PROOF.md` §6.1, with §3–§5 at the modulus `q⁴`):

1. the four factors are units; the norm and mod-3 exclusions give
   `N1 = Nt = 3 B + 1 = Ns = 1` (`Q170Units.units_four`);
2. `Ns = 1` gives `Q = S²` with `S = Δ m c²`, so `B = 0` reads
   `(S² - 1) t² = A (S² V² - 1)`; `Q170Units.square_extraction` gives
   `A = τ²`, `t = ± τ y` and the auxiliary norm with `y > 0`;
3. `y ≡ ±1 (mod 4 S²)` (`Q170Units.aux_residue`), `q⁴ ∣ 4 S²`, and `τ ≡ 1 (mod q⁴)`
   (first Pell classification, `q⁴ ∣ E`) give `k - R ≡ ±1 (mod q⁴)`, and the rank
   window gives `R + 2 < q⁴` (`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`);
4. `Q170Residue.carrier_of_residue` (modulus `q⁴`) gives `E N + k = τ + R` with `N > 0`, i.e.
   Carrier65's carrier `τ = E N + k - R`.

`zero_halts` composes with `Carrier65BFSSource.equations_halt` at the
direct-BFS943 ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace Q170Sound72
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
  Q170Form72 Q170Units ArithmeticPellRecurrence ArithmeticOddOrdinateResidue
open ArithmeticCarrierSoundness2011 (Equations)
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat
  lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Defs
variable (p : Fin 4 → ℕ) (v : Fin 13 → V)
/-- The natural registers of a positive assignment. -/
def q : V := (p 0:V)*v 0+1
def X : V := v 9*q p v
def Y : V := v 8*q p v^3
def E : V := X p v*Y p v
def k : V := v 10+v 11
def c : V := k v*Y p v+v 10
def a : V := E p v+Y p v
def A : V := (E p v*k v*Y p v)*((E p v*k v*Y p v)+k v)+1
def m : V := q p v*q p v*v 6*A p v
def D : V := X p v+a p v*c p v+v 12*(4*a p v+3)
def S : V := delta (a p v)*m p v*c p v*c p v
def R : V := ((q p v-1)*(q p v-v 1)+v 2)*(q p v^2-1)+((p 2:V)+q p v*(p 3:V))*v 0
end Defs

theorem A_first (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    A p v=1+((X p v*Y p v)*Y p v)*((X p v*Y p v)*Y p v+1)*k v*k v := by
  unfold A E; ring

/-- **Soundness of the 72 carrier**: a positive zero gives the five Carrier65 equations. -/
theorem equations_of_zero (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j, 0<v j)
    (hz : value72 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0) :
    ∃ u : Fin 14 → V, (∀ j, 0<u j) ∧ Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) u := by
  have hb0 : (0:V)<(p 0:V) := lt_of_lt_of_le (by norm_num) hb31
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  -- positivity of the natural registers
  have hq32 : (32:V)≤q p v := by
    unfold q
    calc (32:V)=31*1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := add_le_add (mul_le_mul hb31 (pos_iff_one_le.mp (hv 0)) (by simp)
          (by simp)) le_rfl
  have hq1 : 1≤q p v := le_trans (by norm_num) hq32
  have hX16 : (16:V)≤X p v := le_trans (le_trans (by norm_num) hq32)
    (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 9)))
  have hq3 : 1≤q p v^3 := one_le_pow₀ hq1
  have hY4 : (4:V)≤Y p v := by
    have h1 : q p v≤q p v^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hq1 (by norm_num : 1≤3)
    exact le_trans (le_trans (by norm_num) hq32) (le_trans h1
      (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 8))))
  have hX0 : 0<X p v := lt_of_lt_of_le (by norm_num) hX16
  have hY0 : 0<Y p v := lt_of_lt_of_le (by norm_num) hY4
  have hE0 : 0<E p v := mul_pos hX0 hY0
  have hk0 : 0<k v := add_pos (hv 10) (hv 11)
  have hketa : v 10<k v := lt_add_of_pos_right _ (hv 11)
  have hc0 : 0<c p v := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 10)
  have hA0 : 0<A p v := by unfold A; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hq0 : 0<q p v := lt_of_lt_of_le (by norm_num) hq32
  have hm0 : 0<m p v := mul_pos (mul_pos (mul_pos hq0 hq0) (hv 6)) hA0
  have hd3 : (3:V)≤delta (a p v) := by
    unfold delta
    simpa only [one_mul] using mul_le_mul (show (1:V)≤a p v+1 by simp)
      (show (3:V)≤a p v+3 by simp) (by simp) (by simp)
  have hS2 : 2≤S p v := by
    unfold S
    have h1 : 1≤m p v*c p v*c p v := one_le_mul (one_le_mul (pos_iff_one_le.mp hm0)
      (pos_iff_one_le.mp hc0)) (pos_iff_one_le.mp hc0)
    calc (2:V)≤3 := by norm_num
      _≤delta (a p v) := hd3
      _≤delta (a p v)*(m p v*c p v*c p v) := le_mul_of_one_le_right (by simp) h1
      _=delta (a p v)*m p v*c p v*c p v := by ring
  -- the factorization of the circuit in the ring of differences
  obtain ⟨R0,hR0⟩ : ∃ x : DiffRing V, x=(((p 0:ℕ):DiffRing V)*ι (v 0)*(ι (q p v)-ι (v 1))+
      ι (v 2))*(ι (q p v)*ι (q p v)-1)+(((p 2:ℕ):DiffRing V)+ι (q p v)*((p 3:ℕ):DiffRing V))*
      ι (v 0) := ⟨_,rfl⟩
  obtain ⟨t,ht⟩ : ∃ x : DiffRing V, x=ι (q p v)*ι (q p v)*(ι (q p v)*ι (q p v))*ι (v 5)-ι (k v)+R0 :=
    ⟨_,rfl⟩
  obtain ⟨Nt,hNt⟩ : ∃ x : DiffRing V, x=(((p 1:ℕ):DiffRing V)+ι (v 9))*
      (ι (q p v)-ι (v 1)-ι (v 2))+(ι (q p v)-ι (v 1))-ι (v 3)*(((p 0:ℕ):DiffRing V)*ι (v 0)) :=
    ⟨_,rfl⟩
  obtain ⟨Vr,hVr⟩ : ∃ x : DiffRing V, x=ι (v 4*v 4)*(ι (c p v)*ι (v 7)-R0)-ι (c p v) :=
    ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃ x : DiffRing V, x=ι (delta (a p v))*(ι (v 4*v 4)-1)*(t*t-ι (A p v)*(Vr*Vr))-
      t*t+ι (A p v) := ⟨_,rfl⟩
  have hqι : ι (q p v)=((p 0:ℕ):DiffRing V)*ι (v 0)+1 := by
    simp only [q,map_add,map_mul,map_one,map_natCast]
  rw [value72_factors (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j)) (ι (q p v)) (ι (X p v))
    (ι (Y p v)) (ι (E p v)) (ι (k v)) (ι (A p v)) (ι (c p v)) (ι (a p v)) (ι (4*a p v+3))
    (ι (delta (a p v))) (ι (D p v)) R0 t Nt (ι (m p v)) (ι (S p v)) (ι (m p v*c p v*c p v))
    (ι (v 4*v 4)) Vr B hqι (by simp only [X,map_mul]) (by simp only [Y,map_mul,map_pow]; ring)
    (by simp only [E,map_mul]) (by simp only [k,map_add])
    (by simp only [A,map_add,map_mul,map_one]; ring) (by simp only [c,map_add,map_mul])
    (by simp only [a,map_add]) (by simp only [map_add,map_mul,map_ofNat])
    (by simp only [delta,map_add,map_mul,map_one,map_ofNat]; ring)
    (by simp only [D,map_add,map_mul,map_ofNat]) hR0 ht hNt
    (by simp only [m,map_mul]) (by simp only [S,map_mul]; ring) (by simp only [map_mul]; ring)
    (by simp only [map_mul]) hVr hB] at hz
  -- the four factors are units
  obtain ⟨φ⟩ : Nonempty (DiffRing V →+* ZMod 4) := ⟨mod4⟩
  have hDelta : ι (delta (a p v))=(ι (a p v)+2)^2-1 := by
    simp only [delta,map_add,map_mul,map_one,map_ofNat]; ring
  have hN1ne : ι (D p v)*ι (D p v)-ι (delta (a p v))*(ι (c p v)*ι (c p v))≠-1 := by
    rw [hDelta,show ι (D p v)*ι (D p v)-((ι (a p v)+2)^2-1)*(ι (c p v)*ι (c p v))=
      ι (D p v)^2-((ι (a p v)+2)^2-1)*ι (c p v)^2 by ring]
    exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _
  have hSm : ι (S p v)=ι (delta (a p v))*(ι (m p v*c p v*c p v)) := by
    simp only [S,map_mul]; ring
  have hNsne : ι (v 4*v 4)-ι (m p v*c p v*c p v)*ι (S p v)≠-1 := by
    rw [hSm,hDelta,show ι (v 4*v 4)-ι (m p v*c p v*c p v)*(((ι (a p v)+2)^2-1)*
      ι (m p v*c p v*c p v))=ι (v 4)^2-((ι (a p v)+2)^2-1)*ι (m p v*c p v*c p v)^2 by
        simp only [map_mul]; ring]
    exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _
  have hprod : (ι (D p v)*ι (D p v)-ι (delta (a p v))*(ι (c p v)*ι (c p v)))*(3*B+1)*Nt*
      (ι (v 4*v 4)-ι (m p v*c p v*c p v)*ι (S p v))=1 := by
    linear_combination hz
  obtain ⟨hN1,h3B,hNt1,hNs⟩ := units_four model_discrete hprod hN1ne
    (three_mul_add_one_ne model_discrete B) hNsne
  have hB0 : B=0 := by
    have h3 : (3:DiffRing V)*B=0 := by linear_combination h3B
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  -- the main and strong norms in the model
  have hmain : D p v*D p v=1+delta (a p v)*c p v*c p v := by
    apply ι_injective
    simp only [map_mul,map_add,map_one]
    linear_combination hN1
  have hstrict : v 4*v 4=1+delta (a p v)*(m p v*c p v*c p v)*(m p v*c p v*c p v) := by
    apply ι_injective
    have h := hNs
    rw [hSm] at h
    simp only [map_mul,map_add,map_one] at h ⊢
    linear_combination h
  -- the transport unit and the scalar window
  have hqb : q p v-1=(p 0:V)*v 0 := by unfold q; exact add_tsub_cancel_right _ _
  have htrans : ((p 1:V)+v 9)*q p v+q p v=((p 1:V)+v 9)*(v 1+v 2)+v 1+v 3*(q p v-1)+1 := by
    apply ι_injective
    rw [hqb]
    simp only [map_mul,map_add,map_one,map_natCast]
    rw [hNt] at hNt1
    linear_combination hNt1
  obtain ⟨hgap,hR24,hRE⟩ := ArithmeticPellFirstIndex.scalar_window (q p v) (p 0:V) (p 1:V)
    (p 2:V) (p 3:V) (v 0) (v 1) (v 2) (v 3) (v 9) (v 8) hb0 (hv 0) (hv 1) (hv 2) (hv 3)
    (hv 9) (hv 8) hl hh rfl htrans
  have hmask : v 1+v 2<q p v := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hFq : v 1≤q p v := le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) (le_of_lt hmask)
  have hRE' : R p v+2<E p v := by
    have he : v 9*v 8*q p v^4=E p v := by unfold E X Y; ring
    rw [←he]; exact hRE
  have hq21 : 1≤q p v^2 := one_le_pow₀ hq1
  have hRι : ι (R p v)=R0 := by
    rw [hR0]
    simp only [R,map_add,map_mul,map_natCast,ι_tsub hq1,ι_tsub hFq,ι_tsub hq21,map_pow,map_one]
    rw [hqι]
    ring
  -- the auxiliary carrier, the multiplier square and the auxiliary norm
  have hVι : Vr=ι (v 4*v 4*c p v*v 7)-ι (v 4*v 4*R p v+c p v) := by
    rw [hVr,←hRι]; simp only [map_mul,map_add]; ring
  let Vb : V := ArithmeticPellHalfIndex.absdiff (v 4*v 4*c p v*v 7) (v 4*v 4*R p v+c p v)
  have hVb : ι Vb=|Vr| := by rw [hVι]; exact ι_absdiff _ _
  have hQS : ι (delta (a p v))*(ι (v 4*v 4)-1)=ι (S p v)*ι (S p v) := by
    have h1 : ι (v 4*v 4)-1=ι (m p v*c p v*c p v)*ι (S p v) := by linear_combination hNs
    rw [h1,hSm]; ring
  have hBrel : (ι (S p v)*ι (S p v)-1)*(t*t)=ι (A p v)*(ι (S p v)*ι (S p v)*(Vr*Vr)-1) := by
    rw [hB,hQS] at hB0
    linear_combination hB0
  have hSι : (2:DiffRing V)≤ι (S p v) := two_le_ι hS2
  have hVr0 : Vr≠0 := by
    intro h0
    rw [h0] at hBrel
    have h1 : 0≤(ι (S p v)*ι (S p v)-1)*(t*t) :=
      mul_nonneg (by nlinarith) (mul_self_nonneg t)
    have h2 : (0:DiffRing V)<ι (A p v) := ι_pos hA0
    nlinarith
  have hVb1 : 1≤Vb := by
    have h := abs_ge_one model_discrete hVr0
    rw [←hVb] at h
    exact ι_le_ι.mp (by simpa only [map_one] using h)
  obtain ⟨T0,hT0⟩ := nonneg_iff.mp (abs_nonneg t)
  have hS1 : 1≤S p v*S p v := one_le_mul (le_trans (by norm_num) hS2) (le_trans (by norm_num) hS2)
  have hSV1 : 1≤S p v*S p v*Vb*Vb := one_le_mul (one_le_mul hS1 hVb1) hVb1
  have hVnat : (S p v*S p v-1)*(T0*T0)=A p v*(S p v*S p v*Vb*Vb-1) := by
    apply ι_injective
    have hTT : |t| * |t|=t*t := abs_mul_abs_self t
    have hVV : |Vr| * |Vr|=Vr*Vr := abs_mul_abs_self Vr
    simp only [map_mul,ι_tsub hS1,ι_tsub hSV1,map_one,←hT0,hVb]
    linear_combination hBrel+(ι (S p v)*ι (S p v)-1)*hTT-ι (A p v)*ι (S p v)*ι (S p v)*hVV
  have hAS : A p v∣S p v := ⟨delta (a p v)*(q p v*q p v)*v 6*c p v*c p v,by unfold S m; ring⟩
  obtain ⟨tau,y,htau0,hAtau,hT0y,hyrel⟩ := square_extraction (S p v) (A p v) Vb T0 hS2 hA0 hAS
    hVb1 hVnat
  have hy0 : 0<y := by
    rcases eq_zero_or_pos y with h0|h0
    · exfalso
      rw [h0,mul_zero] at hT0y
      rw [hT0y,mul_zero,mul_zero] at hVnat
      have h1 : S p v*S p v*Vb*Vb-1=0 := by
        rcases mul_eq_zero.mp hVnat.symm with h2|h2
        · exact absurd h2 (ne_of_gt hA0)
        · exact h2
      have h4 : (4:V)≤S p v*S p v*Vb*Vb := by
        calc (4:V)=2*2*1*1 := by norm_num
          _≤S p v*S p v*Vb*Vb := mul_le_mul (mul_le_mul (mul_le_mul hS2 hS2 (by simp) (by simp))
            hVb1 (by simp) (by simp)) hVb1 (by simp) (by simp)
      have h5 := tsub_eq_zero_iff_le.mp h1
      exact absurd (le_trans h4 h5) (by norm_num)
    · exact h0
  have haux : S p v*S p v*Vb*Vb+y*y=1+S p v*S p v*y*y := by
    apply ι_injective
    have h := congrArg ι hyrel
    simp only [map_mul,ι_tsub hS1,ι_tsub hSV1,map_one,map_add] at h ⊢
    linear_combination -h
  -- residues modulo E
  have hfirst : tau*tau=1+((X p v*Y p v)*Y p v)*((X p v*Y p v)*Y p v+1)*k v*k v := by
    rw [←hAtau]; exact A_first p v
  let Q : V := E p v*Y p v
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE0 hY0))
  have hn0 : tau*tau=1+ArithmeticPellFirstNorm.discriminant (Q-1)*k v*k v := by
    have hd : ArithmeticPellFirstNorm.discriminant (Q-1)=Q*(Q+1) := by
      unfold ArithmeticPellFirstNorm.discriminant
      rw [show Q-1+2=(Q-1+1)+1 by ring,hQ1]
    rw [hd]; exact hfirst
  obtain ⟨_,r,_,_,_,_,htr,_⟩ := ArithmeticPellFirstNorm.solution_residues (Q-1) tau (k v) hn0
  rw [hQ1] at htr
  have htauι : ι tau=1+ι (q p v^4)*(2*ι (v 9*v 8)*ι (Y p v)*ι r) := by
    rw [htr]; simp only [Q,E,X,Y,map_add,map_mul,map_one,map_ofNat,map_pow]; ring
  have hres_y : ∃ w0 : DiffRing V, ∃ σ : DiffRing V, (σ=1 ∨ σ=-1) ∧
      ι y=σ+ι (q p v^4)*w0 := by
    have hES : ι (4*S p v*S p v)=ι (q p v^4)*(4*ι (delta (a p v)*v 6*A p v*c p v*c p v)*
        ι (delta (a p v)*v 6*A p v*c p v*c p v)) := by
      simp only [S,m,map_mul,map_ofNat,map_pow]; ring
    rcases aux_residue (S p v) Vb y hS2 hyrel hSV1 with ⟨w1,hw1⟩|⟨w1,hw1⟩
    · refine ⟨4*ι (delta (a p v)*v 6*A p v*c p v*c p v)*
        ι (delta (a p v)*v 6*A p v*c p v*c p v)*w1,1,Or.inl rfl,?_⟩
      rw [hES] at hw1; linear_combination hw1
    · refine ⟨4*ι (delta (a p v)*v 6*A p v*c p v*c p v)*
        ι (delta (a p v)*v 6*A p v*c p v*c p v)*w1,-1,Or.inr rfl,?_⟩
      rw [hES] at hw1; linear_combination hw1
  obtain ⟨w0,σ,hσ,hyι⟩ := hres_y
  have htι : t=ι (q p v^4)*ι (v 5)-ι (k v)+ι (R p v) := by
    rw [ht,hRι]; simp only [map_pow]; ring
  have hTt : ι T0=ι tau*ι y := by rw [hT0y,map_mul]
  -- `k - R ≡ ε (mod q⁴)` with `ε = ±1`, and `R + 2 < q⁴`
  obtain ⟨-,hup⟩ := ArithmeticAdaptiveRankWindow2011.scalar_rank_window (q p v) (p 0:V) (p 2:V)
    (p 3:V) (v 0) (v 1) (v 2) hb0 (hv 0) (hv 1) (hv 2) hl hh rfl hmask
  have hRq4 : R p v+2<q p v^4 := by
    have h1 : R p v+2<R p v+q p v^3+q p v+1 := by
      have h2 : (2:V)<q p v+1 := lt_of_lt_of_le (by norm_num : (2:V)<2+1)
        (add_le_add (le_trans (by norm_num : (2:V)≤32) hq32) (le_refl (1:V)))
      calc R p v+2<R p v+(q p v+1) := add_lt_add_of_le_of_lt le_rfl h2
        _≤R p v+q p v^3+q p v+1 := by
          rw [show R p v+q p v^3+q p v+1=R p v+(q p v+1)+q p v^3 by ring]
          exact le_add_of_nonneg_right (Arithmetic.zero_le _)
    exact lt_of_lt_of_le h1 hup
  have hq40 : 0<q p v^4 := pow_pos hq0 4
  have hRlt : R p v+1<q p v^4 := lt_trans (lt_add_one _) (by
    simpa only [add_assoc,one_add_one_eq_two] using hRq4)
  have hRlt' : R p v<q p v^4 := lt_trans (lt_add_one _) hRlt
  have hME : q p v^4∣X p v*Y p v := ⟨v 9*v 8,by unfold X Y; ring⟩
  have hres : k v%q p v^4=R p v+1 ∨ (k v+1)%q p v^4=R p v := by
    let W : DiffRing V := 2*ι (v 9*v 8)*ι (Y p v)*ι r
    have hprod' : ι tau*ι y=σ+ι (q p v^4)*(w0+W*σ+ι (q p v^4)*W*w0) := by
      rw [htauι,hyι]; ring
    rcases abs_choice t with hta|hta <;> rw [hT0,hTt,hprod'] at hta <;> rcases hσ with rfl|rfl
    · -- `t = 1 + E W'`: `k - R ≡ -1`
      right
      apply mod_of_cong hq40 hRlt'
      refine ⟨ι (v 5)-(w0+W*1+ι (q p v^4)*W*w0),?_⟩
      simp only [map_add,map_one]
      linear_combination htι+hta
    · left
      apply mod_of_cong hq40 hRlt
      refine ⟨ι (v 5)-(w0+W*(-1)+ι (q p v^4)*W*w0),?_⟩
      simp only [map_add,map_one]
      linear_combination htι+hta
    · left
      apply mod_of_cong hq40 hRlt
      refine ⟨ι (v 5)+(w0+W*1+ι (q p v^4)*W*w0),?_⟩
      simp only [map_add,map_one]
      linear_combination htι-hta
    · right
      apply mod_of_cong hq40 hRlt'
      refine ⟨ι (v 5)+(w0+W*(-1)+ι (q p v^4)*W*w0),?_⟩
      simp only [map_add,map_one]
      linear_combination htι-hta
  -- the Carrier65 carrier
  have hmainR : D p v*D p v=1+delta (X p v*Y p v+Y p v)*(k v*Y p v+v 10)*(k v*Y p v+v 10) :=
    hmain
  obtain ⟨N,hN0,hN⟩ := Q170Residue.carrier_of_residue (X p v) (Y p v) (k v) (v 10) (D p v)
    (v 4) (m p v) (R p v) y (v 7) tau (q p v^4) hX16 hY4 (hv 10) hketa (hv 4) hm0 hy0 hR24
    hRq4 hME hfirst hmainR hstrict haux hres
  have hN' : E p v*N+k v=tau+R p v := hN
  have htauN : E p v*N+k v-R p v=tau := by rw [hN']; exact add_tsub_cancel_right _ _
  refine ⟨![v 0,v 1,v 2,v 3,v 4,m p v,v 7,v 8,v 9,N,v 10,v 11,y,v 12],?_,?_⟩
  · intro j
    fin_cases j
    exacts [hv 0,hv 1,hv 2,hv 3,hv 4,hm0,hv 7,hv 8,hv 9,hN0,hv 10,hv 11,hy0,hv 12]
  · refine ⟨htrans,?_,hmain,hstrict,haux⟩
    change (E p v*N+k v-R p v)*(E p v*N+k v-R p v)=1+(E p v*Y p v)*(E p v*Y p v+1)*k v*k v
    rw [htauN]
    exact hfirst

/-- **Zero ⇒ halt** for the 72 carrier at the direct-BFS943 ports. -/
theorem zero_halts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀ j, 0<v j)
    (hz : value72 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  obtain ⟨u,hu,he⟩ := equations_of_zero p v h31 hl hh hv hz
  exact Carrier65BFSSource.equations_halt p u hp0 hp1 hp2 hp3 hu he

#print axioms Q170Sound72.equations_of_zero
#print axioms Q170Sound72.zero_halts
end Q170Sound72
