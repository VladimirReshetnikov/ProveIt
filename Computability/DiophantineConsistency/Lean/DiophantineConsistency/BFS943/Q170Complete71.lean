import DiophantineConsistency.BFS943.Q170Syntax71
import DiophantineConsistency.BFS943.Carrier65BFSHalt
import DiophantineConsistency.ArithmeticThirteenSeed

/-! # Completeness of package 170's 71/162 residue carrier

In every model of `𝗜𝚺₁`, an internal halting time gives a positive zero of
`Q170Form71.value71` at the direct-BFS943 ports (`FIXED_CARRIER_PROOF.md` §6):

* the outer data of `Carrier65BFSHalt.halt_outer` (the direct-BFS943 packing,
  transport, rank `R ≡ 3 (mod 4)` and the outer Pell seed, whose first root
  `τ = E n₀ + k - R` satisfies `τ² = A`);
* a fresh strong seed whose normalized multiplier is divisible by `A E`
  (`ArithmeticThirteenSeed.strong_index` with `b = A E`), i.e. `m = E j A`;
* the fresh auxiliary seed of that strong pair
  (`ArithmeticThirteenSeed.auxiliary_seed_of`), whose ordinate is
  `≡ -1 (mod 4 I²)` and so `≡ -1 (mod E)`;
* the carrier `n = (τ y + k - R) / E`: `τ ≡ 1` and `k ≡ R + 1 (mod E)`
  (first Pell residues, first index `(R+1)/2`), so `E n - k + R = τ y`.

All four factors are then one. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace Q170Complete71
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Q170Form71 ArithmeticPellRecurrence
  ArithmeticPellCongruences
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b≤a) : ι (a-b)=ι a-ι b := by
  rw [eq_sub_iff_add_eq,←map_add,tsub_add_cancel_of_le h]

/-- **Halt ⇒ zero** for the 71 carrier, at ports with the direct-BFS943 model values. -/
theorem zero_of_halt (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp : Carrier65BFSHalt.PortValues (V:=V) p) :
    ∃ v : Fin 13 → V, (∀ j, 0<v j) ∧
      value71 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0 := by
  obtain ⟨J,F,alpha,z,w,sY,n0,eta,zeta,gamma,u,R,hJ,hF,ha0,hz,hw,hsY,hn0,heta,hzeta,hgamma,
    hq,hX,hR,hW,hmask,hR4,_,hseed⟩ := Carrier65BFSHalt.halt_outer p time hT hp
  obtain ⟨hτ,hd,hc,-,r,hRr,-,hkx⟩ := hseed
  generalize hqq : Exp.exp u=qq at *
  generalize hXX : Exp.exp R=XX at *
  generalize hY : sY*qq^3=Y at *
  generalize hE : XX*Y=E at *
  generalize hk : eta+zeta=k at *
  generalize hcc : k*Y+eta=c at *
  generalize haa : E+Y=a at *
  generalize hdd : XX+a*c+gamma*(4*a+3)=d at *
  -- positivity
  have hq1 : 1≤qq := by rw [←hq]; exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  have hY0 : 0<Y := by
    rw [←hY]; exact mul_pos hsY (pow_pos (lt_of_lt_of_le _root_.zero_lt_one hq1) 3)
  have hXX0 : 0<XX := by rw [←hXX]; exact lt_of_lt_of_le _root_.zero_lt_one (one_le_exp _)
  have hE0 : 0<E := by rw [←hE]; exact mul_pos hXX0 hY0
  have hk0 : 0<k := by rw [←hk]; exact add_pos heta hzeta
  have hc0 : 0<c := by rw [←hcc]; exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) heta
  -- the first root `τ`, `τ² = A`, and its residues
  obtain ⟨tau,htau⟩ : ∃ x : V, x=E*n0+k-R := ⟨_,rfl⟩
  rw [←htau] at hτ
  obtain ⟨A,hA⟩ : ∃ x : V, x=E*(k*Y)*(E*(k*Y)+k)+1 := ⟨_,rfl⟩
  have hA0 : 0<A := by rw [hA]; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hτA : tau*tau=A := by rw [hτ,hA]; ring
  obtain ⟨Q,hQ⟩ : ∃ x : V, x=E*Y := ⟨_,rfl⟩
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (by rw [hQ]; exact mul_pos hE0 hY0))
  have hn0' : tau*tau=1+ArithmeticPellFirstNorm.discriminant (Q-1)*k*k := by
    have hdsc : ArithmeticPellFirstNorm.discriminant (Q-1)=Q*(Q+1) := by
      unfold ArithmeticPellFirstNorm.discriminant
      rw [show Q-1+2=(Q-1+1)+1 by ring,hQ1]
    rw [hdsc,hτ,hQ]
  obtain ⟨tm,r1,s1,_,_,hkt,htr,hks⟩ := ArithmeticPellFirstNorm.solution_residues (Q-1) tau k hn0'
  rw [hQ1] at htr hks
  rw [←hQ] at hkx
  have htm : tm=r+1 := by
    apply index_unique (2*(Q-1)+1)
    have h2 : 2*ycoord tm (2*(Q-1)+1)=2*ycoord (r+1) (2*(Q-1)+1) := hkt.trans hkx
    exact mul_left_cancel₀ (by norm_num : (2:V)≠0) h2
  have hkR : k=R+1+4*Q*s1 := by rw [hks,htm,hRr]; ring
  -- a strong seed with multiplier divisible by `A E`, and its auxiliary seed
  have hcR : c=ycoord R a := hc
  obtain ⟨ts,j,_,hj,hyt⟩ := ArithmeticThirteenSeed.strong_index a (A*E) (ycoord R a)
    (mul_pos hA0 hE0) (by rw [←hcR]; exact hc0)
  obtain ⟨T',u',y,hf,hT',hu',hy,hfn,-,-,hlit,-,haux,hymod⟩ :=
    ArithmeticThirteenSeed.auxiliary_seed_of a R ts (A*E*j) hR4 (mul_pos (mul_pos hA0 hE0) hj) hyt
  rw [←hcR] at hfn hlit haux hymod
  obtain ⟨f,hfdef⟩ : ∃ x : V, x=xcoord ts a := ⟨_,rfl⟩
  rw [←hfdef] at hf hfn hlit
  obtain ⟨m,hm⟩ : ∃ x : V, x=E*j*A := ⟨_,rfl⟩
  have hmi : A*E*j=m := by rw [hm]; ring
  rw [hmi] at hfn haux hymod
  have hm0 : 0<m := by rw [hm]; exact mul_pos (mul_pos hE0 hj) hA0
  -- the carrier `n`: `τ y + k = R + E n`
  obtain ⟨I0,hI0⟩ : ∃ x : V, x=delta a*m*c*c := ⟨_,rfl⟩
  rw [←hI0] at haux hymod
  obtain ⟨w2,hw2⟩ : 4*I0*I0∣y+1 := mod_eq_zero_iff_dvd.mp hymod
  obtain ⟨G,hG⟩ : ∃ x : V, x=delta a*A*j*c*c := ⟨_,rfl⟩
  have hI0G : I0=E*G := by rw [hI0,hG,hm]; ring
  have hG0 : 0<G := by
    rw [hG]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by unfold delta; exact mul_pos (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)) (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)))
      hA0) hj) hc0) hc0
  have hI00 : 0<I0 := by rw [hI0G]; exact mul_pos hE0 hG0
  have hw20 : 0<w2 := by
    rcases eq_zero_or_pos w2 with h0|h0
    · rw [h0,mul_zero] at hw2; exact absurd hw2 (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
    · exact h0
  obtain ⟨n,hn⟩ : ∃ x : V, x=4*G*I0*w2+2*Y*r1*y+4*Y*s1 := ⟨_,rfl⟩
  have hnpos : 0<n := by
    rw [hn]
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (mul_pos (by norm_num) hG0) hI00) hw20) (Arithmetic.zero_le _))
      (Arithmetic.zero_le _)
  have hτy : tau*y+k=R+E*n := by
    calc
      tau*y+k=(1+2*Q*r1)*y+(R+1+4*Q*s1) := by rw [htr,←hkR]
      _=(y+1)+R+E*(2*Y*r1*y+4*Y*s1) := by rw [hQ]; ring
      _=4*I0*I0*w2+R+E*(2*Y*r1*y+4*Y*s1) := by rw [hw2]
      _=R+E*n := by rw [hn,hI0G]; ring
  -- the thirteen coordinates and the four unit factors in the ring of differences
  let v13 : Fin 13 → V := ![J,F,alpha,z,f,n,j,T',sY,w,eta,zeta,gamma]
  have hv13 : ∀ i, 0<v13 i := by
    intro i
    fin_cases i
    exacts [hJ,hF,ha0,hz,hf,hnpos,hj,hT',hsY,hw,heta,hzeta,hgamma]
  refine ⟨v13,hv13,?_⟩
  have hqι : ι qq=((p 0:ℕ):DiffRing V)*ι J+1 := by
    rw [←hq]; simp only [map_add,map_mul,map_one,map_natCast]
  have hFq : F≤qq := le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) (le_of_lt hmask)
  have hq21 : 1≤qq^2 := one_le_pow₀ hq1
  obtain ⟨R0,hR0⟩ : ∃ x : DiffRing V, x=(((p 0:ℕ):DiffRing V)*ι J*(ι qq-ι F)+ι alpha)*
      (ι qq*ι qq-1)+(((p 2:ℕ):DiffRing V)+ι qq*((p 3:ℕ):DiffRing V))*ι J := ⟨_,rfl⟩
  have hRι : R0=ι R := by
    rw [hR0,←hR]
    simp only [map_add,map_mul,map_natCast,ι_tsub hq1,ι_tsub hFq,ι_tsub hq21,map_pow,map_one]
    rw [hqι]
    ring
  obtain ⟨t,ht⟩ : ∃ x : DiffRing V, x=ι E*ι n-ι k+R0 := ⟨_,rfl⟩
  have htι : t=ι tau*ι y := by
    have h := congrArg ι hτy
    simp only [map_add,map_mul] at h
    rw [ht,hRι]
    linear_combination -h
  obtain ⟨Nt,hNt⟩ : ∃ x : DiffRing V, x=(((p 1:ℕ):DiffRing V)+ι w)*(ι qq-ι F-ι alpha)+
      (ι qq-ι F)-ι z*(((p 0:ℕ):DiffRing V)*ι J) := ⟨_,rfl⟩
  have hNt1 : Nt=1 := by
    have h := congrArg ι hW
    simp only [map_add,map_mul,map_natCast,ι_tsub hq1,map_one] at h
    rw [hNt]
    linear_combination h+(ι z)*hqι
  obtain ⟨Vr,hVr⟩ : ∃ x : DiffRing V, x=ι (f*f)*(ι c*ι T'-R0)-ι c := ⟨_,rfl⟩
  have hVu : Vr=ι u' := by
    have h := congrArg ι hlit
    simp only [map_add,map_mul] at h
    rw [hVr,hRι]
    simp only [map_mul]
    linear_combination h
  obtain ⟨S,hS⟩ : ∃ x : V, x=m*(delta a*(c*c)) := ⟨_,rfl⟩
  obtain ⟨I,hI⟩ : ∃ x : V, x=m*(c*c) := ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃ x : DiffRing V, x=ι (delta a)*(ι (f*f)-1)*(t*t-ι A*(Vr*Vr))-t*t+ι A :=
    ⟨_,rfl⟩
  have hN1 : ι d*ι d-ι (delta a)*(ι c*ι c)=1 := by
    have h := congrArg ι hd
    simp only [map_add,map_mul,map_one,map_ofNat] at h
    simp only [delta,map_add,map_mul,map_one,map_ofNat]
    linear_combination h
  have hNs : ι (f*f)-ι I*ι S=1 := by
    have h := congrArg ι hfn
    rw [hI,hS]
    simp only [delta,map_add,map_mul,map_one,map_ofNat] at h ⊢
    linear_combination h
  have hSI0 : S=I0 := by rw [hS,hI0]; ring
  have hB0 : B=0 := by
    have hQS : ι (delta a)*(ι (f*f)-1)=ι S*ι S := by
      have h1 : ι (f*f)-1=ι I*ι S := by linear_combination hNs
      rw [h1,hI,hS]; simp only [map_mul]; ring
    have hτAι : ι tau*ι tau=ι A := by rw [←map_mul,hτA]
    have hauxS : ι S*ι S*ι u'*ι u'+ι y*ι y=1+ι S*ι S*ι y*ι y := by
      have h := congrArg ι haux
      simp only [map_add,map_mul,map_one] at h
      rw [hSI0]
      exact h
    rw [hB,hQS,htι,hVu]
    linear_combination (ι S*ι S*ι y*ι y-ι y*ι y)*hτAι+(-ι A)*hauxS
  rw [value71_factors (fun i => ((p i:ℕ):DiffRing V)) (fun i => ι (v13 i)) (ι qq) (ι XX)
    (ι Y) (ι E) (ι k) (ι A) (ι c) (ι a) (ι (4*a+3)) (ι (delta a)) (ι d) R0 t Nt (ι m) (ι S)
    (ι I) (ι (f*f)) Vr B hqι
    (show ι XX=ι w*ι qq by rw [←hX]; simp only [map_mul])
    (show ι Y=ι sY*(ι qq*ι qq*ι qq) by rw [←hY]; simp only [map_mul,map_pow]; ring)
    (show ι E=ι XX*ι Y by rw [←hE]; simp only [map_mul])
    (show ι k=ι eta+ι zeta by rw [←hk]; simp only [map_add])
    (show ι A=ι E*(ι k*ι Y)*(ι E*(ι k*ι Y)+ι k)+1 by rw [hA]; simp only [map_add,map_mul,map_one])
    (show ι c=ι k*ι Y+ι eta by rw [←hcc]; simp only [map_add,map_mul])
    (show ι a=ι E+ι Y by rw [←haa]; simp only [map_add])
    (show ι (4*a+3)=4*ι a+3 by simp only [map_add,map_mul,map_ofNat])
    (show ι (delta a)=ι a*ι a+ι (4*a+3) by simp only [delta,map_add,map_mul,map_one,map_ofNat]; ring)
    (show ι d=ι XX+ι a*ι c+ι gamma*ι (4*a+3) by rw [←hdd]; simp only [map_add,map_mul,map_ofNat])
    hR0 ht hNt
    (show ι m=ι E*ι j*ι A by rw [hm]; simp only [map_mul])
    (show ι S=ι m*(ι (delta a)*(ι c*ι c)) by rw [hS]; simp only [map_mul])
    (show ι I=ι m*(ι c*ι c) by rw [hI]; simp only [map_mul])
    (show ι (f*f)=ι f*ι f by simp only [map_mul]) hVr hB]
  rw [hN1,hNt1,hB0,hNs]
  norm_num

#print axioms Q170Complete71.zero_of_halt
end Q170Complete71
