import DiophantineConsistency.BFS943.Q170Syntax74
import DiophantineConsistency.BFS943.Carrier65BFSHalt
import DiophantineConsistency.ArithmeticThirteenSeed

/-! # Completeness of package 170's 74/438 rational carrier

In every model of `𝗜𝚺₁`, an internal halting time gives a positive zero of
`Q170Form74.value74` at the direct-BFS943 ports (`FIXED_CARRIER_PROOF.md` §7.3):

* the outer data of `Carrier65BFSHalt.halt_outer`, with first root
  `τ = E n₀ + k - R`, `τ² = A`, and `k = R + 1 + E h` (`h = 4 Y s₁`, first Pell
  residues at the first index `(R+1)/2`);
* a fresh strong seed whose normalized multiplier is divisible by `τ (a+2) D`
  (`ArithmeticThirteenSeed.strong_index` with `b = τ (a+2) D`), so the strong
  multiplier is `τ m` with `m = j (a+2) D` and `F2 = 1 + A Δ (m c²)² = f²`;
* the fresh auxiliary seed of that strong pair; `Q = Δ W = S²`;
* the carrier `n = τ f y - h > 0` (`τ f y ≥ τ > k > h`), so
  `t = E n + (k - R - 1) = E τ f y`.

All three factors are then one. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace Q170Complete74
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Q170Form74 ArithmeticPellRecurrence
  ArithmeticPellCongruences
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b≤a) : ι (a-b)=ι a-ι b := by
  rw [eq_sub_iff_add_eq,←map_add,tsub_add_cancel_of_le h]

/-- **Halt ⇒ zero** for the 74 carrier, at ports with the direct-BFS943 model values. -/
theorem zero_of_halt (p : Fin 4 → ℕ) (time : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run time)=0)
    (hp : Carrier65BFSHalt.PortValues (V:=V) p) :
    ∃ v : Fin 12 → V, (∀ j, 0<v j) ∧
      value74 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j))=0 := by
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
  -- `k < τ`
  have hkt' : k<tau := by
    apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _)
    rw [hτ]
    have hQQ : 1≤(E*Y)*(E*Y+1) := one_le_mul (pos_iff_one_le.mp (mul_pos hE0 hY0))
      (le_add_of_nonneg_left (Arithmetic.zero_le _))
    calc
      k*k=1*(k*k) := (one_mul _).symm
      _≤((E*Y)*(E*Y+1))*(k*k) := mul_le_mul_of_nonneg_right hQQ (Arithmetic.zero_le _)
      _=(E*Y)*(E*Y+1)*k*k := by ring
      _<1+(E*Y)*(E*Y+1)*k*k := lt_one_add _
  have htau0 : 0<tau := lt_of_le_of_lt (Arithmetic.zero_le _) hkt'
  -- a strong seed with multiplier divisible by `τ (a+2) D`, and its auxiliary seed
  have hcR : c=ycoord R a := hc
  have hd0 : 0<d := by
    rw [←hdd]; exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hXX0 (Arithmetic.zero_le _))
      (Arithmetic.zero_le _)
  have ha2 : 0<a+2 := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
  obtain ⟨ts,j,_,hj,hyt⟩ := ArithmeticThirteenSeed.strong_index a (tau*(a+2)*d) (ycoord R a)
    (mul_pos (mul_pos htau0 ha2) hd0) (by rw [←hcR]; exact hc0)
  obtain ⟨T',u',y,hf,hT',hu',hy,hfn,-,-,hlit,-,haux,-⟩ :=
    ArithmeticThirteenSeed.auxiliary_seed_of a R ts (tau*(a+2)*d*j) hR4
      (mul_pos (mul_pos (mul_pos htau0 ha2) hd0) hj) hyt
  rw [←hcR] at hfn hlit haux
  obtain ⟨f,hfdef⟩ : ∃ x : V, x=xcoord ts a := ⟨_,rfl⟩
  rw [←hfdef] at hf hfn hlit
  obtain ⟨m,hm⟩ : ∃ x : V, x=j*(a+2)*d := ⟨_,rfl⟩
  have hmi : tau*(a+2)*d*j=tau*m := by rw [hm]; ring
  rw [hmi] at hfn haux
  obtain ⟨S,hS⟩ : ∃ x : V, x=delta a*(tau*m)*c*c := ⟨_,rfl⟩
  rw [←hS] at haux
  -- the carrier `n = τ f y - 4 Y s₁`
  have hE1 : 1≤E := pos_iff_one_le.mp hE0
  have hlt : 4*Y*s1<tau*f*y := by
    have h1 : E*(4*Y*s1)<tau := by
      have : R+1+E*(4*Y*s1)<tau := by
        rw [show R+1+E*(4*Y*s1)=R+1+4*Q*s1 by rw [hQ]; ring,←hkR]; exact hkt'
      exact lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) this
    have h2 : 4*Y*s1≤E*(4*Y*s1) := le_mul_of_one_le_left (Arithmetic.zero_le _) hE1
    have h3 : tau≤tau*f*y := by
      rw [mul_assoc]; exact le_mul_of_one_le_right (Arithmetic.zero_le _)
        (one_le_mul (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hy))
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le h1 h3)
  obtain ⟨n,hn⟩ : ∃ x : V, x=tau*f*y-4*Y*s1 := ⟨_,rfl⟩
  have hnpos : 0<n := by rw [hn]; exact tsub_pos_of_lt hlt
  have hn4 : n+4*Y*s1=tau*f*y := by rw [hn]; exact tsub_add_cancel_of_le (le_of_lt hlt)
  -- the twelve coordinates and the three unit factors in the ring of differences
  let v12 : Fin 12 → V := ![J,F,alpha,z,n,j,T',sY,w,eta,zeta,gamma]
  have hv12 : ∀ i, 0<v12 i := by
    intro i
    fin_cases i
    exacts [hJ,hF,ha0,hz,hnpos,hj,hT',hsY,hw,heta,hzeta,hgamma]
  refine ⟨v12,hv12,?_⟩
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
  obtain ⟨t,ht⟩ : ∃ x : DiffRing V, x=ι E*ι n+(ι k-R0-1) := ⟨_,rfl⟩
  have htι : t=ι E*ι tau*ι f*ι y := by
    have h1 := congrArg ι hn4
    simp only [map_add,map_mul,map_ofNat] at h1
    have h2 : ι k=ι R+1+4*ι E*ι Y*ι s1 := by
      rw [hkR,hQ]; simp only [map_add,map_mul,map_one,map_ofNat]; ring
    rw [ht,hRι]
    linear_combination (ι E)*h1+h2
  obtain ⟨Nt,hNt⟩ : ∃ x : DiffRing V, x=(((p 1:ℕ):DiffRing V)+ι w)*(ι qq-ι F-ι alpha)+
      (ι qq-ι F)-ι z*(((p 0:ℕ):DiffRing V)*ι J) := ⟨_,rfl⟩
  have hNt1 : Nt=1 := by
    have h := congrArg ι hW
    simp only [map_add,map_mul,map_natCast,ι_tsub hq1,map_one] at h
    rw [hNt]
    linear_combination h+(ι z)*hqι
  obtain ⟨W,hWdef⟩ : ∃ x : V, x=A*((m*(c*c))*(m*(delta a*(c*c)))) := ⟨_,rfl⟩
  obtain ⟨F2,hF2⟩ : ∃ x : V, x=1+W := ⟨_,rfl⟩
  have hF2f : F2=f*f := by rw [hF2,hfn,hWdef,←hτA]; ring
  obtain ⟨Vr,hVr⟩ : ∃ x : DiffRing V, x=ι F2*(ι c*ι T'-R0)-ι c := ⟨_,rfl⟩
  have hVu : Vr=ι u' := by
    have h := congrArg ι hlit
    simp only [map_add,map_mul] at h
    rw [hVr,hRι,hF2f]
    simp only [map_mul]
    linear_combination h
  obtain ⟨B,hB⟩ : ∃ x : DiffRing V, x=ι (delta a)*ι W*
      (t*t-ι E*ι E*(ι A*ι F2)*(Vr*Vr))-t*t+ι E*ι E*(ι A*ι F2) := ⟨_,rfl⟩
  have hN1 : ι d*ι d-ι (delta a)*(ι c*ι c)=1 := by
    have h := congrArg ι hd
    simp only [map_add,map_mul,map_one,map_ofNat] at h
    simp only [delta,map_add,map_mul,map_one,map_ofNat]
    linear_combination h
  have hB0 : B=0 := by
    have hQSn : delta a*W=S*S := by rw [hWdef,hS,←hτA]; ring
    have hQS : ι (delta a)*ι W=ι S*ι S := by
      have h := congrArg ι hQSn
      simpa only [map_mul] using h
    have hτAι : ι A=ι tau*ι tau := by rw [←hτA,map_mul]
    have hF2ι : ι F2=ι f*ι f := by rw [hF2f,map_mul]
    have hauxS : ι S*ι S*ι u'*ι u'+ι y*ι y=1+ι S*ι S*ι y*ι y := by
      have h := congrArg ι haux
      simp only [map_add,map_mul,map_one] at h
      exact h
    rw [hB,hQS,htι,hVu,hτAι,hF2ι]
    linear_combination (-(ι E*ι E*(ι tau*ι tau)*(ι f*ι f)))*hauxS
  rw [value74_factors (fun i => ((p i:ℕ):DiffRing V)) (fun i => ι (v12 i)) (ι qq) (ι XX)
    (ι Y) (ι E) (ι k) (ι A) (ι c) (ι a) (ι (4*a+3)) (ι (delta a)) (ι d) R0 t Nt (ι m)
    (ι (m*(delta a*(c*c)))) (ι (m*(c*c))) (ι W) (ι F2) Vr (ι A*ι F2) B hqι
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
    (show ι m=ι j*(ι a+2)*ι d by rw [hm]; simp only [map_mul,map_add,map_ofNat])
    (show ι (m*(delta a*(c*c)))=ι m*(ι (delta a)*(ι c*ι c)) by simp only [map_mul])
    (show ι (m*(c*c))=ι m*(ι c*ι c) by simp only [map_mul])
    (show ι W=ι A*(ι (m*(c*c))*ι (m*(delta a*(c*c)))) by rw [hWdef]; simp only [map_mul])
    (show ι F2=1+ι W by rw [hF2]; simp only [map_add,map_one]) hVr rfl hB]
  rw [hN1,hNt1,hB0]
  norm_num

#print axioms Q170Complete74.zero_of_halt
end Q170Complete74
