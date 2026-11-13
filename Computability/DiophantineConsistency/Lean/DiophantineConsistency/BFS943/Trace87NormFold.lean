import DiophantineConsistency.BFS943.Trace87NormRoots
import DiophantineConsistency.BFS943.Trace87Factors
import DiophantineConsistency.BFS943.Trace87Residue
import DiophantineConsistency.BFS943.PellRecovery
import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! # First Pell index, auxiliary index and odd ordinate at an arbitrary carrier

`Trace75Pell.first_and_doubled`, `Trace75Joined` and `Trace75Fold` restated
for a positive zero of `normValue (regs …) Z` at an arbitrary carrier value
`Z`; the proofs are those of the 75 modules, routed through
`Trace87NormRoots`.

Free-inverse copy of `TraceNormFold` (from the chart-q1 copy `Trace80NormFold`) for the 87/214
registers `TenPositiveTrace87.regs` (`X = q w`, register `Y = q s`, strip
`c = k s + η`); names `Trace75*`/`TraceNorm*` below refer to the q3 originals.
Beyond `X = q w` (positivity lines only), only the strip lines differ
from `Trace80NormFold`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace87NormFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open ArithmeticPellRecurrence ArithmeticPellFirstNorm ArithmeticPellClassification
open ArithmeticPellResidueClasses ArithmeticPellHalfIndex TenPositivePellRecovery
open Trace87Factors Trace87Residue Trace87NormRoots
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_and_doubled (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let K := k v
    let P := firstParam p v
    let C := c p v
    let aa := D*U0*U0*E0
    ∃ tau f n I : V, 0<tau ∧ 0<f ∧ 0<n ∧ n≤K ∧
      E0=tau*tau ∧ 1+aa=f*f ∧
      xcoord n (2*(P-1)+1)=tau ∧ 2*ycoord n (2*(P-1)+1)=K ∧
      I=2*U0*tau*f ∧ 0<I ∧ (1+2*aa)*(1+2*aa)=1+D*I*I ∧
      D*(4*aa*(1+aa))=(D*I)*(D*I) ∧ C*C∣I := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let K : V := k v
  let P : V := firstParam p v
  let C : V := c p v
  let aa : V := D*U0*U0*E0
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hP : 0<P := mul_pos hx (mul_pos hy hy)
  have hK : 0<K := add_pos (hv 8) (hv 9)
  have hU : 0<U0 := (factors_positive p v hb hv).2.1
  obtain ⟨tau,f,htau,hf,ht,hf2⟩ := graph_roots p v Z hb hv hz
  have hnorm : tau*tau=1+P*(P+1)*K*K := by
    calc
      tau*tau=E0 := ht.symm
      _=1+P*(P+1)*K*K := by dsimp [E0,E,P,firstParam,K]; ring
  obtain ⟨n,hnk,hnx,hny⟩ := positive_parameter_solution P tau K hP hnorm
  have hn : 0<n := pos_iff_ne_zero.mpr (by
    intro hn0
    apply (ne_of_gt hK)
    simpa [hn0] using hny.symm)
  change E0=tau*tau at ht
  change 1+aa=f*f at hf2
  let I : V := 2*U0*tau*f
  have hI : 0<I := mul_pos (mul_pos (mul_pos (by simp) hU) htau) hf
  have hG : E0*(1+aa)=(tau*tau)*(f*f) := by rw [ht,hf2]
  have hdbl : (1+2*aa)*(1+2*aa)=1+D*I*I := by
    calc
      (1+2*aa)*(1+2*aa)=1+4*aa*(1+aa) := by ring
      _=1+D*(2*U0)*(2*U0)*(E0*(1+aa)) := by dsimp [aa]; ring
      _=1+D*(2*U0)*(2*U0)*((tau*tau)*(f*f)) := by rw [hG]
      _=1+D*I*I := by dsimp [I]; ring
  have hQ : D*(4*aa*(1+aa))=(D*I)*(D*I) := by
    calc
      D*(4*aa*(1+aa))=(D*(2*U0))*(D*(2*U0))*(E0*(1+aa)) := by dsimp [aa]; ring
      _=(D*(2*U0))*(D*(2*U0))*((tau*tau)*(f*f)) := by rw [hG]
      _=(D*I)*(D*I) := by dsimp [I]; ring
  have hC : C*C∣I := ⟨2*v 3*tau*f,by dsimp [I,U0,U,C]; ring⟩
  exact ⟨tau,f,n,I,htau,hf,hn,hnk,ht,hf2,hnx,hny,rfl,hI,hdbl,hQ,hC⟩

/-- Strong index and odd auxiliary index, including the signed modular
transfer, at an arbitrary carrier. -/
theorem strong_and_auxiliary_indices_with_graph_residue (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (Z : DiffRing V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let a := D*U0*U0*E0
    let F := 1+2*a
    ∃ tau f V0 y I j h : V,
      0<tau ∧ 0<f ∧ 0<V0 ∧ 0<y ∧ 0<I ∧ 0<j ∧
      E0=tau*tau ∧ 1+a=f*f ∧ I=2*U0*tau*f ∧ c p v*c p v∣I ∧
      xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      xcoord (2*h+1) (D*I-2)=(D*I)*V0 ∧
      ycoord (2*h+1) (D*I-2)=y ∧
      SignMod F V0 (c p v) ∧
      SignMod F V0 (ycoord (2*h+1) (A0-1)) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  obtain ⟨hD,hU,hE,hM⟩ := factors_positive p v hb hv
  have hA : 0<A0 := pos_of_mul_pos_left (by change 0<A0*(A0+2) at hD; exact hD) (by simp)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hdelta : ArithmeticPellRecurrence.delta (A0-1)=D := by
    unfold ArithmeticPellRecurrence.delta
    have h3 : A0-1+3=(A0-1+1)+2 := by ring
    rw [h3,hA1]
    rfl
  obtain ⟨tau,f,V0,Z0,y,htau,hf,hVp,hy,ht,hf2,hV,hZ,hZeq,haux⟩ := graph_adjacent p v Z hb hv hz
  change E0=tau*tau at ht
  change 1+a=f*f at hf2
  change Q*(V0*V0)=1+(Q-1)*(y*y) at haux
  let I : V := 2*U0*tau*f
  let J : V := D*I
  have hI : 0<I := mul_pos (mul_pos (mul_pos (by simp) hU) htau) hf
  have hD1 : 1≤D := pos_iff_one_le.mp hD
  have hI2 : 2≤I := by
    have hpos : 1≤U0*tau*f := pos_iff_one_le.mp (mul_pos (mul_pos hU htau) hf)
    simpa only [I,mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hpos (by simp : (0:V)≤2)
  have hJ2 : 2≤J := le_trans hI2 (le_mul_of_one_le_left (by simp) hD1)
  have hJ : 0<J := lt_of_lt_of_le (by simp : (0:V)<2) hJ2
  have hF : 0<F := by dsimp [F]; simp
  have hG : E0*(1+a)=(tau*tau)*(f*f) := by rw [ht,hf2]
  have hstrong : F*F=1+D*I*I := by
    calc
      F*F=1+4*a*(1+a) := by dsimp [F]; ring
      _=1+D*(2*U0)*(2*U0)*(E0*(1+a)) := by dsimp [a]; ring
      _=1+D*(2*U0)*(2*U0)*((tau*tau)*(f*f)) := by rw [hG]
      _=1+D*I*I := by dsimp [I]; ring
  have hQ : Q=J*J := by
    calc
      Q=(D*(2*U0))*(D*(2*U0))*(E0*(1+a)) := by dsimp [Q,a]; ring
      _=(D*(2*U0))*(D*(2*U0))*((tau*tau)*(f*f)) := by rw [hG]
      _=J*J := by dsimp [J,I]; ring
  have hc : c p v*c p v∣I := ⟨2*v 3*tau*f,by dsimp [I,U0,U]; ring⟩
  have hstrong' : F*F=1+ArithmeticPellRecurrence.delta (A0-1)*I*I := by rwa [hdelta]
  obtain ⟨j,_,hjx,hjy⟩ := ArithmeticPellClassification.solution_index (A0-1) F I hstrong'
  have hj : 0<j := pos_iff_ne_zero.mpr (by intro hj0; apply (ne_of_gt hI); simpa [hj0] using hjy.symm)
  have hJsub : J-2+2=J := tsub_add_cancel_of_le hJ2
  have hdJ : ArithmeticPellRecurrence.delta (J-2)+1=J*J := by
    calc
      ArithmeticPellRecurrence.delta (J-2)+1=(J-2+2)*(J-2+2) := by unfold ArithmeticPellRecurrence.delta; ring
      _=J*J := by rw [hJsub]
  have hQsub : Q-1=ArithmeticPellRecurrence.delta (J-2) := by rw [hQ,←hdJ]; simp
  have hn : (J*V0)*(J*V0)=1+ArithmeticPellRecurrence.delta (J-2)*y*y := by
    calc
      (J*V0)*(J*V0)=Q*(V0*V0) := by rw [hQ]; ring
      _=1+(Q-1)*(y*y) := haux
      _=1+ArithmeticPellRecurrence.delta (J-2)*y*y := by rw [hQsub]; ring
  obtain ⟨s,_,hsx,hsy⟩ := ArithmeticPellClassification.solution_index (J-2) (J*V0) y hn
  obtain ⟨h,hs⟩ := odd_index_witness (J-2) s (by rw [hJsub,hsx]; exact ⟨V0,rfl⟩)
  have hV0 : V0=oddQuotient h (J-2) := by
    apply mul_left_cancel₀ (ne_of_gt hJ)
    calc
      J*V0=xcoord (2*h+1) (J-2) := by rw [←hs,hsx]
      _=J*oddQuotient h (J-2) := by rw [odd_exact,hJsub]
  have hstrongnorm : J*J+ArithmeticPellRecurrence.delta (A0-1)=
      ArithmeticPellRecurrence.delta (A0-1)*F*F := by
    rw [hdelta]
    calc
      J*J+D=D*(1+D*I*I) := by dsimp [J]; ring
      _=D*(F*F) := by rw [hstrong]
      _=D*F*F := by ring
  have htransfer : SignMod F V0 (ycoord (2*h+1) (A0-1)) := by
    rw [hV0]
    exact quotient_mod_norm (A0-1) J F h hJ2 hF hstrongnorm
  refine ⟨tau,f,V0,y,I,j,h,htau,hf,hVp,hy,hI,hj,ht,hf2,rfl,hc,hjx,hjy,?_,?_,?_,htransfer⟩
  · simpa only [←hs] using hsx
  · simpa only [←hs] using hsy
  · exact graph_signed_residue p v V0 hV

theorem signed_coordinate (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let F := 1+2*(D*U0*U0*E0)
    ∃ I j h : V, 0<I ∧ 0<j ∧ c p v≤I ∧
      c p v*c p v∣I ∧ xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      SignMod F (c p v) (ycoord (2*h+1) (A0-1)) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let F : V := 1+2*(D*U0*U0*E0)
  obtain ⟨tau,f,V0,y,I,j,h,htau,hf,hV,hy,hI,hj,ht,hf2,hIeq,hdiv,hjx,hjy,_hauxx,_hauxy,hgc,hgu⟩ :=
    strong_and_auxiliary_indices_with_graph_residue p v Z hb hv hz
  have hF : 0<F := by dsimp [F]; simp
  have hcpos : 0<c p v := by
    by_contra hn
    have hc0 : c p v=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hc0] at hdiv
    simp only [zero_mul,zero_dvd_iff] at hdiv
    exact (ne_of_gt hI) hdiv
  have hcle : c p v≤c p v*c p v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hcpos) (by simp : (0:V)≤c p v)
  have hbound : c p v≤I := le_trans hcle (Arithmetic.le_of_dvd hI hdiv)
  exact ⟨I,j,h,hI,hj,hbound,hdiv,hjx,hjy,sign_trans hF (sign_symm hgc) hgu⟩

theorem graph_odd_ordinate (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    ∃ r j I : V, 0<r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<I ∧
      c p v=ycoord r (A p v-1) ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let C : V := c p v
  let F : V := 1+2*(D*U0*U0*E0)
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hA2 : 2≤A0 := by
    have hxy : 1≤X p v*Y p v := pos_iff_one_le.mp (mul_pos hX hY)
    have hy1 : 1≤Y p v := pos_iff_one_le.mp hY
    change 2≤X p v*Y p v+Y p v
    simpa only [show (2:V)=1+1 by ring] using _root_.add_le_add hxy hy1
  have hD4 : 4≤D := by
    calc
      4=(2:V)*2 := by ring
      _≤A0*2 := mul_le_mul_of_nonneg_right hA2 (by simp)
      _≤A0*(A0+2) := mul_le_mul_of_nonneg_left (by simp) (by simp)
      _=D := rfl
  have hk2 : 2≤k v := by
    simpa only [k,show (2:V)=1+1 by ring] using
      _root_.add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
  have hkY : k v≤k v*v 6 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp : (0:V)≤k v)
  have hC2 : 2<C := lt_of_le_of_lt (le_trans hk2 hkY) (by
    change k v*v 6<k v*v 6+v 8
    exact lt_add_of_pos_right _ (hv 8))
  have hC : 0<C := lt_trans (by simp : (0:V)<2) hC2
  obtain ⟨I,j,h,hI,hj,hCI,hdiv,hjx,hjy,hcong⟩ := signed_coordinate p v Z hb hv hz
  have hCsq : C*C≤I := Arithmetic.le_of_dvd hI hdiv
  have hCstrict : C<C*C := by
    have h1 : 1<C := lt_trans (by simp : (1:V)<2) hC2
    simpa only [mul_one] using mul_lt_mul_of_pos_left h1 hC
  have hCIstrict : C<I := lt_of_lt_of_le hCstrict hCsq
  have hApos : 0<A0 := lt_of_lt_of_le (by simp : (0:V)<2) hA2
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hdelta : ArithmeticPellRecurrence.delta (A0-1)=D := by
    unfold ArithmeticPellRecurrence.delta
    have h3 : A0-1+3=(A0-1+1)+2 := by ring
    rw [h3,hA1]
    rfl
  have hnorm : F*F=1+D*I*I := by
    have h := norm j (A0-1)
    rw [hdelta,hjx,hjy] at h
    exact h
  have hFsize : 2*I<F := by
    by_contra hn
    have hle : F≤2*I := le_of_not_gt hn
    have hsq : F*F≤(2*I)*(2*I) := mul_self_le_mul_self (by simp) hle
    have hmul : 4*I*I≤D*I*I := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD4 (by simp)) (by simp)
    have hlt : (2*I)*(2*I)<F*F := by
      calc
        (2*I)*(2*I)=4*I*I := by ring
        _≤D*I*I := hmul
        _<1+D*I*I := by simp
        _=F*F := hnorm.symm
    exact (not_le_of_gt hlt) hsq
  have hsodd : (2*h+1)%2=1 := by rw [mod_add (by simp : (0:V)<2),mod_mul_self_right]; simp
  obtain ⟨r,hr,hrj,hrodd,heq⟩ := recover_odd_ordinate j (2*h+1) (A0-1) C hj hsodd hC
    (by rwa [hjy]) (by rwa [hjy,hjx]) (by rwa [hjx])
  exact ⟨r,j,I,hr,hrj,hrodd,hj,hI,heq,hjx,hjy,hdiv⟩

#print axioms Trace87NormFold.graph_odd_ordinate
end Trace87NormFold
