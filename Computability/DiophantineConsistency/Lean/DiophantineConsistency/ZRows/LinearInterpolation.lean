import DiophantineConsistency.ZRows.PellValuationIndex
import DiophantineConsistency.ZRows.PellEvenChebyshev
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! # Supported-modulus interpolation by linear stepping

In every model `V` of `𝗜𝚺₁`, fix a main base `A = a + 2` (`Δ = delta a = A² − 1`), an index
`R ≡ 3 (mod 4)` with `c = ψ_A(R)`, and a strong pair `I = ψ_A(n0)`, `f = χ_A(n0)` with `4 ∣ I`.
The auxiliary base is `ρ = Δ·I` (Lean base parameter `ρ − 2`), `V_ν = χ_ρ(ν)/ρ` for odd `ν`
(`ArithmeticPellHalfIndex.oddQuotient`) and `y = ψ_ρ(ν)`, so that `ρ²V_ν² − (ρ²−1)y² = 1`.

The **requirement** (P138 risk audit §3.1) is that for every modulus `M ∣ I²` and every target
`t0`, some `T` with `T ≡ t0 (mod M)` makes `V = f²(c − R + 4I·T) − c` an auxiliary abscissa
quotient. This module proves it (`linear_interpolation`, and with the strong index chosen,
`supported_interpolation`) by the **linear stepping** of audit §3.3:

* the index split `n0 = g·w`, `g ∣ I`, `w` coprime to `I` (`ZRowsPellValuation.strong_index`,
  which is where the valuation inequality enters), and `w' = f·w`;
* the step `ν(h) = R + d·h`, `d = 4·I·w'`: `4n0f ∣ d`, so `ψ_A(ν) ≡ c (mod f²)`
  (`square_period`), and `ν ≡ R (mod 4I)`; with `quotient_square_pair` and the `4ρ²` form of the
  odd-quotient law (`quotient_four_sq_pair`) this makes
  `T(h) = (V_ν + c − f²(c−R)) / (4 I f²)` integral at every `h` (`point`);
* the doubled-quotient form of `χ_ρ, ψ_ρ` at `d/2`, and the even-ordinate law
  `ψ_ρ(d/2) = 2ρ·P`, `P ≡ ±d/4 (mod 4ρ²)` (`ZRowsPellEvenChebyshev.even_ordinate`), give
  `T(h) ≡ T(0) + h·u (mod I²)` with `u = (ρ²−1)·ψ_ρ(R)·χ_ρ(d/2)·P/I` (`linear_core`, `T_core`);
* every factor of `u` is coprime to `I` (`Cop`), so `h ≡ u⁻¹(t0 − T(0))` (Bezout, then a natural
  representative) hits `t0` modulo `I²`, hence modulo `M`.

No isometry, pigeonhole or exact lifting-the-exponent statement is needed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ZRowsLinearInterpolation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellSquaredSeed
open ArithmeticPellResidueClasses ArithmeticPellHalfIndex ArithmeticPellAuxiliarySeed
open ZRowsCoprimeSquares ZRowsIntersective19 ZRowsPellValuation ZRowsPellEvenChebyshev

/-! ### Ring algebra (no model needed) -/

section Ring
variable {𝔸 : Type*} [CommRing 𝔸] [NoZeroDivisors 𝔸]

/-- Coprimality to `I` as a ring Bezout certificate. -/
def Cop (x I : 𝔸) : Prop := ∃ α β : 𝔸, x*α+I*β=1

theorem cop_mul {x y I : 𝔸} (hx : Cop x I) (hy : Cop y I) : Cop (x*y) I := by
  obtain ⟨α,β,h⟩ := hx
  obtain ⟨α',β',h'⟩ := hy
  exact ⟨α*α',x*α*β'+β*y*α'+I*β*β',by linear_combination (y*α'+I*β')*h+h'⟩

/-- The linear law for the abscissa quotient, after cancelling `ρ`. -/
theorem linear_core (ρ Δ I V0 Vh χR ψR χe ψe r s P P' δ h : 𝔸)
    (hρ0 : ρ≠0) (hρ : ρ=Δ*I) (hχR : χR=ρ*V0)
    (hadd : ρ*Vh=χR*(1+ψe*ψe*r)+δ*ψR*(2*h*χe*ψe+ψe*ψe*s))
    (hψe : ψe=2*ρ*P) (hP : P=I*P') :
    Vh-V0=4*I*(h*(δ*ψR*χe*P')+I*I*(Δ*Δ*I*P'*P'*V0*r+Δ*P'*P'*δ*ψR*s)) := by
  subst hχR hψe hP hρ
  have key : Δ*I*(Vh-V0-4*I*(h*(δ*ψR*χe*P')+I*I*(Δ*Δ*I*P'*P'*V0*r+Δ*P'*P'*δ*ψR*s)))=0 := by
    linear_combination hadd
  rcases mul_eq_zero.mp key with h0|h0
  · exact absurd h0 hρ0
  · exact sub_eq_zero.mp h0

/-- The linear law for `T`, from the two defining equations. -/
theorem T_core (I f2 Δ T0 Th V0 Vh c R u h K : 𝔸) (hI : (4:𝔸)*I≠0)
    (hf : f2=1+Δ*I*I) (hT0 : 4*I*f2*T0=V0+c-f2*(c-R)) (hTh : 4*I*f2*Th=Vh+c-f2*(c-R))
    (hV : Vh-V0=4*I*(h*u+I*I*K)) : Th-T0-h*u=I*I*(K-Δ*(Th-T0)) := by
  have key : 4*I*(f2*(Th-T0)-(h*u+I*I*K))=0 := by linear_combination hTh-hT0+hV
  rcases mul_eq_zero.mp key with h0|h0
  · exact absurd h0 hI
  · have e := sub_eq_zero.mp h0
    linear_combination e-(Th-T0)*hf

/-- Bezout inversion modulo `I²`. -/
theorem solve {u I : 𝔸} (hu : Cop u I) (z : 𝔸) : ∃ h' : 𝔸, I*I∣u*h'-z := by
  obtain ⟨α,β,h⟩ := hu
  refine ⟨(2*α-u*α*α)*z,-(z*β*β),?_⟩
  have e : 1-u*α=I*β := by linear_combination (-1:𝔸)*h
  linear_combination (-(z*(1-u*α+I*β)))*e

end Ring

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord oddQuotient

/-! ### The odd-quotient law modulo divisors of `4ρ²` (C6) -/

/-- `ArithmeticPellAuxiliarySeed.quotient_divisor_pair` for every divisor `c` of `4ρ²` (its proof
only uses `c ∣ 4ρ²`). -/
theorem quotient_four_sq_pair (I c t : V) (hI : 2≤I) (hc : 0<c) (hd : c∣4*I*I) :
    oddQuotient (2*t) (I-2)%c=(4*t+1)%c ∧
    (oddQuotient (2*t+1) (I-2)+(4*t+3))%c=0 := by
  let b:=I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hcoef : (4*(b+2)*(b+2)+4)%c=(4:V)%c := by
    rw [hb]
    exact mod_add_remove_left_of_dvd hd hc
  have hfirst : (oddQuotient 1 b+3)%c=0 := by
    rw [ArithmeticPellHalfIndex.odd_one,hb]
    exact mod_eq_zero_iff_dvd.mpr hd
  have linear_rec (h : V) :
      (2*(h+2)+1)+(2*h+1)+2*(2*(h+1)+1)=4*(2*(h+1)+1) := by ring
  have pair (t : V) : oddQuotient (2*t) b%c=(2*(2*t)+1)%c ∧
      (oddQuotient (2*t+1) b+(2*(2*t+1)+1))%c=0 := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      constructor
      · simp only [mul_zero,zero_add,odd_zero]
      · simpa only [mul_zero,zero_add,show (2:V)*1+1=3 by ring] using hfirst
    case succ t ih =>
      have h2 := transport_equal c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*t) b) (linear_rec (2*t)) ih.1 ih.2
      have h3 := transport_opposite c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*t+1) b) (linear_rec (2*t+1)) ih.2
        (by simpa only [add_assoc,one_add_one_eq_two] using h2)
      constructor
      · simpa only [show 2*(t+1)=2*t+2 by ring] using h2
      · simpa only [show 2*(t+1)+1=(2*t+1)+2 by ring] using h3
  simpa only [show 2*(2*t)+1=4*t+1 by ring,
    show 2*(2*t+1)+1=4*t+3 by ring] using pair t

/-! ### The square period (C4) -/

/-- **Square period**: index shifts by multiples of `4·n0·f` fix `ψ_A` modulo `f²`. -/
theorem square_period (a R n0 k : V) :
    ∃ q : DiffRing V, ι (ycoord (R+2*(xcoord n0 a*k)*(2*n0)) a)-ι (ycoord R a)=
      ι (xcoord n0 a)*ι (xcoord n0 a)*q := by
  obtain ⟨r,s,hx,hy⟩ := doubled_quotients (xcoord n0 a*k) (2*n0) a
  have h2 := double_y n0 a
  have hadd := (addition R (2*(xcoord n0 a*k)*(2*n0)) a).2
  have Hx := congrArg (ι (V := V)) hx
  have Hy := congrArg (ι (V := V)) hy
  have H2 := congrArg (ι (V := V)) h2
  have Hadd := congrArg (ι (V := V)) hadd
  simp only [map_add,map_mul,map_ofNat,map_one] at Hx Hy H2 Hadd
  rw [H2] at Hx Hy
  rw [Hx,Hy] at Hadd
  refine ⟨ι (xcoord R a)*(4*ι k*ι (xcoord (2*n0) a)*ι (ycoord n0 a)+
      4*ι (ycoord n0 a)*ι (ycoord n0 a)*ι s)+
      4*ι (ycoord R a)*ι (ycoord n0 a)*ι (ycoord n0 a)*ι r,?_⟩
  linear_combination Hadd

/-! ### Integrality at every step -/

theorem four_I_dvd (ρ Δ I : V) (hρ : ρ=Δ*I) : 4*I∣4*ρ*ρ :=
  ⟨Δ*Δ*I,by rw [hρ]; ring⟩

/-- **Integrality** of `T(h)` for the step `ν(h) = R + 4·I·f·w·h`. -/
theorem point (a n0 R g J w I f ρ h : V) (hn0 : n0=g*w) (hI : I=ycoord n0 a)
    (hf : f=xcoord n0 a) (hIJ : I=g*J) (hI4 : 4∣I) (hIpos : 0<I) (hR : R%4=3)
    (hρ : ρ=delta a*I) :
    ∃ T : DiffRing V, 4*ι I*(ι f*ι f)*T=
      ι (oddQuotient (2*(R/4+I*(f*w)*h)+1) (ρ-2))+ι (ycoord R a)-
        ι f*ι f*(ι (ycoord R a)-ι R) := by
  obtain ⟨τ,hτ⟩ : ∃ τ : V, τ=R/4+I*(f*w)*h := ⟨_,rfl⟩
  rw [← hτ]
  have hRq : R=4*(R/4)+3 := by simpa only [hR] using (div_add_mod R 4).symm
  have hf2 : f*f=1+delta a*I*I := by rw [hf,hI]; exact norm n0 a
  have hI4' : 4≤I := LO.FirstOrder.Arithmetic.le_of_dvd hIpos hI4
  have hD1 : 1≤delta a := pos_iff_one_le.mp (by unfold delta; exact mul_pos (by simp) (by simp))
  have hρI : I≤ρ := by rw [hρ]; exact le_mul_of_one_le_left (Arithmetic.zero_le I) hD1
  have hρ2 : 2≤ρ := le_trans (le_trans (by norm_num : (2:V)≤4) hI4') hρI
  have hn : ρ*ρ+delta a=delta a*f*f := by
    calc ρ*ρ+delta a=delta a*(1+delta a*I*I) := by rw [hρ]; ring
      _=delta a*f*f := by rw [← hf2]; ring
  have hfpos : 0<f := by
    rw [hf]
    exact lt_of_lt_of_le _root_.zero_lt_one (one_le_x n0 a)
  have h4I : 0<4*I := mul_pos (by norm_num) hIpos
  -- the two residues of the abscissa quotient
  have hsq := (quotient_square_pair a ρ f τ hρ2 hfpos hn).2
  have hc6 := (quotient_four_sq_pair ρ (4*I) τ hρ2 h4I (four_I_dvd ρ (delta a) I hρ)).2
  -- the step index
  have hidx : 2*(2*τ+1)+1=R+2*(f*(J*h))*(2*n0) := by
    calc 2*(2*τ+1)+1=4*(R/4)+3+4*I*f*w*h := by rw [hτ]; ring
      _=R+2*(f*(J*h))*(2*n0) := by rw [← hRq,hIJ,hn0]; ring
  have hidx4 : 4*τ+3=R+4*I*(f*w*h) := by
    calc 4*τ+3=4*(R/4)+3+4*I*(f*w*h) := by rw [hτ]; ring
      _=R+4*I*(f*w*h) := by rw [← hRq]
  obtain ⟨q,hq⟩ := square_period a R n0 (J*h)
  rw [← hf] at hq
  obtain ⟨k1,hk1⟩ := mod_eq_zero_iff_dvd.mp hsq
  rw [hidx] at hk1
  obtain ⟨k2,hk2⟩ := mod_eq_zero_iff_dvd.mp hc6
  rw [hidx4] at hk2
  obtain ⟨I',hI'⟩ := hI4
  have K1 := congrArg (ι (V := V)) hk1
  have K2 := congrArg (ι (V := V)) hk2
  have F2 := congrArg (ι (V := V)) hf2
  have EI := congrArg (ι (V := V)) hI'
  simp only [map_add,map_mul,map_ofNat,map_one] at K1 K2 F2 EI
  have hX1 : ι f*ι f∣ι (oddQuotient (2*τ+1) (ρ-2))+ι (ycoord R a)-
      ι f*ι f*(ι (ycoord R a)-ι R) :=
    ⟨ι k1-q-(ι (ycoord R a)-ι R),by linear_combination K1-hq⟩
  have hX2 : 4*ι I∣ι (oddQuotient (2*τ+1) (ρ-2))+ι (ycoord R a)-
      ι f*ι f*(ι (ycoord R a)-ι R) :=
    ⟨ι k2-ι f*ι w*ι h-ι (delta a)*ι I'*(ι (ycoord R a)-ι R),
      by linear_combination K2-(ι (ycoord R a)-ι R)*F2-(ι (ycoord R a)-ι R)*ι (delta a)*ι I*EI⟩
  have hcop : 4*ι I*(-(ι (delta a)*ι I'))+ι f*ι f*1=1 := by
    linear_combination F2+ι (delta a)*ι I*EI
  obtain ⟨T,hT⟩ := dvd_mul_of_bez_ring hX2 hX1 hcop
  exact ⟨T,hT.symm⟩

/-! ### Linear stepping -/

/-- **Supported-modulus interpolation** for a strong index with a coprime split
`n0 = g·w`, `g ∣ I`, `w` coprime to `I` (`I = ψ_A(n0)`, `4 ∣ I`): for every `M ∣ I²` and every
target `t0` there are `T ≡ t0 (mod M)` and `y` with `ρ²V² − (ρ²−1)y² = 1`, where `ρ = Δ·I` and
`V = f²(c − R + 4I·T) − c`. -/
theorem linear_interpolation (a R n0 g w M : V) (t0 : DiffRing V)
    (hn : 0<n0) (hR : R%4=3) (hn0 : n0=g*w) (hg : g∣ycoord n0 a)
    (hw : Bez w (ycoord n0 a) 1) (h4 : 4∣ycoord n0 a) (hM : 0<M)
    (hMI : M∣ycoord n0 a*ycoord n0 a) :
    ∃ T y : DiffRing V, (ι M : DiffRing V)∣T-t0 ∧
      (ι (delta a)*ι (ycoord n0 a))^2*
        (ι (xcoord n0 a)^2*(ι (ycoord R a)-ι R+4*ι (ycoord n0 a)*T)-ι (ycoord R a))^2-
        ((ι (delta a)*ι (ycoord n0 a))^2-1)*y^2=1 := by
  obtain ⟨I,hI⟩ : ∃ I : V, I=ycoord n0 a := ⟨_,rfl⟩
  obtain ⟨f,hf⟩ : ∃ f : V, f=xcoord n0 a := ⟨_,rfl⟩
  obtain ⟨ρ,hρ⟩ : ∃ ρ : V, ρ=delta a*I := ⟨_,rfl⟩
  rw [← hI] at hg hw h4 hMI
  have Dρ : (ι ρ : DiffRing V)=ι (delta a)*ι I := by rw [hρ,map_mul]
  rw [← hI,← hf,← Dρ]
  obtain ⟨J,hJ⟩ := hg
  have hIpos : 0<I := by rw [hI]; exact lt_of_lt_of_le hn (time_le_y n0 a)
  have hI4' : 4≤I := LO.FirstOrder.Arithmetic.le_of_dvd hIpos h4
  have hD1 : 1≤delta a := pos_iff_one_le.mp (by unfold delta; exact mul_pos (by simp) (by simp))
  have hρ2 : 2≤ρ := le_trans (le_trans (by norm_num : (2:V)≤4) hI4')
    (by rw [hρ]; exact le_mul_of_one_le_left (Arithmetic.zero_le I) hD1)
  obtain ⟨b',hb'⟩ : ∃ b' : V, b'=ρ-2 := ⟨_,rfl⟩
  have hb'2 : b'+2=ρ := by rw [hb']; exact tsub_add_cancel_of_le hρ2
  have hδ : delta b'+1=ρ*ρ := by rw [← hb'2]; unfold delta; ring
  have hf2 : f*f=1+delta a*I*I := by rw [hf,hI]; exact norm n0 a
  have hRq : R=4*(R/4)+3 := by simpa only [hR] using (div_add_mod R 4).symm
  have hRi : 2*(2*(R/4)+1)+1=R := by
    calc 2*(2*(R/4)+1)+1=4*(R/4)+3 := by ring
      _=R := hRq.symm
  -- ring images of the fixed data
  have F2 : ι f*ι f=1+ι (delta a)*ι I*ι I := by
    have e := congrArg (ι (V := V)) hf2
    simpa only [map_add,map_mul,map_one] using e
  have D1ρ : ι (delta b')+1=ι ρ*ι ρ := by
    have e := congrArg (ι (V := V)) hδ
    simpa only [map_add,map_mul,map_one] using e
  have D1 : ι (delta b')+1=ι (delta a)*ι I*(ι (delta a)*ι I) := by rw [D1ρ,Dρ]
  have hρ0 : (ι ρ : DiffRing V)≠0 := by
    have hlt : (0:DiffRing V)<ι ρ := by
      rw [← map_zero (ι (V := V))]
      exact ι_lt_ι.mpr (lt_of_lt_of_le (by norm_num) hρ2)
    exact ne_of_gt hlt
  have hI0 : (4:DiffRing V)*ι I≠0 := by
    have hlt : (0:DiffRing V)<ι I := by
      rw [← map_zero (ι (V := V))]
      exact ι_lt_ι.mpr hIpos
    exact ne_of_gt (mul_pos (by norm_num) hlt)
  -- the even ordinate at the half step `e = 2·I·f·w`
  obtain ⟨P,hPe,hPs⟩ := even_ordinate b' (I*(f*w))
  rw [hb'2] at hPe hPs
  obtain ⟨ε,k,hε,hPk⟩ : ∃ ε k : DiffRing V, ε*ε=1 ∧ ι P=ε*ι (I*(f*w))+ι (4*ρ*ρ)*k := by
    rcases hPs with h|h
    · obtain ⟨k,hk⟩ := mod_eq_zero_iff_dvd.mp h
      have hk' := congrArg (ι (V := V)) hk
      rw [map_add,map_mul (ι (V := V)) (4*ρ*ρ) k] at hk'
      exact ⟨-1,ι k,by ring,by linear_combination hk'⟩
    · obtain ⟨q,hq⟩ := ringSub_of_mod_eq h
      exact ⟨1,q,by ring,by linear_combination hq⟩
  have R1 : ι (4*ρ*ρ)=4*ι (delta a)*ι (delta a)*ι I*ι I := by
    simp only [map_mul,map_ofNat,Dρ]
    ring
  have R2 : ι (I*(f*w))=ι I*(ι f*ι w) := by simp only [map_mul]
  obtain ⟨P',hP'⟩ : ∃ P' : DiffRing V, P'=ε*(ι f*ι w)+4*ι (delta a)*ι (delta a)*ι I*k :=
    ⟨_,rfl⟩
  have hPP : ι P=ι I*P' := by rw [hP']; linear_combination hPk+ε*R2+k*R1
  have HPe : ι (ycoord (2*(I*(f*w))) b')=2*ι ρ*ι P := by
    rw [hPe]; simp only [map_mul,map_ofNat]
  -- `χ_ρ(R) = ρ·V(0)`
  have hoe0 := odd_exact (2*(R/4)+1) b'
  rw [hRi,hb'2] at hoe0
  have HχR : ι (xcoord R b')=ι ρ*ι (oddQuotient (2*(R/4)+1) b') := by rw [hoe0,map_mul]
  -- every factor of `u` is coprime to `I`
  have NR := congrArg (ι (V := V)) (norm R b')
  simp only [map_add,map_mul,map_one] at NR
  rw [HχR,Dρ] at NR
  have cδ : Cop (ι (delta b')) (ι I) :=
    ⟨-1,ι (delta a)*ι (delta a)*ι I,by linear_combination (-1:DiffRing V)*D1⟩
  have cR : Cop (ι (ycoord R b')) (ι I) :=
    ⟨-(ι (delta b')*ι (ycoord R b')),
      ι (delta a)*ι (delta a)*ι I*ι (oddQuotient (2*(R/4)+1) b')*
        ι (oddQuotient (2*(R/4)+1) b'),by linear_combination NR⟩
  have Ne := congrArg (ι (V := V)) (norm (2*(I*(f*w))) b')
  simp only [map_add,map_mul,map_one] at Ne
  rw [HPe,hPP,Dρ] at Ne
  have ce : Cop (ι (xcoord (2*(I*(f*w))) b')) (ι I) :=
    ⟨ι (xcoord (2*(I*(f*w))) b'),
      -(ι (delta b')*4*ι (delta a)*ι (delta a)*ι I*ι I*ι I*P'*P'),by linear_combination Ne⟩
  have cf : Cop (ι f) (ι I) := ⟨ι f,-(ι (delta a)*ι I),by linear_combination F2⟩
  have cw : Cop (ι w) (ι I) := bez_one_iff_ring.mp hw
  obtain ⟨α,β,hαβ⟩ := cop_mul cf cw
  have cP : Cop P' (ι I) :=
    ⟨ε*α,β-4*ι (delta a)*ι (delta a)*k*ε*α,by
      rw [hP']; linear_combination hαβ+ι f*ι w*α*hε⟩
  obtain ⟨u,hu⟩ : ∃ u : DiffRing V,
      u=ι (delta b')*ι (ycoord R b')*ι (xcoord (2*(I*(f*w))) b')*P' := ⟨_,rfl⟩
  have cu : Cop u (ι I) := by rw [hu]; exact cop_mul (cop_mul (cop_mul cδ cR) ce) cP
  -- `T(0)` and the choice of the step count `h`
  obtain ⟨T0,hT0⟩ := point a n0 R g J w I f ρ 0 hn0 hI hf hJ h4 hIpos hR hρ
  simp only [mul_zero,add_zero] at hT0
  rw [← hb'] at hT0
  obtain ⟨h',hh'⟩ := solve cu (t0-T0)
  obtain ⟨h,hh⟩ := exists_nat_congr M hM h'
  obtain ⟨Th,hTh⟩ := point a n0 R g J w I f ρ h hn0 hI hf hJ h4 hIpos hR hρ
  rw [← hb'] at hTh
  -- the linear law at `h`
  obtain ⟨r,s,hx,hy⟩ := doubled_quotients h (2*(I*(f*w))) b'
  have hadd := (addition R (2*h*(2*(I*(f*w)))) b').1
  have hνi : 2*(2*(R/4+I*(f*w)*h)+1)+1=R+2*h*(2*(I*(f*w))) := by
    calc 2*(2*(R/4+I*(f*w)*h)+1)+1=4*(R/4)+3+4*I*f*w*h := by ring
      _=R+2*h*(2*(I*(f*w))) := by rw [← hRq]; ring
  have hoe := odd_exact (2*(R/4+I*(f*w)*h)+1) b'
  rw [hνi,hb'2] at hoe
  have Hx := congrArg (ι (V := V)) hx
  have Hy := congrArg (ι (V := V)) hy
  have Hadd := congrArg (ι (V := V)) hadd
  have Hoe := congrArg (ι (V := V)) hoe
  simp only [map_add,map_mul,map_ofNat,map_one] at Hx Hy Hadd Hoe
  have hadd' : ι ρ*ι (oddQuotient (2*(R/4+I*(f*w)*h)+1) b')=
      ι (xcoord R b')*(1+ι (ycoord (2*(I*(f*w))) b')*ι (ycoord (2*(I*(f*w))) b')*ι r)+
      ι (delta b')*ι (ycoord R b')*
        (2*ι h*ι (xcoord (2*(I*(f*w))) b')*ι (ycoord (2*(I*(f*w))) b')+
          ι (ycoord (2*(I*(f*w))) b')*ι (ycoord (2*(I*(f*w))) b')*ι s) := by
    linear_combination -Hoe+Hadd+ι (xcoord R b')*Hx+ι (delta b')*ι (ycoord R b')*Hy
  have hV := linear_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hρ0 Dρ HχR hadd' HPe hPP
  rw [← hu] at hV
  have hlin := T_core _ _ _ _ _ _ _ _ _ _ _ _ hI0 F2 hT0 hTh hV
  have hMI' : (ι M : DiffRing V)∣ι I*ι I := by rw [← map_mul]; exact ι_dvd_iff.mpr hMI
  refine ⟨Th,ι (ycoord (R+2*h*(2*(I*(f*w)))) b'),?_,?_⟩
  · have e1 : (ι M : DiffRing V)∣Th-T0-ι h*u := dvd_trans hMI' ⟨_,hlin⟩
    have e2 : (ι M : DiffRing V)∣u*(ι h-h') := dvd_mul_of_dvd_right hh u
    have e3 : (ι M : DiffRing V)∣u*h'-(t0-T0) := dvd_trans hMI' hh'
    have e := dvd_add (dvd_add e1 e2) e3
    convert e using 1
    ring
  · have hVv : ι f^2*(ι (ycoord R a)-ι R+4*ι I*Th)-ι (ycoord R a)=
        ι (oddQuotient (2*(R/4+I*(f*w)*h)+1) b') := by
      linear_combination hTh
    rw [hVv]
    have Nν := congrArg (ι (V := V)) (norm (R+2*h*(2*(I*(f*w)))) b')
    simp only [map_add,map_mul,map_one] at Nν
    rw [Hoe] at Nν
    linear_combination Nν+(ι (ycoord (R+2*h*(2*(I*(f*w)))) b'))^2*D1ρ

/-- **Supported-modulus interpolation** with the strong index chosen
(`ZRowsPellValuation.strong_index`): for every `N > 0` with `4 ∣ N` there is `n0 > 0` with
`N ∣ I = ψ_A(n0)` such that every class modulo every `M ∣ I²` is hit by an auxiliary solution. -/
theorem supported_interpolation (a R N : V) (hR : R%4=3) (hN : 0<N) (h4N : 4∣N) :
    ∃ n0 : V, 0<n0 ∧ N∣ycoord n0 a ∧
      ∀ M : V, 0<M → M∣ycoord n0 a*ycoord n0 a → ∀ t0 : DiffRing V,
      ∃ T y : DiffRing V, (ι M : DiffRing V)∣T-t0 ∧
        (ι (delta a)*ι (ycoord n0 a))^2*
          (ι (xcoord n0 a)^2*(ι (ycoord R a)-ι R+4*ι (ycoord n0 a)*T)-ι (ycoord R a))^2-
          ((ι (delta a)*ι (ycoord n0 a))^2-1)*y^2=1 := by
  obtain ⟨n0,g,w,hn,hN',hgw,hg,hw⟩ := strong_index a N hN
  exact ⟨n0,hn,hN',fun M hM hMI t0 =>
    linear_interpolation a R n0 g w M t0 hn hR hgw hg hw (dvd_trans h4N hN') hM hMI⟩

#print axioms quotient_four_sq_pair
#print axioms square_period
#print axioms point
#print axioms linear_interpolation
#print axioms supported_interpolation

end DiophantineConsistency.ZRowsLinearInterpolation
