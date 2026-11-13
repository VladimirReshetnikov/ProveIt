import DiophantineConsistency.ZRows.LinearInterpolation

/-! # Supported-modulus interpolation modulo `I⁴` by two-level linear stepping

In every model `V` of `𝗜𝚺₁`, with the data of `ZRowsLinearInterpolation` (main base `A = a + 2`,
`Δ = delta a`, index `R ≡ 3 (mod 4)`, `c = ψ_A(R)`, strong pair `I = ψ_A(n0)`, `f = χ_A(n0)`,
`4 ∣ I`, split `n0 = g·w` with `g ∣ I` and `w` coprime to `I`, auxiliary base `ρ = Δ·I`), the
abscissa quotient `T(h)` of the progression `ν(h) = R + 4·I·f·w·h` is integral at every `h`
(`ZRowsLinearInterpolation.point`). Stage 3 showed that `T` reaches every class modulo `I²`.
This module shows that it reaches every class modulo `I⁴` (`quartic_interpolation`,
`supported_interpolation4`), which is what the linear-cofactor completeness needs: there the
modulus is `u·s·r = A²·d·s·t³`, which divides `I⁴` but in general not `I²`.

The argument is a second level of the same linear stepping:

* `step_law`: from an **arbitrary** base point `h₀` of the progression and a half step
  `m = 2·I·f·w·k` with `ψ_ρ(m) = 2ρ·I·Q·P`, the addition formula and the doubled quotients give
  `f²·(T(h₀ + k·h) − T(h₀)) = Q·(h·u + I²·Q·K)` with `u = (ρ²−1)·ψ_ρ(ν(h₀))·χ_ρ(m)·P`;
* `first_ordinate`: `ψ_ρ(2·I·f·w) = 2ρ·I·P₁` with `P₁` coprime to `I` (stage 3's even-ordinate
  law, `ZRowsPellEvenChebyshev.even_ordinate`);
* `second_ordinate`: `ψ_ρ(2·I·f·w·I²) = 2ρ·I³·P₂` with `P₂` coprime to `I`. The composition
  `ψ_ρ(m₁·I²) = ψ_ρ(m₁)·ψ_C(I²)` with `C = χ_ρ(m₁)`, the residue law `ψ_C(N) ≡ N (mod C − 1)`
  (`ArithmeticPellCongruences.residue_quotients`) and `C − 1 = 2(ρ²−1)ψ_ρ(I·f·w)²` with
  `Δ·I² ∣ ψ_ρ(I) ∣ ψ_ρ(I·f·w)` (`ZRowsPellValuation.lift`) give `ψ_C(I²) = I²·(1 + I²·E)`;
* every factor of `u` is coprime to `I` at every base point (`cop_odd`, `cop_x`);
* so `T(h₁) ≡ T(0) + h₁·u₁ (mod I²)` (`level_one`) and
  `T(h₁ + I²h₂) ≡ T(h₁) + I²·h₂·u₂(h₁) (mod I⁴)` (`level_two`); choosing `h₁` by Bezout modulo
  `I²` and then `h₂` by Bezout modulo `I²` hits every target modulo `I⁴`.

A sharper even-ordinate law `P ≡ ±L (mod L·ρ²)` is *not* used, and is false in general
(for `a = 0`, `n0 = 6`, `I = 780`, `L = I³·f·w`, it fails); only `P₂` coprime to `I` is needed.

**Genericity boundary.** The modulus bound is `M ∣ I⁴`. The same `step_law` applies at every
level `Q = I^(2j)`, but `second_ordinate` only gives the unit cofactor at `Q = I²` (the residue
law yields `ψ_C(N) ≡ N` modulo `C − 1`, where `I⁴ ∣ C − 1`, not modulo `N·(C − 1)`); higher
levels would need one composition per level, i.e. an internal induction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ZRowsQuarticInterpolation
open ZRowsLinearInterpolation

/-! ### Ring algebra (no model needed) -/

section Ring
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The linear law of the abscissa quotient from an arbitrary base point, for a half step whose
ordinate is `2ρ·I·Q·P`. -/
theorem law_ring [NoZeroDivisors 𝔸] (ρ Δ I Q V0 Vh ψR χm ψm r s P δ h f2 T0 Th C1 C2 : 𝔸)
    (hρ0 : ρ≠0) (hI : (4:𝔸)*I≠0) (hρ : ρ=Δ*I)
    (hadd : ρ*Vh=ρ*V0*(1+ψm*ψm*r)+δ*ψR*(2*h*χm*ψm+ψm*ψm*s))
    (hψm : ψm=2*ρ*(I*Q*P))
    (hT0 : 4*I*f2*T0=V0+C1-C2) (hTh : 4*I*f2*Th=Vh+C1-C2) :
    f2*(Th-T0)=Q*(h*(δ*ψR*χm*P)+I*I*Q*(Δ*Δ*I*P*P*V0*r+Δ*P*P*δ*ψR*s)) := by
  subst hψm hρ
  have key : Δ*I*(4*I*(f2*(Th-T0)-
      Q*(h*(δ*ψR*χm*P)+I*I*Q*(Δ*Δ*I*P*P*V0*r+Δ*P*P*δ*ψR*s))))=0 := by
    linear_combination (Δ*I)*hTh-(Δ*I)*hT0+hadd
  rcases mul_eq_zero.mp key with h0|h0
  · exact absurd h0 hρ0
  · rcases mul_eq_zero.mp h0 with h1|h1
    · exact absurd h1 hI
    · exact sub_eq_zero.mp h1

/-- The first level: `T(h) ≡ T(0) + h·u (mod I²)`. -/
theorem level_one (Δ I f2 T0 Th h u K : 𝔸) (hf : f2=1+Δ*I*I)
    (e : f2*(Th-T0)=1*(h*u+I*I*1*K)) : Th-T0-h*u=I*I*(K-Δ*(Th-T0)) := by
  linear_combination e-(Th-T0)*hf

/-- The second level: `T(h₁ + I²h) ≡ T(h₁) + I²·h·u (mod I⁴)`. -/
theorem level_two (Δ I f2 T0 Th h u K : 𝔸) (hf : f2=1+Δ*I*I)
    (e : f2*(Th-T0)=I*I*(h*u+I*I*(I*I)*K)) :
    Th-T0-I*I*h*u=I*I*(I*I)*(I*I*K-Δ*h*u-Δ*I*I*(I*I)*K+Δ*Δ*(Th-T0)) := by
  linear_combination (1-Δ*I*I)*(e-(Th-T0)*hf)

theorem cop_one_add (I E : 𝔸) : Cop (1+I*I*E) I := ⟨1,-(I*E),by ring⟩

theorem cop_pred (δ I G : 𝔸) (h : δ+1=I*G) : Cop δ I :=
  ⟨-1,G,by linear_combination (-1:𝔸)*h⟩

theorem cop_of_norm_x (χ δ I G : 𝔸) (h : χ*χ=1+δ*(I*G)) : Cop χ I :=
  ⟨χ,-(δ*G),by linear_combination h⟩

theorem cop_of_norm_y (χ ψ δ I G : 𝔸) (h : χ*χ=1+δ*ψ*ψ) (hχ : χ=I*G) : Cop ψ I :=
  ⟨-(δ*ψ),G*χ,by subst hχ; linear_combination h⟩

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellSquaredSeed
open ArithmeticPellHalfIndex ArithmeticPellCommonUnit ArithmeticPellCongruences
open ZRowsCoprimeSquares ZRowsIntersective19 ZRowsPellValuation ZRowsPellEvenChebyshev

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord oddQuotient

/-! ### The addition step at an arbitrary odd base index -/

/-- `χ(2j'+1) = χ(2j+1)·χ(2hm) + δ·ψ(2j+1)·ψ(2hm)` in quotient form, at `2j'+1 = 2j+1+2hm`. -/
theorem stepped (b j j' m h : V) (hidx : 2*j'+1=2*j+1+2*h*m) :
    ∃ r s : V, (b+2)*oddQuotient j' b=(b+2)*oddQuotient j b*(1+ycoord m b*ycoord m b*r)+
      delta b*ycoord (2*j+1) b*(2*h*xcoord m b*ycoord m b+ycoord m b*ycoord m b*s) := by
  obtain ⟨r,s,hx,hy⟩ := doubled_quotients h m b
  refine ⟨r,s,?_⟩
  rw [← odd_exact j' b,← odd_exact j b,hidx,(addition (2*j+1) (2*h*m) b).1,hx,hy]

/-- **The linear law from an arbitrary base point** `h₀` of the progression, for the step
`k·h` with half step `m = 2·I·f·w·k` and `ψ_ρ(m) = 2ρ·I·Q·P`. -/
theorem step_law (a R I f w ρ b' h₀ h₁ h m k : V) (Q P T0 T1 C1 C2 : DiffRing V)
    (hρ : ρ=delta a*I) (hb : b'+2=ρ) (hIpos : 0<I)
    (hh : h₁=h₀+k*h) (hm : m=2*(I*(f*w))*k)
    (hψ : ι (ycoord m b')=2*ι ρ*(ι I*Q*P))
    (hT0 : 4*ι I*(ι f*ι f)*T0=ι (oddQuotient (2*(R/4+I*(f*w)*h₀)+1) b')+C1-C2)
    (hT1 : 4*ι I*(ι f*ι f)*T1=ι (oddQuotient (2*(R/4+I*(f*w)*h₁)+1) b')+C1-C2) :
    ∃ K : DiffRing V, ι f*ι f*(T1-T0)=Q*(ι h*(ι (delta b')*
      ι (ycoord (2*(2*(R/4+I*(f*w)*h₀)+1)+1) b')*ι (xcoord m b')*P)+ι I*ι I*Q*K) := by
  have hidx : 2*(2*(R/4+I*(f*w)*h₁)+1)+1=2*(2*(R/4+I*(f*w)*h₀)+1)+1+2*h*m := by
    rw [hh,hm]; ring
  obtain ⟨r,s,hst⟩ := stepped b' _ _ m h hidx
  rw [hb] at hst
  have Hst := congrArg (ι (V := V)) hst
  simp only [map_add,map_mul,map_ofNat,map_one] at Hst
  have Dρ : (ι ρ : DiffRing V)=ι (delta a)*ι I := by rw [hρ,map_mul]
  have hρ0 : (ι ρ : DiffRing V)≠0 := by
    have hlt : (0:DiffRing V)<ι ρ := by
      rw [← map_zero (ι (V := V))]
      exact ι_lt_ι.mpr (by rw [← hb]; exact lt_of_lt_of_le (by norm_num) le_add_self)
    exact ne_of_gt hlt
  have hI0 : (4:DiffRing V)*ι I≠0 := by
    have hlt : (0:DiffRing V)<ι I := by
      rw [← map_zero (ι (V := V))]
      exact ι_lt_ι.mpr hIpos
    exact ne_of_gt (mul_pos (by norm_num) hlt)
  exact ⟨_,law_ring _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hρ0 hI0 Dρ Hst hψ hT0 hT1⟩

/-! ### Units modulo `I` -/

/-- Odd auxiliary ordinates are units modulo `I`: `χ_ρ(2j+1) = ρ·V ≡ 0`, so `δψ² ≡ −1`. -/
theorem cop_odd (Δ I ρ b' j : V) (hb : b'+2=ρ) (hρ : ρ=Δ*I) :
    Cop (ι (ycoord (2*j+1) b')) (ι I) := by
  have N := congrArg (ι (V := V)) (norm (2*j+1) b')
  rw [odd_exact j b',hb] at N
  simp only [map_add,map_mul,map_one] at N
  exact cop_of_norm_y _ _ _ _ (ι Δ*ι (oddQuotient j b')) N (by rw [hρ,map_mul]; ring)

/-- An abscissa whose ordinate is divisible by `I` is a unit modulo `I`. -/
theorem cop_x (I ρ b' m : V) (Q P : DiffRing V) (hψ : ι (ycoord m b')=2*ι ρ*(ι I*Q*P)) :
    Cop (ι (xcoord m b')) (ι I) := by
  have N := congrArg (ι (V := V)) (norm m b')
  simp only [map_add,map_mul,map_one] at N
  rw [hψ] at N
  exact cop_of_norm_x _ (ι (delta b')) (ι I) (4*ι ρ*ι ρ*ι I*Q*Q*P*P)
    (by linear_combination N)

/-! ### The two half-step ordinates -/

/-- **First level** (stage 3): `ψ_ρ(2·I·f·w) = 2ρ·I·P₁` with `P₁` coprime to `I`. -/
theorem first_ordinate (Δ I f w ρ b' : V) (hb : b'+2=ρ) (hρ : ρ=Δ*I)
    (cfw : Cop (ι (f*w)) (ι I)) :
    ∃ P : DiffRing V, ι (ycoord (2*(I*(f*w))) b')=2*ι ρ*(ι I*1*P) ∧ Cop P (ι I) := by
  obtain ⟨P,hPe,hPs⟩ := even_ordinate b' (I*(f*w))
  rw [hb] at hPe hPs
  obtain ⟨ε,k,hε,hPk⟩ : ∃ ε k : DiffRing V, ε*ε=1 ∧ ι P=ε*ι (I*(f*w))+ι (4*ρ*ρ)*k := by
    rcases hPs with h|h
    · obtain ⟨k,hk⟩ := mod_eq_zero_iff_dvd.mp h
      have hk' := congrArg (ι (V := V)) hk
      rw [map_add,map_mul (ι (V := V)) (4*ρ*ρ) k] at hk'
      exact ⟨-1,ι k,by ring,by linear_combination hk'⟩
    · obtain ⟨q,hq⟩ := ringSub_of_mod_eq h
      exact ⟨1,q,by ring,by linear_combination hq⟩
  have R1 : ι (4*ρ*ρ)=4*ι Δ*ι Δ*ι I*ι I := by
    rw [hρ]; simp only [map_mul,map_ofNat]; ring
  have R2 : ι (I*(f*w))=ι I*ι (f*w) := map_mul _ _ _
  have hPP : ι P=ι I*1*(ε*ι (f*w)+4*ι Δ*ι Δ*ι I*k) := by rw [hPk,R1,R2]; ring
  obtain ⟨α,β,hαβ⟩ := cfw
  have HPe : ι (ycoord (2*(I*(f*w))) b')=2*ι ρ*ι P := by
    rw [hPe]; simp only [map_mul,map_ofNat]
  refine ⟨ε*ι (f*w)+4*ι Δ*ι Δ*ι I*k,by rw [HPe,hPP],
    ⟨ε*α,β-4*ι Δ*ι Δ*k*ε*α,by linear_combination hαβ+ι (f*w)*α*hε⟩⟩

/-- **Second level**: `ψ_ρ(2·I·f·w·I²) = 2ρ·I³·P₂` with `P₂` coprime to `I`, by composition
at `C = χ_ρ(2·I·f·w)` and the residue law `ψ_C(I²) ≡ I² (mod C − 1)`, where `I⁴ ∣ C − 1`. -/
theorem second_ordinate (Δ I f w ρ b' : V) (P : DiffRing V) (hb : b'+2=ρ) (hρ : ρ=Δ*I)
    (hI4 : 4∣I) (hIpos : 0<I) (hfw : 0<f*w)
    (hP : ι (ycoord (2*(I*(f*w))) b')=2*ι ρ*(ι I*1*P)) (cP : Cop P (ι I)) :
    ∃ P2 : DiffRing V, ι (ycoord (2*(I*(f*w))*(I*I)) b')=2*ι ρ*(ι I*(ι I*ι I)*P2) ∧
      Cop P2 (ι I) := by
  obtain ⟨I',hI'⟩ := hI4
  -- `Δ·I² ∣ ψ_ρ(I) ∣ ψ_ρ(I·f·w)`
  have h2 : 2*I'∣ycoord 2 b' := ⟨4*Δ,by rw [y_two,hb,hρ,hI']; ring⟩
  have hl := ZRowsPellValuation.lift b' 2 (2*I') h2
  rw [show 2*I'*2=I by rw [hI']; ring] at hl
  have hII : I*I∣ycoord (I*(f*w)) b' :=
    dvd_trans (dvd_trans ⟨Δ,by rw [y_two,hb,hρ,hI']; ring⟩ hl) (y_dvd_mul b' I (f*w))
  obtain ⟨X,hX⟩ := hII
  -- the composed base `C = χ_ρ(m₁)`
  have hm1 : 0<2*(I*(f*w)) := mul_pos (by norm_num) (mul_pos hIpos hfw)
  have hC := two_le_x b' (2*(I*(f*w))) hm1
  obtain ⟨a2,ha2⟩ : ∃ a2 : V, a2=xcoord (2*(I*(f*w))) b'-2 := ⟨_,rfl⟩
  have hA : a2+2=xcoord (2*(I*(f*w))) b' := by rw [ha2]; exact tsub_add_cancel_of_le hC
  have comp := (composition a2 b' (2*(I*(f*w))) hA (I*I)).2
  obtain ⟨-,s,-,hs⟩ := residue_quotients (I*I) a2 (a2+1) dvd_rfl
  have ha1 : a2+1=2*delta b'*ycoord (I*(f*w)) b'*ycoord (I*(f*w)) b' := by
    have e : a2+1+1=2*delta b'*ycoord (I*(f*w)) b'*ycoord (I*(f*w)) b'+1 := by
      rw [show a2+1+1=a2+2 by ring,hA,double_x]; ring
    exact add_right_cancel e
  rw [ha1,hX] at hs
  have Hs := congrArg (ι (V := V)) hs
  simp only [map_add,map_mul,map_ofNat] at Hs
  refine ⟨P*(1+ι I*ι I*(2*ι (delta b')*ι X*ι X*ι s)),?_,cop_mul cP (cop_one_add _ _)⟩
  rw [← comp,map_mul,Hs,hP]
  ring

/-! ### Interpolation modulo `I⁴` -/

/-- **Supported-modulus interpolation modulo `I⁴`** for a strong index with a coprime split
`n0 = g·w`, `g ∣ I`, `w` coprime to `I` (`I = ψ_A(n0)`, `4 ∣ I`): for every `M ∣ I⁴` and every
target `t0` there are `T ≡ t0 (mod M)` and `y` with `ρ²V² − (ρ²−1)y² = 1`, where `ρ = Δ·I` and
`V = f²(c − R + 4I·T) − c`. The exact analogue of `ZRowsLinearInterpolation.linear_interpolation`
with `M ∣ I²` replaced by `M ∣ I⁴` (the hypothesis `0 < M` is not needed here). -/
theorem quartic_interpolation (a R n0 g w M : V) (t0 : DiffRing V)
    (hn : 0<n0) (hR : R%4=3) (hn0 : n0=g*w) (hg : g∣ycoord n0 a)
    (hw : Bez w (ycoord n0 a) 1) (h4 : 4∣ycoord n0 a)
    (hMI : M∣ycoord n0 a*ycoord n0 a*(ycoord n0 a*ycoord n0 a)) :
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
  have F2 : ι f*ι f=1+ι (delta a)*ι I*ι I := by
    have e := congrArg (ι (V := V)) hf2
    simpa only [map_add,map_mul,map_one] using e
  have D1ρ : ι (delta b')+1=ι ρ*ι ρ := by
    have e := congrArg (ι (V := V)) hδ
    simpa only [map_add,map_mul,map_one] using e
  have hw0 : 0<w := by
    rcases (Arithmetic.zero_le w).lt_or_eq with h|h
    · exact h
    · exfalso
      rw [← h,mul_zero] at hn0
      rw [hn0] at hn
      exact _root_.lt_irrefl _ hn
  have hfpos : 0<f := by
    rw [hf]
    exact lt_of_lt_of_le _root_.zero_lt_one (one_le_x n0 a)
  have hfw : 0<f*w := mul_pos hfpos hw0
  -- units modulo `I`
  have cf : Cop (ι f) (ι I) := ⟨ι f,-(ι (delta a)*ι I),by linear_combination F2⟩
  have cw : Cop (ι w) (ι I) := bez_one_iff_ring.mp hw
  have cfw : Cop (ι (f*w)) (ι I) := by rw [map_mul]; exact cop_mul cf cw
  have cδ : Cop (ι (delta b')) (ι I) :=
    cop_pred _ _ (ι (delta a)*ι (delta a)*ι I) (by rw [D1ρ,Dρ]; ring)
  -- the two half-step ordinates
  obtain ⟨P1,hP1,cP1⟩ := first_ordinate (delta a) I f w ρ b' hb'2 hρ cfw
  obtain ⟨P2,hP2,cP2⟩ := second_ordinate (delta a) I f w ρ b' P1 hb'2 hρ h4 hIpos hfw hP1 cP1
  have hII : 0<I*I := mul_pos hIpos hIpos
  -- first level: `T(h₁) ≡ t0 (mod I²)`
  have cu1 := cop_mul (cop_mul (cop_mul cδ
    (cop_odd (delta a) I ρ b' (2*(R/4+I*(f*w)*0)+1) hb'2 hρ)) (cop_x I ρ b' _ 1 P1 hP1)) cP1
  obtain ⟨T0,hT0⟩ := point a n0 R g J w I f ρ 0 hn0 hI hf hJ h4 hIpos hR hρ
  rw [← hb'] at hT0
  obtain ⟨h1',hh1'⟩ := ZRowsLinearInterpolation.solve cu1 (t0-T0)
  obtain ⟨h1,hh1⟩ := exists_nat_congr (I*I) hII h1'
  rw [map_mul] at hh1
  obtain ⟨T1,hT1⟩ := point a n0 R g J w I f ρ h1 hn0 hI hf hJ h4 hIpos hR hρ
  rw [← hb'] at hT1
  obtain ⟨K1,e1⟩ := step_law a R I f w ρ b' 0 h1 h1 (2*(I*(f*w))) 1 1 P1 T0 T1 _ _
    hρ hb'2 hIpos (by ring) (by ring) hP1 hT0 hT1
  have l1 := level_one _ _ _ _ _ _ _ _ F2 e1
  have dz : (ι I*ι I : DiffRing V)∣T1-t0 := by
    have d1 : (ι I*ι I : DiffRing V)∣_ := ⟨_,l1⟩
    have d2 := dvd_mul_of_dvd_right hh1
      (ι (delta b')*ι (ycoord (2*(2*(R/4+I*(f*w)*0)+1)+1) b')*
        ι (xcoord (2*(I*(f*w))) b')*P1)
    have e := dvd_add (dvd_add d1 d2) hh1'
    convert e using 1
    ring
  obtain ⟨z,hz⟩ := dz
  -- second level: `T(h₁ + I²h₂) ≡ t0 (mod I⁴)`
  have cu2 := cop_mul (cop_mul (cop_mul cδ
    (cop_odd (delta a) I ρ b' (2*(R/4+I*(f*w)*h1)+1) hb'2 hρ))
    (cop_x I ρ b' _ (ι I*ι I) P2 hP2)) cP2
  obtain ⟨h2',hh2'⟩ := ZRowsLinearInterpolation.solve cu2 (-z)
  obtain ⟨h2,hh2⟩ := exists_nat_congr (I*I) hII h2'
  rw [map_mul] at hh2
  obtain ⟨T2,hT2⟩ := point a n0 R g J w I f ρ (h1+I*I*h2) hn0 hI hf hJ h4 hIpos hR hρ
  rw [← hb'] at hT2
  obtain ⟨K2,e2⟩ := step_law a R I f w ρ b' h1 (h1+I*I*h2) h2 (2*(I*(f*w))*(I*I)) (I*I)
    (ι I*ι I) P2 T1 T2 _ _ hρ hb'2 hIpos rfl rfl hP2 hT1 hT2
  have l2 := level_two _ _ _ _ _ _ _ _ F2 e2
  have hMI' : (ι M : DiffRing V)∣ι I*ι I*(ι I*ι I) := by
    simpa only [map_mul] using (ι_dvd_iff.mpr hMI : (ι M : DiffRing V)∣ι (I*I*(I*I)))
  refine ⟨T2,ι (ycoord (2*(2*(R/4+I*(f*w)*(h1+I*I*h2))+1)+1) b'),?_,?_⟩
  · have d1 : (ι I*ι I*(ι I*ι I) : DiffRing V)∣_ := ⟨_,l2⟩
    have d2 : (ι I*ι I*(ι I*ι I) : DiffRing V)∣ι I*ι I*((ι (delta b')*
        ι (ycoord (2*(2*(R/4+I*(f*w)*h1)+1)+1) b')*
        ι (xcoord (2*(I*(f*w))*(I*I)) b')*P2)*(ι h2-h2')) :=
      mul_dvd_mul_left _ (dvd_mul_of_dvd_right hh2 _)
    have d3 : (ι I*ι I*(ι I*ι I) : DiffRing V)∣ι I*ι I*((ι (delta b')*
        ι (ycoord (2*(2*(R/4+I*(f*w)*h1)+1)+1) b')*
        ι (xcoord (2*(I*(f*w))*(I*I)) b')*P2)*h2'-(-z)) :=
      mul_dvd_mul_left _ hh2'
    have e := dvd_trans hMI' (dvd_add (dvd_add d1 d2) d3)
    convert e using 1
    linear_combination hz
  · have hVv : ι f^2*(ι (ycoord R a)-ι R+4*ι I*T2)-ι (ycoord R a)=
        ι (oddQuotient (2*(R/4+I*(f*w)*(h1+I*I*h2))+1) b') := by
      linear_combination hT2
    rw [hVv]
    have N := congrArg (ι (V := V)) (norm (2*(2*(R/4+I*(f*w)*(h1+I*I*h2))+1)+1) b')
    rw [odd_exact _ b',hb'2] at N
    simp only [map_add,map_mul,map_one] at N
    linear_combination N+(ι (ycoord (2*(2*(R/4+I*(f*w)*(h1+I*I*h2))+1)+1) b'))^2*D1ρ

/-- **Supported-modulus interpolation modulo `I⁴`** with the strong index chosen
(`ZRowsPellValuation.strong_index`): for every `N > 0` with `4 ∣ N` there is `n0 > 0` with
`N ∣ I = ψ_A(n0)` such that every class modulo every `M ∣ I⁴` is hit by an auxiliary solution.
The statement has the shape of `ZRowsLinearInterpolation.supported_interpolation` (including the
redundant `0 < M`), so callers can switch by changing `I²` to `I⁴`. -/
theorem supported_interpolation4 (a R N : V) (hR : R%4=3) (hN : 0<N) (h4N : 4∣N) :
    ∃ n0 : V, 0<n0 ∧ N∣ycoord n0 a ∧
      ∀ M : V, 0<M → M∣ycoord n0 a*ycoord n0 a*(ycoord n0 a*ycoord n0 a) →
      ∀ t0 : DiffRing V,
      ∃ T y : DiffRing V, (ι M : DiffRing V)∣T-t0 ∧
        (ι (delta a)*ι (ycoord n0 a))^2*
          (ι (xcoord n0 a)^2*(ι (ycoord R a)-ι R+4*ι (ycoord n0 a)*T)-ι (ycoord R a))^2-
          ((ι (delta a)*ι (ycoord n0 a))^2-1)*y^2=1 := by
  obtain ⟨n0,g,w,hn,hN',hgw,hg,hw⟩ := strong_index a N hN
  exact ⟨n0,hn,hN',fun M _ hMI t0 =>
    quartic_interpolation a R n0 g w M t0 hn hR hgw hg hw (dvd_trans h4N hN') hMI⟩

#print axioms step_law
#print axioms first_ordinate
#print axioms second_ordinate
#print axioms quartic_interpolation
#print axioms supported_interpolation4

end DiophantineConsistency.ZRowsQuarticInterpolation
