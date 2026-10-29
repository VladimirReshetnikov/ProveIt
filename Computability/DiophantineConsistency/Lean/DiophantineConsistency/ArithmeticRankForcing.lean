import DiophantineConsistency.ArithmeticBinaryCarry

/-! Construction stage R (spec §6), generic part: the four-block rank.

For `q = 2^u`, blocks `A = C-1`, `F`, `α` with `A+1+F+α = q`, and two block
summands `M`, `H` that do not carry against `A` and `F`, the number

`fourBlocks = (A+M) + q*(F+H) + q^2*(F+α) + q^3*(A+α)`

has population exactly `2u + σ(M) + σ(H)`; it is `3 (mod 4)` when
`A ≡ 0`, `M ≡ 3 (mod 4)` and `u ≥ 2`; and it exceeds `2u`. The window-rank
formula of the current carrier equals `fourBlocks` (`rank_eq_fourBlocks`), so
the rank is *constructed* from the packing blocks, not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticRankForcing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A carry-free sum of two `u`-bit numbers is a `u`-bit number. -/
theorem noCarry_add_lt (u : V) : ∀ a<Exp.exp u, ∀ b<Exp.exp u, NoCarry a b → a+b<Exp.exp u := by
  induction u using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro a ha b hb _
    have ha0 : a=0 := le_antisymm (by simpa using lt_iff_succ_le.mp ha) (by simp)
    have hb0 : b=0 := le_antisymm (by simpa using lt_iff_succ_le.mp hb) (by simp)
    simp [ha0,hb0]
  case succ u ih =>
    intro a ha b hb hab
    have hda : 2*(a/2)+a%2=a := div_add_mod a 2
    have hdb : 2*(b/2)+b%2=b := div_add_mod b 2
    have hra : a%2≤1 := lt_two_iff_le_one.mp (by simp)
    have hrb : b%2≤1 := lt_two_iff_le_one.mp (by simp)
    have hab2 : NoCarry (2*(a/2)+a%2) (2*(b/2)+b%2) := by rw [hda,hdb]; exact hab
    obtain ⟨hrs,hab'⟩ := (noCarry_binary _ _ _ _ hra hrb).mp hab2
    have hqa : a/2<Exp.exp u := half_lt a _ (by simpa only [exp_succ] using ha)
    have hqb : b/2<Exp.exp u := half_lt b _ (by simpa only [exp_succ] using hb)
    have hsum := ih (a/2) hqa (b/2) hqb hab'
    have h1 : a/2+b/2+1≤Exp.exp u := lt_iff_succ_le.mp hsum
    rw [exp_succ]
    calc
      a+b=(2*(a/2)+a%2)+(2*(b/2)+b%2) := by rw [hda,hdb]
      _=2*(a/2+b/2)+(a%2+b%2) := by ring
      _≤2*(a/2+b/2)+1 := add_le_add le_rfl hrs
      _<2*(a/2+b/2)+1+1 := lt_add_one _
      _=2*(a/2+b/2+1) := by ring
      _≤2*Exp.exp u := mul_le_mul_of_nonneg_left h1 (by simp)

/-- The four-block number `(A+M) + q(F+H) + q²(F+α) + q³(A+α)`, `q = 2^u`. -/
def fourBlocks (u A M F H alpha : V) : V :=
  (A+M)+Exp.exp u*(F+H)+Exp.exp u^2*(F+alpha)+Exp.exp u^3*(A+alpha)

/-- **Population of the four-block rank.** -/
theorem fourBlocks_population (u A M F H alpha : V)
    (hsum : A+1+F+alpha=Exp.exp u) (hM : M<Exp.exp u) (hH : H<Exp.exp u)
    (hAM : NoCarry A M) (hFH : NoCarry F H) :
    population (fourBlocks u A M F H alpha)=2*u+(population M+population H) := by
  have hAq : A<Exp.exp u := by
    rw [←hsum,show A+1+F+alpha=(A+1)+(F+alpha) by ring]
    exact lt_of_lt_of_le (lt_add_one A) (le_add_right le_rfl)
  have hFq : F<Exp.exp u := by
    rw [←hsum,show A+1+F+alpha=(F+1)+(A+alpha) by ring]
    exact lt_of_lt_of_le (lt_add_one F) (le_add_right le_rfl)
  have hb3 : F+alpha<Exp.exp u := by
    rw [←hsum,show A+1+F+alpha=(F+alpha+1)+A by ring]
    exact lt_of_lt_of_le (lt_add_one _) (le_add_right le_rfl)
  have hb1 : A+M<Exp.exp u := noCarry_add_lt u A hAq M hM hAM
  have hb2 : F+H<Exp.exp u := noCarry_add_lt u F hFq H hH hFH
  have hc1 : Exp.exp u-1-A=F+alpha := by
    apply tsub_eq_of_eq_add
    apply tsub_eq_of_eq_add
    rw [←hsum]; ring
  have hc2 : Exp.exp u-1-F=A+alpha := by
    apply tsub_eq_of_eq_add
    apply tsub_eq_of_eq_add
    rw [←hsum]; ring
  have hcomp1 := complement u A hAq
  have hcomp2 := complement u F hFq
  rw [hc1] at hcomp1
  rw [hc2] at hcomp2
  have hnest : fourBlocks u A M F H alpha=
      (((A+alpha)*Exp.exp u+(F+alpha))*Exp.exp u+(F+H))*Exp.exp u+(A+M) := by
    unfold fourBlocks; ring
  rw [hnest,concatenate _ u _ hb1,concatenate _ u _ hb2,concatenate _ u _ hb3,
    (population_add_eq_iff A M).mpr hAM,(population_add_eq_iff F H).mpr hFH]
  calc
    population (A+alpha)+population (F+alpha)+(population F+population H)+
        (population A+population M)=
      (population A+population (F+alpha))+(population F+population (A+alpha))+
        (population M+population H) := by ring
    _=2*u+(population M+population H) := by rw [hcomp1,hcomp2]; ring

/-- **Residue.** `fourBlocks ≡ 3 (mod 4)` when `A ≡ 0`, `M ≡ 3 (mod 4)`, `u ≥ 2`. -/
theorem fourBlocks_mod_four (u A M F H alpha : V) (hu : 2≤u)
    (hA : A%4=0) (hM : M%4=3) : fourBlocks u A M F H alpha%4=3 := by
  obtain ⟨e,rfl⟩ : ∃ e, u=2+e := ⟨u-2,(add_tsub_cancel_of_le hu).symm⟩
  have hq : Exp.exp (2+e)=4*Exp.exp e := by
    rw [exp_add,show (2:V)=1+1 by ring,exp_add,exp_one]; ring
  unfold fourBlocks
  rw [hq]
  have h4 : (0:V)<4 := by norm_num
  simp [pow_succ, mod_add h4, mod_mul h4, hA, hM,
    mod_eq_self_of_lt (show (3:V)<4 by exact_mod_cast (show (3:ℕ)<4 by decide))]

/-- **Size.** `2u < q^3 ≤ fourBlocks` once `α > 0`. -/
theorem fourBlocks_gt (u A M F H alpha : V) (halpha : 0<alpha) :
    2*u<fourBlocks u A M F H alpha := by
  have hq : u<Exp.exp u := lt_exp u
  have hq1 : 1≤Exp.exp u := one_le_exp u
  have hcube : 2*u<Exp.exp u^3 := by
    rcases zero_or_succ u with rfl|⟨w,rfl⟩
    · simp
    · have h2 : 2≤Exp.exp (w+1) := by
        rw [exp_succ]
        calc
          (2:V)=2*1 := by ring
          _≤2*Exp.exp w := mul_le_mul_of_nonneg_left (one_le_exp w) (by simp)
      calc
        2*(w+1)<2*Exp.exp (w+1) := mul_lt_mul_of_pos_left hq (by simp)
        _≤Exp.exp (w+1)*Exp.exp (w+1) := mul_le_mul_of_nonneg_right h2 (by simp)
        _≤Exp.exp (w+1)*Exp.exp (w+1)*Exp.exp (w+1) := le_mul_of_one_le_right (by simp) hq1
        _=Exp.exp (w+1)^3 := by ring
  have h1 : 1≤A+alpha := le_trans (pos_iff_one_le.mp halpha) (le_add_of_nonneg_left (by simp))
  calc
    2*u<Exp.exp u^3 := hcube
    _≤Exp.exp u^3*(A+alpha) := le_mul_of_one_le_right (by simp) h1
    _≤fourBlocks u A M F H alpha := by
      unfold fourBlocks; exact le_add_of_nonneg_left (by simp)

/-- **The window rank is the four-block number.** `q = β*J+1`, the low summand
is `M = MC*J+1` and the high summand `H` satisfies `H+1 = HP*J`; the fourth
port is `HP+β` (the single β shift). -/
theorem rank_eq_fourBlocks (u q beta J MC HP A F alpha H : V)
    (hq : beta*J+1=q) (hqu : q=Exp.exp u) (hsum : A+1+F+alpha=q) (hH : H+1=HP*J) :
    ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*(HP+beta))*J=
      fourBlocks u A (MC*J+1) F H alpha := by
  have hq1 : q-1=A+F+alpha := tsub_eq_of_eq_add (by rw [←hsum]; ring)
  have hqF : q-F=A+1+alpha := tsub_eq_of_eq_add (by rw [←hsum]; ring)
  have hq2 : q^2-1=(A+F+alpha)*(q+1) := tsub_eq_of_eq_add (by rw [←hsum]; ring)
  have hbJ : beta*J=A+F+alpha := by
    apply add_right_cancel (b:=(1:V)); rw [hq,←hsum]; ring
  have e1 : (MC+q*(HP+beta))*J=MC*J+q*(HP*J)+q*(beta*J) := by ring
  unfold fourBlocks
  rw [e1,←hH,hbJ,hq1,hqF,hq2,←hqu,←hsum]
  ring

end DiophantineConsistency.ArithmeticRankForcing
