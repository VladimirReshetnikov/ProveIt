import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring

/-! A fixed Sigma1 gcd graph and normalization of the actual relaxed norm.
A bounded least positive natural Bezout certificate supplies divisibility;
no gcd, coprimality, minimality, factorization or Pell-index premise is used.
The common Pell-unit consumer is deliberately separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticGcdNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Signed coefficients are represented by two sums of natural multiples. -/
def Bez (a b g : V) : Prop :=
  ∃ u v w z : V, g+a*u+b*v=a*w+b*z

def GcdCert (a b g : V) : Prop := g∣a ∧ g∣b ∧ Bez a b g

/-- Model-independent syntax; no universal greatest-divisor clause. -/
def gcdDef : 𝚺₁.Semisentence 3 := .mkSigma
  “g a b. g ∣ a ∧ g ∣ b ∧ ∃ u v w z, g+a*u+b*v=a*w+b*z”

private theorem bez_swap {a b g : V} (h : Bez a b g) : Bez b a g := by
  obtain ⟨u,v,w,z,he⟩ := h
  refine ⟨v,u,z,w,?_⟩
  simpa only [add_assoc,add_comm,add_left_comm] using he

private theorem bez_remainder {a b g q r : V}
    (h : Bez a b g) (ha : a=g*q+r) : Bez a b r := by
  obtain ⟨u,v,w,z,he⟩ := h
  refine ⟨q*w,q*z,1+q*u,q*v,?_⟩
  calc
    r+a*(q*w)+b*(q*z)=r+q*(a*w+b*z) := by ring
    _=r+q*(g+a*u+b*v) := by rw [he]
    _=(g*q+r)+a*(q*u)+b*(q*v) := by ring
    _=a+a*(q*u)+b*(q*v) := by rw [←ha]
    _=a*(1+q*u)+b*(q*v) := by ring

/-- Every common divisor divides a natural Bezout certificate, including0. -/
theorem bez_divisor {a b g h : V} (hc : Bez a b g) (ha : h∣a) (hb : h∣b) :
    h∣g := by
  obtain ⟨u,v,w,z,he⟩ := hc
  by_cases hh : h=0
  · subst h
    have ha0 : a=0 := by simpa using ha
    have hb0 : b=0 := by simpa using hb
    have hg0 : g=0 := by simpa [ha0,hb0] using he
    simp [hg0]
  · have hp : 0<h := pos_iff_ne_zero.mpr hh
    obtain ⟨A,hA⟩ := ha
    obtain ⟨B,hB⟩ := hb
    apply mod_eq_zero_iff_dvd.mp
    have hm := congrArg (fun t : V => t%h) he
    simpa [hA,hB,mul_assoc,hp] using hm

/-- The positive search is bounded by a+b. Its coefficients stay existential.
A nonzero remainder would be a smaller certificate in the same search. -/
theorem gcd_certificate_exists (a b : V) : ∃ g : V, GcdCert a b g := by
  by_cases hz : a+b=0
  · have ha : a=0 := le_antisymm
      (le_trans (by simp : a≤a+b) (le_of_eq hz)) (Arithmetic.zero_le a)
    have hb : b=0 := le_antisymm
      (le_trans (by simp : b≤a+b) (le_of_eq hz)) (Arithmetic.zero_le b)
    refine ⟨0,?_,?_,0,0,0,0,?_⟩ <;> simp [ha,hb]
  · have hab : 0<a+b := pos_iff_ne_zero.mpr hz
    let P : V → Prop := fun g => 0<g ∧ g≤a+b ∧ Bez a b g
    have hP : 𝚺₁-Predicate P := by dsimp [P,Bez]; definability
    have hs : P (a+b) := ⟨hab,le_rfl,0,0,1,1,by simp⟩
    obtain ⟨g,hg,hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hs
    obtain ⟨hgp,hgb,hbez⟩ := hg
    have divides_of_remainder (x : V) (hrem : Bez a b (x%g)) : g∣x := by
      apply mod_eq_zero_iff_dvd.mp
      by_contra hn
      have hr : 0<x%g := pos_iff_ne_zero.mpr hn
      have hlt : x%g<g := mod_lt x hgp
      exact hmin (x%g) hlt ⟨hr,le_trans (le_of_lt hlt) hgb,hrem⟩
    have hda : g∣a := divides_of_remainder a (bez_remainder hbez (div_add_mod a g).symm)
    have hdb : g∣b := divides_of_remainder b
      (bez_swap (bez_remainder (bez_swap hbez) (div_add_mod b g).symm))
    exact ⟨g,hda,hdb,hbez⟩

theorem gcd_certificate_unique {a b g h : V}
    (hg : GcdCert a b g) (hh : GcdCert a b h) : g=h :=
  Arithmetic.dvd_antisymm (bez_divisor hh.2.2 hg.1 hg.2.1)
    (bez_divisor hg.2.2 hh.1 hh.2.1)

theorem gcd_certificate_total (a b : V) : ∃! g : V, GcdCert a b g := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists a b
  exact ⟨g,hg,fun h hh => gcd_certificate_unique hh hg⟩

noncomputable def gcdValue (a b : V) : V := Classical.choose! (gcd_certificate_total a b)

theorem gcd_graph (a b g : V) : GcdCert a b g ↔ g=gcdValue a b := by
  exact (Classical.choose!_eq_iff_right (gcd_certificate_total a b)).symm

instance gcd_defined : 𝚺₁-Function₂[V] gcdValue via gcdDef := .mk fun e => by
  simpa [gcdDef,GcdCert,Bez] using gcd_graph (e 1) (e 2) (e 0)

instance gcd_definable : 𝚺₁-Function₂[V] gcdValue := gcd_defined.to_definable

theorem gcd_total (a b : V) : ∃! g : V, gcdDef.val.Evalb ![g,a,b] := by simp

theorem gcd_spec (a b : V) : GcdCert a b (gcdValue a b) :=
  (gcd_graph a b _).mpr rfl

/-- This cancellation is proved from the actual coefficient identity. -/
theorem unit_certificate_cancel {t d x : V} (hu : Bez t d 1) (hx : d∣t*x) : d∣x := by
  obtain ⟨u,v,w,z,he⟩ := hu
  have hc : Bez (t*x) d x := by
    refine ⟨u,x*v,w,x*z,?_⟩
    calc
      x+(t*x)*u+d*(x*v)=x*(1+t*u+d*v) := by ring
      _=x*(t*w+d*z) := by rw [he]
      _=(t*x)*w+d*(x*z) := by ring
  exact bez_divisor hc hx (dvd_refl d)

/-- Actual norm normalization. The gcd and the quotient unit certificate are
derived here; no caller supplies either one. All factors returned are positive. -/
theorem norm_normalization (R D f : V)
    (hR : 0<R) (hD : 0<D) (_hf : 0<f) (hnorm : R*R+D=D*(f*f)) :
    ∃ d s t : V, 0<d ∧ 0<s ∧ 0<t ∧
      D=d*d*s ∧ R=d*s*t ∧ f*f=1+s*t*t := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists R D
  obtain ⟨t,hRt⟩ := hg.1
  obtain ⟨d,hDd⟩ := hg.2.1
  have hg0 : 0<g := pos_of_mul_pos_left (by rw [←hRt]; exact hR) (by simp)
  have ht0 : 0<t := pos_of_mul_pos_right (by rw [←hRt]; exact hR) (by simp)
  have hd0 : 0<d := pos_of_mul_pos_right (by rw [←hDd]; exact hD) (by simp)
  obtain ⟨u,v,w,z,he⟩ := hg.2.2
  have hunit : Bez t d 1 := by
    refine ⟨u,v,w,z,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hg0)
    calc
      g*(1+t*u+d*v)=g+R*u+D*v := by rw [hRt,hDd]; ring
      _=R*w+D*z := he
      _=g*(t*w+d*z) := by rw [hRt,hDd]; ring
  have hgn : g*t*t+d=d*(f*f) := by
    apply mul_left_cancel₀ (ne_of_gt hg0)
    calc
      g*(g*t*t+d)=R*R+D := by rw [hRt,hDd]; ring
      _=D*(f*f) := hnorm
      _=g*(d*(f*f)) := by rw [hDd]; ring
  have hdiv : d∣g*t*t := by
    apply mod_eq_zero_iff_dvd.mp
    have hm := congrArg (fun x : V => x%d) hgn
    simpa [hd0,mul_assoc] using hm
  have hdiv1 : d∣g*t := unit_certificate_cancel hunit
    (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hdiv)
  have hdiv2 : d∣g := unit_certificate_cancel hunit (by simpa only [mul_comm] using hdiv1)
  obtain ⟨s,hgs⟩ := hdiv2
  have hs0 : 0<s := pos_of_mul_pos_right (by rw [←hgs]; exact hg0) (by simp)
  have hlast : 1+s*t*t=f*f := by
    apply mul_left_cancel₀ (ne_of_gt hd0)
    calc
      d*(1+s*t*t)=g*t*t+d := by rw [hgs]; ring
      _=d*(f*f) := hgn
  refine ⟨d,s,t,hd0,hs0,ht0,?_,?_,hlast.symm⟩
  · rw [hDd,hgs]
    ring
  · rw [hRt,hgs]

/-- Positivity makes the truncated square norm equivalent to the additive norm. -/
theorem norm_tsub_to_add (D f R : V) (hf : 0 < f) (hnorm : R*R = D*(f*f-1)) :
    R*R + D = D*(f*f) := by
  have hf1 : 1 ≤ f := pos_iff_one_le.mp hf
  have hs : f*f-1+1 = f*f := tsub_add_cancel_of_le (one_le_mul hf1 hf1)
  calc
    R*R+D = D*(f*f-1)+D := by rw [hnorm]
    _ = D*(f*f-1+1) := by ring
    _ = D*(f*f) := by rw [hs]

/-- The literal truncated norm is converted only after f>0 justifies the
subtraction. No new index or source premise is introduced. -/
theorem norm_normalization_tsub (R D f : V)
    (hR : 0<R) (hD : 0<D) (hf : 0<f) (hnorm : R*R=D*(f*f-1)) :
    ∃ d s t : V, 0<d ∧ 0<s ∧ 0<t ∧
      D=d*d*s ∧ R=d*s*t ∧ f*f=1+s*t*t := by
  exact norm_normalization R D f hR hD hf (norm_tsub_to_add D f R hf hnorm)
end DiophantineConsistency.ArithmeticGcdNormalization
