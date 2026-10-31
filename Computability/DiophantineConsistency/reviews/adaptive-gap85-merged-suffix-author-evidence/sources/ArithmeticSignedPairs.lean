import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring

/-! Natural signed-pair algebra for internal carrier factor extraction.
All components are internal numbers. Equivalence is cross-sum equality;
neither a standard integer interpretation nor a quotient is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSignedPairs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev Pair (V : Type*) := V × V
def natural (a : V) : Pair V := (a,0)
def swap (p : Pair V) : Pair V := (p.2,p.1)
def multiply (p q : Pair V) : Pair V :=
  (p.1*q.1+p.2*q.2,p.1*q.2+p.2*q.1)
def scale (a : V) (p : Pair V) : Pair V := (a*p.1,a*p.2)
def Equivalent (p q : Pair V) : Prop := p.1+q.2=p.2+q.1
def magnitude (p : Pair V) : V := (p.1-p.2)+(p.2-p.1)
def product5 (p q r s t : Pair V) : Pair V :=
  multiply (multiply (multiply (multiply p q) r) s) t

theorem equivalent_refl (p : Pair V) : Equivalent p p := by
  simp only [Equivalent,add_comm]
theorem equivalent_symm {p q : Pair V} (h : Equivalent p q) : Equivalent q p := by
  simpa only [Equivalent,add_comm] using h.symm
theorem equivalent_trans {p q r : Pair V} (h : Equivalent p q) (k : Equivalent q r) :
    Equivalent p r := by
  apply add_right_cancel (b:=q.2)
  calc
    (p.1+r.2)+q.2=(p.1+q.2)+r.2 := by ring
    _=(p.2+q.1)+r.2 := by rw [h]
    _=p.2+(q.1+r.2) := by ring
    _=p.2+(q.2+r.1) := by rw [k]
    _=(p.2+r.1)+q.2 := by ring

theorem equivalent_one {p : Pair V} : Equivalent p (natural (1:V)) ↔ p.1=p.2+1 := by
  simp only [Equivalent,natural,add_zero]
theorem multiply_comm (p q : Pair V) : multiply p q=multiply q p := by
  apply Prod.ext <;> simp only [multiply] <;> ring
@[simp] theorem multiply_one (p : Pair V) : multiply p (natural (1:V))=p := by
  cases p
  simp [multiply,natural]
@[simp] theorem one_multiply (p : Pair V) : multiply (natural (1:V)) p=p := by
  rw [multiply_comm,multiply_one]

theorem equivalent_multiply_right {p q : Pair V} (h : Equivalent p q) (r : Pair V) :
    Equivalent (multiply p r) (multiply q r) := by
  change p.1+q.2=p.2+q.1 at h
  change (p.1*r.1+p.2*r.2)+(q.1*r.2+q.2*r.1)=
    (p.1*r.2+p.2*r.1)+(q.1*r.1+q.2*r.2)
  calc
    _=(p.1+q.2)*r.1+(p.2+q.1)*r.2 := by ring
    _=(p.2+q.1)*r.1+(p.1+q.2)*r.2 := by simp only [h]
    _=_ := by ring
theorem equivalent_multiply {p q r s : Pair V}
    (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (multiply p r) (multiply q s) := by
  apply equivalent_trans (equivalent_multiply_right h r)
  rw [multiply_comm q r,multiply_comm q s]
  exact equivalent_multiply_right k q

@[simp] theorem magnitude_swap (p : Pair V) : magnitude (swap p)=magnitude p := by
  simp only [magnitude,swap,add_comm]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem multiply_swap_right (p q : Pair V) : multiply p (swap q)=swap (multiply p q) := rfl
theorem multiply_swap_left (p q : Pair V) : multiply (swap p) q=swap (multiply p q) := by
  apply Prod.ext <;> simp only [multiply,swap] <;> ring

theorem magnitude_of_add {a b c : V} (h : a=b+c) : magnitude (a,b)=c := by
  change (a-b)+(b-a)=c
  have hl : (b+c)-b=c := by rw [add_comm b c,add_tsub_cancel_right]
  have hr : b-(b+c)=0 := tsub_eq_zero_of_le (show b≤b+c by simp)
  simp only [h,hl,hr,add_zero]

private theorem magnitude_multiply_positive (p q : Pair V)
    (hp : p.2≤p.1) (hq : q.2≤q.1) :
    magnitude (multiply p q)=magnitude p*magnitude q := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  let u:=a-b
  let v:=c-d
  have hu : u+b=a := tsub_add_cancel_of_le hp
  have hv : v+d=c := tsub_add_cancel_of_le hq
  have ha : a=b+u := by rw [←hu]; ring
  have hc : c=d+v := by rw [←hv]; ring
  rw [magnitude_of_add ha,magnitude_of_add hc]
  apply magnitude_of_add
  change a*c+b*d=(a*d+b*c)+u*v
  rw [←hu,←hv]
  ring

/-- Multiplication of formal differences multiplies their natural magnitudes. -/
theorem magnitude_multiply (p q : Pair V) :
    magnitude (multiply p q)=magnitude p*magnitude q := by
  rcases le_total p.2 p.1 with hp|hp
  · rcases le_total q.2 q.1 with hq|hq
    · exact magnitude_multiply_positive p q hp hq
    · simpa only [multiply_swap_right,magnitude_swap] using
        magnitude_multiply_positive p (swap q) hp hq
  · rcases le_total q.2 q.1 with hq|hq
    · simpa only [multiply_swap_left,magnitude_swap] using
        magnitude_multiply_positive (swap p) q hp hq
    · simpa only [multiply_swap_left,multiply_swap_right,magnitude_swap] using
        magnitude_multiply_positive (swap p) (swap q) hp hq

private theorem factors_one {a b : V} (h : a*b=1) : a=1 ∧ b=1 := by
  have hp : 0<a := pos_of_mul_pos_left (by rw [h]; simp) (Arithmetic.zero_le b)
  have ha : a≤1 := le_of_dvd (by simp) ⟨b,h.symm⟩
  have he : a=1 := le_antisymm ha (pos_iff_one_le.mp hp)
  exact ⟨he,by simpa only [he,one_mul] using h⟩

/-- An actual signed product equal to one forces all five magnitudes to one. -/
theorem product5_magnitudes {p q r s t : Pair V}
    (h : Equivalent (product5 p q r s t) (natural (1:V))) :
    magnitude p=1 ∧ magnitude q=1 ∧ magnitude r=1 ∧ magnitude s=1 ∧ magnitude t=1 := by
  have hm := magnitude_of_add (equivalent_one.mp h)
  change magnitude (product5 p q r s t)=1 at hm
  simp only [product5,magnitude_multiply] at hm
  obtain ⟨hfour,ht⟩ := factors_one hm
  obtain ⟨hthree,hs⟩ := factors_one hfour
  obtain ⟨htwo,hr⟩ := factors_one hthree
  obtain ⟨hp,hq⟩ := factors_one htwo
  exact ⟨hp,hq,hr,hs,ht⟩

theorem positive_of_magnitude_one {p : Pair V} (h : magnitude p=1)
    (hn : p.1+1≠p.2) : Equivalent p (natural (1:V)) := by
  apply equivalent_one.mpr
  rcases le_total p.2 p.1 with hp|hp
  · have he : p.1=p.2+(p.1-p.2) := by rw [add_comm,tsub_add_cancel_of_le hp]
    have hm := magnitude_of_add he
    rw [h] at hm
    rwa [←hm] at he
  · have he : p.2=p.1+(p.2-p.1) := by rw [add_comm,tsub_add_cancel_of_le hp]
    have hm := magnitude_of_add he
    change magnitude (swap p)=p.2-p.1 at hm
    rw [magnitude_swap p,h] at hm
    exact (hn (by simpa only [←hm] using he.symm)).elim

/-- Four negative-unit exclusions force the remaining transport factor too. -/
theorem product5_positive {p q r s t : Pair V}
    (h : Equivalent (product5 p q r s t) (natural (1:V)))
    (hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2) :
    p.1=p.2+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧ s.1=s.2+1 ∧ t.1=t.2+1 := by
  obtain ⟨mp,mq,mr,_,mt⟩ := product5_magnitudes h
  have ep := positive_of_magnitude_one mp hp
  have eq := positive_of_magnitude_one mq hq
  have er := positive_of_magnitude_one mr hr
  have et := positive_of_magnitude_one mt ht
  have hs : Equivalent (product5 p q r s t) s := by
    simpa only [product5,one_multiply,multiply_one] using
      equivalent_multiply (equivalent_multiply
        (equivalent_multiply (equivalent_multiply ep eq) er) (equivalent_refl s)) et
  have es := equivalent_trans (equivalent_symm hs) h
  exact ⟨equivalent_one.mp ep,equivalent_one.mp eq,equivalent_one.mp er,
    equivalent_one.mp es,equivalent_one.mp et⟩

/-- Cancel the actual positive discriminant scale before extracting units. -/
theorem scaled_product5_positive (a : V) (ha : 0<a) {p q r s t : Pair V}
    (h : Equivalent (scale a (product5 p q r s t)) (natural a))
    (hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2) :
    p.1=p.2+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧ s.1=s.2+1 ∧ t.1=t.2+1 := by
  apply product5_positive (p:=p) (q:=q) (r:=r) (s:=s) (t:=t) _ hp hq hr ht
  apply equivalent_one.mpr
  apply (mul_left_cancel₀ (ne_of_gt ha))
  simpa only [Equivalent,scale,natural,add_zero,mul_add,mul_one] using h

end DiophantineConsistency.ArithmeticSignedPairs
