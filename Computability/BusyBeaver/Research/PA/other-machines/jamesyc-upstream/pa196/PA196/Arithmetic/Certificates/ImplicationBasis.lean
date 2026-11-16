module
public import M6PA.Theory
public import PA196.Arithmetic.Certificates.Leaves
public import M6.Logic.RestrictedImplication
@[expose] public section

/-! Interpret the restricted implication basis as verified numeric certificates over PA models. -/
open M6.PA
namespace PA196.Arithmetic.Certificates.Dominated
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.SourceCantorInternal Checker HeadGraphs
open PA196.Arithmetic.Certificates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Numeric data plus its verifier equation, never a Prop-extracted witness. -/
structure Certificate (a : V) where
  code : V
  accepted : verifyValue code = a+1

noncomputable abbrev wim (a b : V) : V := implicationValue a b
noncomputable abbrev rho8 (a b c u : V) : V :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c))

theorem refl (a : V) : a ≤ a := le_rfl

theorem implication_bound (x y : V) : pairValue x y ≤ wim x y := by
  change pairValue x y ≤ 4 * pairValue x y
  exact Arithmetic.le_mul_of_pos_left (by norm_num)

theorem le_l {u x : V} (y : V) (h : u ≤ x) : u ≤ wim x y :=
  le_trans h (le_trans (pairValue_bounds x y).1 (implication_bound x y))
theorem le_r {u y : V} (x : V) (h : u ≤ y) : u ≤ wim x y :=
  le_trans h (le_trans (pairValue_bounds x y).2 (implication_bound x y))

abbrev below (a b : V) : Prop := a ≤ b

variable [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def mp (a b : V) (major : Certificate (wim a b))
    (minor : Certificate a) : Certificate b :=
  ⟨mpCertificate b minor.code major.code,verify_mp _ _ _ _ minor.accepted major.accepted⟩
noncomputable def row (a b c u : V) (h : u ≤ a) : Certificate (rho8 a b c u) :=
  ⟨leafCertificate 8 (pack4Value a b c u),verify_r8 a b c u h⟩

noncomputable def rules :
    M6.Logic.RestrictedImplication.Rules (A := V) wim (· ≤ ·) Certificate where
  mp := fun {a b} => mp a b
  row := row
  refl := refl
  boundLeft := le_l
  boundRight := le_r

noncomputable def rho8_all (a b c u : V) :
    Certificate (rho8 a b c u) :=
  M6.Logic.RestrictedImplication.rho8All rules a b c u

noncomputable def composition (a b c : V) :
    Certificate (wim (wim a b) (wim (wim b c) (wim a c))) :=
  M6.Logic.RestrictedImplication.composition rules a b c

noncomputable def exchange (a b c : V) :
    Certificate (wim (wim a (wim b c)) (wim b (wim a c))) :=
  M6.Logic.RestrictedImplication.exchange rules a b c

noncomputable def k (a b : V) :
    Certificate (wim a (wim b a)) :=
  M6.Logic.RestrictedImplication.k rules a b

noncomputable def peirce (a b : V) :
    Certificate (wim (wim (wim a b) a) a) :=
  M6.Logic.RestrictedImplication.peirce rules a b

noncomputable def s (a b c : V) :
    Certificate (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  M6.Logic.RestrictedImplication.s rules a b c

noncomputable def lift_right (a b : V) (hab : Certificate (wim a b)) (x : V) :
    Certificate (wim (wim x a) (wim x b)) :=
  M6.Logic.RestrictedImplication.liftRight rules hab x

theorem k_accepted (a b : V) : verifyValue (k a b).code = wim a (wim b a)+1 :=
  (k a b).accepted

theorem s_accepted (a b c : V) : verifyValue (s a b c).code =
    wim (wim a (wim b c)) (wim (wim a b) (wim a c))+1 := (s a b c).accepted

theorem peirce_accepted (a b : V) : verifyValue (peirce a b).code =
    wim (wim (wim a b) a) a+1 := (peirce a b).accepted

theorem composition_accepted (a b c : V) : verifyValue (composition a b c).code =
    wim (wim a b) (wim (wim b c) (wim a c))+1 := (composition a b c).accepted

#print axioms k_accepted
#print axioms s_accepted
#print axioms peirce_accepted
#print axioms composition_accepted
#print axioms rho8_all
end PA196.Arithmetic.Certificates.Dominated
