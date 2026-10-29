import DiophantineConsistency.ArithmeticUnaryRecursion
import Mathlib.Tactic.Ring

/-! Total represented binary population at arbitrary internal lengths.
The prefixCount uses Foundation's actual bounded fbit, not an external finite sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinaryPopulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out a. out=0”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index a. ∃ bit, !fbitDef bit a index ∧ out=previous+bit”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ parameters index previous := previous+fbit (parameters 0) index
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]

noncomputable def prefixCount (n a : V) : V := construction.result ![a] n
def prefixDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def prefixDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance prefix_defined : 𝚺₁-Function₂[V] prefixCount via prefixDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction
instance prefix_defined_delta : 𝚫₁-Function₂[V] prefixCount via prefixDeltaDef := prefix_defined.graph_delta
instance prefix_definable : 𝚺₁-Function₂[V] prefixCount := prefix_defined.to_definable

@[simp] theorem prefix_zero (a : V) : prefixCount 0 a=0 := by simp [prefixCount,construction]
theorem prefix_succ (n a : V) : prefixCount (n+1) a=prefixCount n a+fbit a n := by
  simp [prefixCount,PR.Construction.result_succ,construction]

noncomputable def population (a : V) : V := prefixCount ‖a‖ a
def populationDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out a. ∃ n, !lengthDef n a ∧ !prefixDef out n a”
def populationDeltaDef : 𝚫₁.Semisentence 2 := populationDef.graphDelta
instance population_defined : 𝚺₁-Function₁[V] population via populationDef := .mk fun e => by
  simp [populationDef,population]
instance population_defined_delta : 𝚫₁-Function₁[V] population via populationDeltaDef :=
  population_defined.graph_delta
instance population_definable : 𝚺₁-Function₁[V] population := population_defined.to_definable

theorem prefix_total (n a : V) : ∃! out, prefixDef.val.Evalb ![out,n,a] := by simp
theorem population_total (a : V) : ∃! out, populationDef.val.Evalb ![out,a] := by simp

@[simp] theorem prefix_on_zero (n : V) : prefixCount n 0=0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [prefix_succ,ih,fbit_zero,add_zero]

theorem prefix_le (n a : V) : prefixCount n a≤n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [prefix_succ]
    exact add_le_add ih (fbit_le_one a n)

theorem prefix_stable (a n : V) (hn : ‖a‖≤n) (m : V) :
    prefixCount (n+m) a=prefixCount n a := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [←add_assoc,prefix_succ,ih,fbit_eq_zero_of_le (le_trans hn (by simp)),add_zero]

theorem prefix_eq_population (n a : V) (hn : ‖a‖≤n) : prefixCount n a=population a := by
  simpa only [add_tsub_self_of_le hn, population] using prefix_stable a ‖a‖ le_rfl (n-‖a‖)

theorem prefix_binary (n a : V) :
    prefixCount (n+1) (2*a)=prefixCount n a ∧
    prefixCount (n+1) (2*a+1)=prefixCount n a+1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    constructor
    · simpa only [zero_add,prefix_zero,fbit_two_mul_zero_eq_zero] using prefix_succ (0:V) (2*a)
    · simpa only [zero_add,prefix_zero,fbit_two_mul_add_one_zero_eq_one] using prefix_succ (0:V) (2*a+1)
  case succ n ih =>
    constructor
    · rw [prefix_succ,ih.1,fbit_mul_two_mul,prefix_succ]
    · rw [prefix_succ,ih.2,fbit_mul_two_add_one_mul,prefix_succ]
      ring

@[simp] theorem population_zero : population (0:V)=0 := by simp [population]
@[simp] theorem population_even (a : V) : population (2*a)=population a := by
  rcases Arithmetic.zero_le a with he|ha
  · rw [←he]
    simp
  · unfold population
    rw [length_two_mul_of_pos ha]
    exact (prefix_binary ‖a‖ a).1

@[simp] theorem population_odd (a : V) : population (2*a+1)=population a+1 := by
  unfold population
  rw [length_two_mul_add_one]
  exact (prefix_binary ‖a‖ a).2

theorem population_le (a : V) : population a≤‖a‖ ∧ ‖a‖≤a :=
  ⟨prefix_le ‖a‖ a,length_le a⟩

theorem population_binary (a r : V) (hr : r≤1) :
    population (2*a+r)=population a+r := by
  rcases le_one_iff_eq_zero_or_one.mp hr with rfl | rfl <;> simp

theorem population_div_mod (a : V) :
    population a=population (a/2)+a%2 := by
  have he : 2*(a/2)+a%2=a := div_add_mod a 2
  calc
    population a=population (2*(a/2)+a%2) := by rw [he]
    _=population (a/2)+a%2 := population_binary _ _ (lt_two_iff_le_one.mp (by simp))

theorem half_lt (a E : V) (h : a<2*E) : a/2<E := by
  apply div_lt_of_lt_mul
  simpa only [mul_comm] using h

/-- Internal block concatenation, including zero length and zero high block. -/
theorem concatenate (A n b : V) (hb : b<Exp.exp n) :
    population (A*Exp.exp n+b)=population A+population b := by
  have all (n : V) : ∀ b<Exp.exp n,
      population (A*Exp.exp n+b)=population A+population b := by
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro b hb
      have hz : b=0 := le_antisymm (by simpa using lt_iff_succ_le.mp hb) (Arithmetic.zero_le b)
      simp [hz]
    case succ n ih =>
      intro b hb
      have hq : b/2<Exp.exp n := half_lt b _ (by simpa only [exp_succ] using hb)
      have hd : 2*(b/2)+b%2=b := div_add_mod b 2
      have he : A*Exp.exp (n+1)+b=2*(A*Exp.exp n+b/2)+b%2 := by
        calc
          _=A*(2*Exp.exp n)+(2*(b/2)+b%2) := by rw [exp_succ,hd]
          _=_ := by ring
      rw [he,population_binary _ _ (lt_two_iff_le_one.mp (by simp)),ih _ hq,population_div_mod b]
      ring
  exact all n b hb

/-- Internal complement weight, with every subtraction justified by the bound. -/
theorem complement (n a : V) (ha : a<Exp.exp n) :
    population a+population (Exp.exp n-1-a)=n := by
  have all (n : V) : ∀ a<Exp.exp n,
      population a+population (Exp.exp n-1-a)=n := by
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro a ha
      have hz : a=0 := le_antisymm (by simpa using lt_iff_succ_le.mp ha) (Arithmetic.zero_le a)
      simp [hz]
    case succ n ih =>
      intro a ha
      let E:=Exp.exp n
      let q:=a/2
      let r:=a%2
      let s:=E-(q+1)
      have hq : q<E := half_lt a E (by simpa only [exp_succ] using ha)
      have hq1 : q+1≤E := lt_iff_succ_le.mp hq
      have hr : r≤1 := lt_two_iff_le_one.mp (by dsimp [r]; simp)
      have hd : 2*q+r=a := div_add_mod a 2
      have hs : s+q+1=E := by
        change (E-(q+1))+q+1=E
        rw [add_assoc,tsub_add_cancel_of_le hq1]
      have hsdef : E-1-q=s := by
        dsimp [s]
        rw [Arithmetic.sub_sub]
        congr 1
        ring
      have hsum : (1-r)+r=1 := tsub_add_cancel_of_le hr
      have hcandidate : (2*s+(1-r))+(a+1)=Exp.exp (n+1) := by
        calc
          _=2*(s+q)+((1-r)+r)+1 := by rw [←hd]; ring
          _=2*(s+q+1) := by rw [hsum]; ring
          _=2*E := by rw [hs]
          _=Exp.exp (n+1) := (exp_succ n).symm
      have hcomp : Exp.exp (n+1)-1-a=2*s+(1-r) := by
        calc
          _=Exp.exp (n+1)-(a+1) := by rw [Arithmetic.sub_sub]; congr 1; ring
          _=((2*s+(1-r))+(a+1))-(a+1) := by rw [hcandidate]
          _=_ := by simp
      have hind := ih q hq
      change population q+population (E-1-q)=n at hind
      rw [hsdef] at hind
      rw [population_div_mod a,hcomp,population_binary _ _ (tsub_le_self : 1-r≤1)]
      change (population q+r)+(population s+(1-r))=n+1
      calc
        _=(population q+population s)+((1-r)+r) := by ring
        _=n+1 := by rw [hind,hsum]
  exact all n a ha

@[simp] theorem population_one : population (1:V)=1 := by
  simpa only [mul_zero,zero_add,population_zero] using population_odd (0:V)

@[simp] theorem population_exp (n : V) : population (Exp.exp n)=1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [exp_succ,population_even,ih]

theorem population_exp_sub_one (n : V) : population (Exp.exp n-1)=n := by
  simpa using complement n (0:V) (exp_pos n)

end DiophantineConsistency.ArithmeticBinaryPopulation
