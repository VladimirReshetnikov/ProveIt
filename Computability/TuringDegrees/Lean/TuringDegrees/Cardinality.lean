import TuringDegrees.Representatives
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.DeriveEncodable

/-!
# Elementary cardinality results for set Turing degrees

For a fixed oracle there are only countably many oracle programs.  We expose
an explicit syntax for Mathlib's inductive definition of oracle recursion and
use it to prove the cardinality claims from the Turing-degree page:

* every degree contains countably many sets (combined with the explicit
  injection from `Representatives`, exactly countably infinitely many); and
* the lower cone below every degree is countable;
* the collection of all set Turing degrees has cardinality continuum; and
* both the nonstrict and strict upper cones above every degree have
  cardinality continuum.

The continuum lower bounds follow from the elementary countable-fiber
argument: quotient fibers are degree classes, and fibers of joining with a
fixed degree embed into a countable lower cone.
-/

noncomputable section

open scoped Computability

namespace TuringDegrees

open scoped SetTuring

/-- Finite syntax for a partial-recursive program with one distinguished
oracle.  Its constructors mirror `Nat.RecursiveIn` exactly. -/
inductive OracleProgram
  | zero
  | succ
  | left
  | right
  | oracle
  | pair (left right : OracleProgram)
  | comp (outer inner : OracleProgram)
  | prec (base step : OracleProgram)
  | rfind (body : OracleProgram)
  deriving Encodable

namespace OracleProgram

/-- Interpret a finite oracle program at a particular oracle. -/
def eval (oracle : ℕ →. ℕ) : OracleProgram → (ℕ →. ℕ)
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => oracle
  | .pair first second => fun n =>
      Nat.pair <$> eval oracle first n <*> eval oracle second n
  | .comp outer inner => fun n =>
      eval oracle inner n >>= eval oracle outer
  | .prec base step => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval oracle base a) fun y previous => do
        let value ← previous
        eval oracle step (Nat.pair a (Nat.pair y value))
  | .rfind body => fun a =>
      Nat.rfind fun n =>
        (fun value => value = 0) <$> eval oracle body (Nat.pair a n)

theorem eval_recursiveIn (oracle : ℕ →. ℕ) :
    ∀ program, Nat.RecursiveIn {oracle} (eval oracle program)
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .oracle => .oracle oracle (by simp)
  | .pair first second => .pair
      (eval_recursiveIn oracle first) (eval_recursiveIn oracle second)
  | .comp outer inner => .comp
      (eval_recursiveIn oracle outer) (eval_recursiveIn oracle inner)
  | .prec base step => .prec
      (eval_recursiveIn oracle base) (eval_recursiveIn oracle step)
  | .rfind body => .rfind (eval_recursiveIn oracle body)

/-- `OracleProgram` is complete for the singleton-oracle fragment of
`Nat.RecursiveIn`. -/
theorem exists_program {oracle f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {oracle} f) :
    ∃ program, eval oracle program = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g hg =>
      rw [Set.mem_singleton_iff.mp hg]
      exact ⟨.oracle, rfl⟩
  | pair hf hg ihf ihg =>
      obtain ⟨first, hfirst⟩ := ihf
      obtain ⟨second, hsecond⟩ := ihg
      exact ⟨.pair first second, by simp [eval, hfirst, hsecond]⟩
  | comp hf hg ihf ihg =>
      obtain ⟨outer, houter⟩ := ihf
      obtain ⟨inner, hinner⟩ := ihg
      exact ⟨.comp outer inner, by simp [eval, houter, hinner]⟩
  | prec hf hg ihf ihg =>
      obtain ⟨base, hbase⟩ := ihf
      obtain ⟨step, hstep⟩ := ihg
      exact ⟨.prec base step, by simp [eval, hbase, hstep]⟩
  | rfind hf ihf =>
      obtain ⟨body, hbody⟩ := ihf
      exact ⟨.rfind body, by simp [eval, hbody]⟩

instance recursiveIn_countable (oracle : ℕ →. ℕ) :
    Countable {f : ℕ →. ℕ // Nat.RecursiveIn {oracle} f} := by
  apply Function.Surjective.countable
    (f := fun program : OracleProgram =>
      ⟨eval oracle program, eval_recursiveIn oracle program⟩)
  rintro ⟨f, hf⟩
  obtain ⟨program, hprogram⟩ := exists_program hf
  exact ⟨program, Subtype.ext hprogram⟩

end OracleProgram

/-- Embed all sets reducible to `A` into the countable collection of programs
recursive in the characteristic oracle for `A`. -/
def lowerConeOracleEmbedding (A : Set ℕ) :
    {B : Set ℕ // B ≤ᵀₛ A} →
      {f : ℕ →. ℕ // Nat.RecursiveIn {characteristic A} f} :=
  fun B => ⟨characteristic B, RecursiveIn.iff_nat.mp B.property⟩

theorem lowerConeOracleEmbedding_injective (A : Set ℕ) :
    Function.Injective (lowerConeOracleEmbedding A) := by
  intro left right equality
  apply Subtype.ext
  apply characteristic_injective
  exact congrArg Subtype.val equality

instance lowerConeSets_countable (A : Set ℕ) :
    Countable {B : Set ℕ // B ≤ᵀₛ A} :=
  Function.Injective.countable (lowerConeOracleEmbedding_injective A)

def degreeClassEmbedding (A : Set ℕ) :
    {B : Set ℕ // SetTuringDegree.of B = SetTuringDegree.of A} →
      {B : Set ℕ // B ≤ᵀₛ A} :=
  fun B => ⟨B, (SetTuringDegree.of_eq_of.mp B.property).1⟩

theorem degreeClassEmbedding_injective (A : Set ℕ) :
    Function.Injective (degreeClassEmbedding A) := by
  intro left right equality
  apply Subtype.ext
  exact congrArg
    (fun value : {B : Set ℕ // B ≤ᵀₛ A} => value.1) equality

theorem degreeClass_countable (A : Set ℕ) :
    Countable {B : Set ℕ // SetTuringDegree.of B = SetTuringDegree.of A} :=
  Function.Injective.countable (degreeClassEmbedding_injective A)

/-- Every degree contains at most countably many sets. -/
theorem representatives_countable (degree : SetTuringDegree) :
    Countable {B : Set ℕ // SetTuringDegree.of B = degree} := by
  induction degree using SetTuringDegree.ind_on
  exact degreeClass_countable _

/-- Every degree contains infinitely many sets. -/
theorem representatives_infinite (degree : SetTuringDegree) :
    Infinite {B : Set ℕ // SetTuringDegree.of B = degree} := by
  obtain ⟨representatives, hinjective, hdegree⟩ :=
    infinitely_many_representatives degree
  apply Infinite.of_injective
    (fun tag =>
      (⟨representatives tag, hdegree tag⟩ :
        {B : Set ℕ // SetTuringDegree.of B = degree}))
  intro left right equality
  apply hinjective
  exact congrArg Subtype.val equality

/-- The page's statement that every Turing degree is countably infinite,
split into Lean's two standard cardinality classes. -/
theorem representatives_countably_infinite (degree : SetTuringDegree) :
    Countable {B : Set ℕ // SetTuringDegree.of B = degree} ∧
    Infinite {B : Set ℕ // SetTuringDegree.of B = degree} :=
  ⟨representatives_countable degree, representatives_infinite degree⟩

theorem cardinal_degreeClass (degree : SetTuringDegree) :
    Cardinal.mk {B : Set ℕ // SetTuringDegree.of B = degree} =
      Cardinal.aleph0 := by
  letI := representatives_countable degree
  letI := representatives_infinite degree
  exact Cardinal.mk_eq_aleph0 _

def lowerSetDegreeMap (A : Set ℕ) :
    {B : Set ℕ // B ≤ᵀₛ A} →
      {lower : SetTuringDegree // lower ≤ SetTuringDegree.of A} :=
  fun B => ⟨SetTuringDegree.of B, B.property⟩

theorem lowerSetDegreeMap_surjective (A : Set ℕ) :
    Function.Surjective (lowerSetDegreeMap A) := by
  rintro ⟨degree, hdegree⟩
  induction degree using SetTuringDegree.ind_on
  exact ⟨⟨_, hdegree⟩, rfl⟩

/-- The collection of degrees below any fixed degree is countable. -/
theorem lowerDegrees_countable (degree : SetTuringDegree) :
    Countable {lower : SetTuringDegree // lower ≤ degree} := by
  induction degree using SetTuringDegree.ind_on
  exact Function.Surjective.countable (lowerSetDegreeMap_surjective _)

private theorem continuum_le_of_le_mul_aleph0 {cardinal : Cardinal}
    (bound : Cardinal.continuum ≤ cardinal * Cardinal.aleph0) :
    Cardinal.continuum ≤ cardinal := by
  have productBound :
      cardinal * Cardinal.aleph0 ≤ max cardinal Cardinal.aleph0 := by
    simpa [max_assoc, max_self] using
      Cardinal.mul_le_max cardinal Cardinal.aleph0
  by_contra notLower
  have cardinalLt : cardinal < Cardinal.continuum :=
    lt_of_not_ge notLower
  have maxLt : max cardinal Cardinal.aleph0 < Cardinal.continuum :=
    max_lt cardinalLt Cardinal.aleph0_lt_continuum
  exact (not_lt_of_ge (bound.trans productBound)) maxLt

/-- There are continuum many set Turing degrees.  The upper bound is the
quotient map from `Set ℕ`; the lower bound follows because this map has only
countable fibers. -/
theorem cardinal_setTuringDegree :
    Cardinal.mk SetTuringDegree = Cardinal.continuum := by
  have fiberBound : ∀ degree : SetTuringDegree,
      Cardinal.mk (SetTuringDegree.of ⁻¹' ({degree} : Set SetTuringDegree)) ≤
        Cardinal.aleph0 := by
    intro degree
    change Cardinal.mk
      {A : Set ℕ // SetTuringDegree.of A = degree} ≤ Cardinal.aleph0
    exact Cardinal.mk_le_aleph0_iff.mpr
      (representatives_countable degree)
  have sourceBound :
      Cardinal.continuum ≤
        Cardinal.mk SetTuringDegree * Cardinal.aleph0 := by
    rw [← Cardinal.mk_set_nat]
    exact Cardinal.mk_le_mk_mul_of_mk_preimage_le
      SetTuringDegree.of fiberBound
  have lower : Cardinal.continuum ≤ Cardinal.mk SetTuringDegree :=
    continuum_le_of_le_mul_aleph0 sourceBound
  have upper : Cardinal.mk SetTuringDegree ≤ Cardinal.continuum := by
    rw [← Cardinal.mk_set_nat]
    exact Cardinal.mk_quotient_le
  exact upper.antisymm lower

/-- Join with `degree` maps every degree into its upper cone. -/
def upperJoinMap (degree other : SetTuringDegree) :
    {upper : SetTuringDegree // degree ≤ upper} :=
  ⟨degree ⊔ other, le_sup_left⟩

/-- Every (nonstrict) upper cone of the Turing degrees has continuum
cardinality.  Countability of the fibers of `other ↦ degree ⊔ other`
reduces this to the preceding total-cardinality theorem. -/
theorem cardinal_upperCone (degree : SetTuringDegree) :
    Cardinal.mk {upper : SetTuringDegree // degree ≤ upper} =
      Cardinal.continuum := by
  have fiberBound :
      ∀ upper : {upper : SetTuringDegree // degree ≤ upper},
        Cardinal.mk
          (upperJoinMap degree ⁻¹'
            ({upper} : Set {upper : SetTuringDegree // degree ≤ upper})) ≤
          Cardinal.aleph0 := by
    intro upper
    change Cardinal.mk
      {other : SetTuringDegree // upperJoinMap degree other = upper} ≤
        Cardinal.aleph0
    let embedding :
        {other : SetTuringDegree // upperJoinMap degree other = upper} →
          {lower : SetTuringDegree // lower ≤ upper.1} :=
      fun other => ⟨other.1, by
        have equality : degree ⊔ other.1 = upper.1 :=
          congrArg Subtype.val other.2
        exact le_sup_right.trans_eq equality⟩
    rw [Cardinal.mk_le_aleph0_iff]
    haveI := lowerDegrees_countable upper.1
    exact Function.Injective.countable (f := embedding) (by
      intro left right equality
      apply Subtype.ext
      exact congrArg
        (fun value : {lower : SetTuringDegree // lower ≤ upper.1} => value.1)
        equality)
  have sourceBound :
      Cardinal.continuum ≤
        Cardinal.mk {upper : SetTuringDegree // degree ≤ upper} *
          Cardinal.aleph0 := by
    rw [← cardinal_setTuringDegree]
    exact Cardinal.mk_le_mk_mul_of_mk_preimage_le
      (upperJoinMap degree) fiberBound
  have lower :
      Cardinal.continuum ≤
        Cardinal.mk {upper : SetTuringDegree // degree ≤ upper} :=
    continuum_le_of_le_mul_aleph0 sourceBound
  have upper :
      Cardinal.mk {upper : SetTuringDegree // degree ≤ upper} ≤
        Cardinal.continuum :=
    (Cardinal.mk_subtype_le _).trans_eq cardinal_setTuringDegree
  exact upper.antisymm lower

def baseInUpperCone (degree : SetTuringDegree) :
    {upper : SetTuringDegree // degree ≤ upper} :=
  ⟨degree, le_rfl⟩

/-- Removing the base point from the nonstrict upper cone gives precisely the
strict upper cone. -/
def upperConeWithoutBaseEquivStrict (degree : SetTuringDegree) :
    Set.compl ({baseInUpperCone degree} :
        Set {upper : SetTuringDegree // degree ≤ upper}) ≃
      {upper : SetTuringDegree // degree < upper} where
  toFun upper := ⟨upper.1.1, by
    have upperNeBase : upper.1 ≠ baseInUpperCone degree := by
      simpa only [Set.compl, Set.mem_singleton_iff, Set.mem_setOf_eq] using upper.2
    have degreeNeUpper : degree ≠ upper.1.1 := by
      intro equality
      apply upperNeBase
      apply Subtype.ext
      exact equality.symm
    exact lt_of_le_of_ne upper.1.2 degreeNeUpper⟩
  invFun upper := ⟨⟨upper.1, upper.2.le⟩, by
    simp only [Set.compl, Set.mem_singleton_iff]
    intro equality
    have valueEquality : upper.1 = degree := congrArg Subtype.val equality
    exact upper.2.ne valueEquality.symm⟩
  left_inv upper := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv upper := by
    apply Subtype.ext
    rfl

/-- The page states the upper-cone result strictly: there are continuum many
degrees greater than any fixed degree. -/
theorem cardinal_strictUpperCone (degree : SetTuringDegree) :
    Cardinal.mk {upper : SetTuringDegree // degree < upper} =
      Cardinal.continuum := by
  let UpperCone := {upper : SetTuringDegree // degree ≤ upper}
  let base : UpperCone := baseInUpperCone degree
  have upperCardinality : Cardinal.mk UpperCone = Cardinal.continuum :=
    cardinal_upperCone degree
  letI : Infinite UpperCone := Cardinal.aleph0_le_mk_iff.mp (by
    rw [upperCardinality]
    exact Cardinal.aleph0_le_continuum)
  have singletonLt : Cardinal.mk ({base} : Set UpperCone) <
      Cardinal.mk UpperCone := by
    rw [Cardinal.mk_singleton, upperCardinality]
    exact Cardinal.nat_lt_continuum 1
  calc
    Cardinal.mk {upper : SetTuringDegree // degree < upper} =
        Cardinal.mk (Set.compl ({base} : Set UpperCone)) := by
          exact (Cardinal.mk_congr
            (upperConeWithoutBaseEquivStrict degree)).symm
    _ = Cardinal.mk UpperCone :=
      Cardinal.mk_compl_of_infinite ({base} : Set UpperCone) singletonLt
    _ = Cardinal.continuum := upperCardinality

end TuringDegrees
