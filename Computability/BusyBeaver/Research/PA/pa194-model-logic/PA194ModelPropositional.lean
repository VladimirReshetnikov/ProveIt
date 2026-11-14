import PA194TargetLineSoundness
import M6.Logic.RestrictedImplication

/-!
# The implication basis of the numerical calculus, in models

`TargetProvable` is the provability predicate of the separate-diagonal numerical calculus
inside a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`. Its only
propositional axiom is the restricted row `rho8 a b c u` with the side condition `u ≤ a`.

The upstream derivation of the usual implicational theorems from that row,
`M6.Logic.RestrictedImplication`, is generic in the carrier, the implication and the proof
predicate. This file instantiates it with `M`, `impValue` and `TargetProvable`, so the
theorems hold for all elements of `M`, nonstandard formula codes included:

* `imp_k`, `imp_s`, `imp_peirce`, `imp_comp`, `imp_exchange`, `imp_refl`;
* `rho8_all`: the row without its side condition;
* `imp_trans`, `imp_lift`: derived rules.

No induction inside the model is used here; each theorem is a fixed finite derivation with
parameters in `M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem le_four_mul (x : M) : x ≤ 4 * x := by
  calc x = 1 * x := (one_mul x).symm
    _ ≤ 4 * x := mul_le_mul_of_nonneg_right (by norm_num) (by simp)

theorem le_impValue_left {u a : M} (b : M) (h : u ≤ a) : u ≤ impValue a b :=
  le_trans h (le_trans (components_le a b).1 (le_four_mul _))

theorem le_impValue_right {u b : M} (a : M) (h : u ≤ b) : u ≤ impValue a b :=
  le_trans h (le_trans (components_le a b).2 (le_four_mul _))

/-- Provability as data, for the generic rules. -/
abbrev TP (a : M) : Type := PLift (TargetProvable a)

/-- The restricted row and modus ponens of the calculus, in the model. -/
noncomputable def rules :
    M6.Logic.RestrictedImplication.Rules (impValue (M := M)) (· ≤ ·) (TP (M := M)) where
  mp := fun hab ha => ⟨PA194TargetVectorJoin.mp_closed _ _ ha.down hab.down⟩
  row := fun a b c u h => ⟨rho8_provable a b c u h⟩
  refl := fun a => le_refl a
  boundLeft := fun b h => le_impValue_left b h
  boundRight := fun a h => le_impValue_right a h

theorem tp_mp {a b : M} (ha : TargetProvable a) (hab : TargetProvable (impValue a b)) :
    TargetProvable b :=
  PA194TargetVectorJoin.mp_closed a b ha hab

theorem tp_gen (label : M) {a : M} (ha : TargetProvable a) : TargetProvable (allValue label a) :=
  PA194TargetGeneralize.generalize_closed label a ha

theorem imp_k (a b : M) : TargetProvable (impValue a (impValue b a)) :=
  (M6.Logic.RestrictedImplication.k rules a b).down

theorem imp_peirce (a b : M) : TargetProvable (impValue (impValue (impValue a b) a) a) :=
  (M6.Logic.RestrictedImplication.peirce rules a b).down

theorem imp_comp (a b c : M) :
    TargetProvable (impValue (impValue a b) (impValue (impValue b c) (impValue a c))) :=
  (M6.Logic.RestrictedImplication.composition rules a b c).down

theorem imp_exchange (a b c : M) :
    TargetProvable (impValue (impValue a (impValue b c)) (impValue b (impValue a c))) :=
  (M6.Logic.RestrictedImplication.exchange rules a b c).down

theorem imp_s (a b c : M) :
    TargetProvable (impValue (impValue a (impValue b c))
      (impValue (impValue a b) (impValue a c))) :=
  (M6.Logic.RestrictedImplication.s rules a b c).down

/-- The row for arbitrary `u`. -/
theorem rho8_all (a b c u : M) : TargetProvable (rho8Value a b c u) :=
  (M6.Logic.RestrictedImplication.rho8All rules a b c u).down

theorem imp_refl (a : M) : TargetProvable (impValue a a) :=
  tp_mp (imp_k a a) (tp_mp (imp_k a (impValue a a)) (imp_s a (impValue a a) a))

theorem imp_trans {a b c : M} (hab : TargetProvable (impValue a b))
    (hbc : TargetProvable (impValue b c)) : TargetProvable (impValue a c) :=
  tp_mp hbc (tp_mp hab (imp_comp a b c))

/-- From `a → b` to `(x → a) → (x → b)`. -/
theorem imp_lift {a b : M} (hab : TargetProvable (impValue a b)) (x : M) :
    TargetProvable (impValue (impValue x a) (impValue x b)) :=
  (M6.Logic.RestrictedImplication.liftRight rules ⟨hab⟩ x).down

/-- A provable formula follows from anything. -/
theorem imp_const {a : M} (ha : TargetProvable a) (x : M) : TargetProvable (impValue x a) :=
  tp_mp ha (imp_k a x)

#print axioms imp_k
#print axioms imp_s
#print axioms imp_peirce
#print axioms rho8_all
#print axioms imp_refl
end models
end PA194ModelLogic
