import PA194ModelPropositional
import PA194SourceOutputWF

/-!
# The numerical calculus for an arbitrary closed set of codes

`pa194-model-logic` derives the propositional and quantifier laws of the numerical calculus
for the predicate `TargetProvable`. The derivations use only that the provable codes are
closed under modus ponens and generalization and contain the restricted row and three heads.
This file states them for an arbitrary predicate `P` on a candidate-PRA model `M` whose
arithmetic reduct satisfies `𝗜𝚺₁`:

* `Closed P`: `P` is closed under modus ponens and generalization and contains the restricted
  row `ρ₈` (under its side condition), the first head `(∃x_D ∀x_D H) → H`, the second head
  (commutation of two universal quantifiers) and the sixth head (distribution);
* `Closed.k`, `s`, `peirce`, `comp`, `exchange`: the implication basis, by the generic
  derivation `M6.Logic.RestrictedImplication`;
* `Ctx`, `Ctx.deduction`: proofs from hypotheses and the deduction theorem;
* `explosion`, `dne`, `contraposition`, `negImpLeft`, `negImpRight`;
* `negationVacuity`, `implicationVacuity`, `universalVacuity`: vacuity at a label is
  inherited by negations, implications and universal formulas.

The main statement is `vacuity`: if `P` is `Σ₁`-definable and contains the vacuity of the
two kinds of atoms at every label different from their two labels (`AtomVac P`), then

```lean
theorem vacuity (C : Closed P) (hP : 𝚺₁-Predicate P) (A : AtomVac P) (c B : M) (h : B ≤ c) :
    P (impValue B (allValue c B))
```

for every code `B`, standard or not, by `Σ₁` order induction on `B`: the components of a
code are smaller than the code, and the labels of an atom below `c` differ from `c`. At
`c = B` this is the diagonal `Γ(B) = B → U(B, B)` (`diagonal`). So a calculus with atom
vacuity proves every diagonal instance.

The predicates of interest are `TargetProvable` and the sets of formulas that the command
words of a scheduler compute (`ConPA.Ctl.G`).
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace ConPA.Calc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetLeaves PA194TargetGate
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

/-- A set of codes closed under the two rules of the numerical calculus that contains the
restricted row and the first, second and sixth heads. -/
structure Closed (P : M → Prop) : Prop where
  mp : ∀ a b : M, P a → P (impValue a b) → P b
  gen : ∀ x a : M, P a → P (allValue x a)
  row : ∀ a b c u : M, u ≤ a → P (rho8Value a b c u)
  h1 : ∀ d h : M, P (head1Value d h)
  h2 : ∀ d a h : M, P (head2Value d a h)
  h6 : ∀ d a h : M, P (head6Value d a h)

/-- Vacuity of the membership and equality atoms at a label different from their labels. -/
structure AtomVac (P : M → Prop) : Prop where
  mem : ∀ a b c : M, c ≠ a → c ≠ b → P (impValue (memValue a b) (allValue c (memValue a b)))
  eq : ∀ a b c : M, c ≠ a → c ≠ b → P (impValue (eqValue a b) (allValue c (eqValue a b)))

variable {P : M → Prop}

/-! ## The implication basis -/

/-- The restricted row and modus ponens as data, for the generic derivation. -/
noncomputable def Closed.rules (C : Closed P) :
    M6.Logic.RestrictedImplication.Rules (impValue (M := M)) (· ≤ ·) (fun r => PLift (P r)) where
  mp := fun hab ha => ⟨C.mp _ _ ha.down hab.down⟩
  row := fun a b c u h => ⟨C.row a b c u h⟩
  refl := fun a => le_refl a
  boundLeft := fun b h => PA194ModelLogic.le_impValue_left b h
  boundRight := fun a h => PA194ModelLogic.le_impValue_right a h

theorem Closed.k (C : Closed P) (a b : M) : P (impValue a (impValue b a)) :=
  (M6.Logic.RestrictedImplication.k C.rules a b).down

theorem Closed.s (C : Closed P) (a b c : M) :
    P (impValue (impValue a (impValue b c)) (impValue (impValue a b) (impValue a c))) :=
  (M6.Logic.RestrictedImplication.s C.rules a b c).down

theorem Closed.peirce (C : Closed P) (a b : M) :
    P (impValue (impValue (impValue a b) a) a) :=
  (M6.Logic.RestrictedImplication.peirce C.rules a b).down

theorem Closed.comp (C : Closed P) (a b c : M) :
    P (impValue (impValue a b) (impValue (impValue b c) (impValue a c))) :=
  (M6.Logic.RestrictedImplication.composition C.rules a b c).down

theorem Closed.exchange (C : Closed P) (a b c : M) :
    P (impValue (impValue a (impValue b c)) (impValue b (impValue a c))) :=
  (M6.Logic.RestrictedImplication.exchange C.rules a b c).down

theorem Closed.refl (C : Closed P) (a : M) : P (impValue a a) :=
  C.mp _ _ (C.k a a) (C.mp _ _ (C.k a (impValue a a)) (C.s a (impValue a a) a))

theorem Closed.trans (C : Closed P) {a b c : M} (hab : P (impValue a b))
    (hbc : P (impValue b c)) : P (impValue a c) :=
  C.mp _ _ hbc (C.mp _ _ hab (C.comp a b c))

/-- The truth code `0` is the restricted row at zero arguments. -/
theorem Closed.zero (C : Closed P) : P (0 : M) := by
  have h := C.row (0 : M) 0 0 0 (le_refl 0)
  simpa [rho8Value, impValue, cantor, triangle] using h

/-- Distribution of a universal quantifier over an implication. -/
theorem Closed.r2 (C : Closed P) (d a h : M) :
    P (impValue (allValue d (impValue a h)) (impValue (allValue d a) (allValue d h))) :=
  C.mp _ _ (C.h6 d a h)
    (C.exchange (allValue d a) (allValue d (impValue a h)) (allValue d h))

theorem Closed.r4 (C : Closed P) (d a h : M) :
    P (impValue (allValue d (allValue a h)) (allValue a (allValue d h))) :=
  C.h2 d a h

theorem Closed.r6 (C : Closed P) (d h : M) : P (impValue (exValue d (allValue d h)) h) :=
  C.h1 d h

/-! ## Contexts -/

/-- Proof trees from the hypotheses `Γ`. -/
inductive Ctx (P : M → Prop) (Γ : List M) : M → Type where
  | assumption {a : M} : a ∈ Γ → Ctx P Γ a
  | closed {a : M} : P a → Ctx P Γ a
  | mp {a b : M} : Ctx P Γ a → Ctx P Γ (impValue a b) → Ctx P Γ b

noncomputable def Ctx.cut {Γ Δ : List M} {a : M} (d : Ctx P Γ a)
    (subst : ∀ b, b ∈ Γ → Ctx P Δ b) : Ctx P Δ a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => .closed p
  | .mp p q => .mp (p.cut subst) (q.cut subst)

theorem Ctx.close (C : Closed P) {Γ : List M} {a : M} (d : Ctx P Γ a)
    (subst : ∀ b, b ∈ Γ → P b) : P a := by
  induction d with
  | assumption h => exact subst _ h
  | closed p => exact p
  | mp _ _ ihp ihq => exact C.mp _ _ ihp ihq

theorem Ctx.empty (C : Closed P) {a : M} (d : Ctx P ([] : List M) a) : P a :=
  Ctx.close C d (fun _ h => False.elim (List.not_mem_nil h))

noncomputable def Ctx.lift (C : Closed P) {Γ : List M} {a : M} (d : Ctx P Γ a) (h : M) :
    Ctx P Γ (impValue h a) := .mp d (.closed (C.k a h))

open Classical in
noncomputable def Ctx.deduction (C : Closed P) {Γ : List M} {h a : M}
    (d : Ctx P (h :: Γ) a) : Ctx P Γ (impValue h a) :=
  match d with
  | .assumption ha =>
    if e : a = h then (by subst e; exact Ctx.closed (C.refl _))
    else Ctx.lift C (Ctx.assumption ((List.mem_cons.mp ha).resolve_left e)) h
  | .closed p => Ctx.lift C (Ctx.closed p) h
  | .mp (a := b) p q =>
    .mp (Ctx.deduction C p) (.mp (Ctx.deduction C q) (.closed (C.s h b a)))

noncomputable def Ctx.up {Γ : List M} {a : M} (p : Ctx P Γ a) (h : M) : Ctx P (h :: Γ) a :=
  p.cut (fun _ hb => .assumption (List.mem_cons_of_mem h hb))

/-- From the contradiction code `1` everything follows. -/
noncomputable def Ctx.explosion (C : Closed P) {Γ : List M} (a : M) (d : Ctx P Γ (1 : M)) :
    Ctx P Γ a :=
  .mp (.mp d (.closed (C.k 1 (allValue 0 (negValue (allValue 0 a)))))) (.closed (C.r6 0 a))

theorem explosion (C : Closed P) (a : M) : P (impValue 1 a) :=
  Ctx.empty C (Ctx.deduction C
    (Ctx.explosion C a (Ctx.assumption (Γ := [(1 : M)]) (by simp) : Ctx P [(1 : M)] 1)))

theorem doubleNegationElimination (C : Closed P) (a : M) :
    P (impValue (negValue (negValue a)) a) := by
  let p : Ctx P [negValue a, negValue (negValue a)] (negValue a) := .assumption (by simp)
  let q : Ctx P [negValue a, negValue (negValue a)] (negValue (negValue a)) :=
    .assumption (by simp)
  let contradiction : Ctx P [negValue a, negValue (negValue a)] (1 : M) := .mp p q
  let conditional : Ctx P [negValue (negValue a)] (impValue (negValue a) a) :=
    Ctx.deduction C (Ctx.explosion C a contradiction)
  exact Ctx.empty C (Ctx.deduction C (Ctx.mp conditional (.closed (C.peirce a 1))))

noncomputable def Ctx.dne (C : Closed P) {Γ : List M} {a : M}
    (p : Ctx P Γ (negValue (negValue a))) : Ctx P Γ a :=
  .mp p (.closed (doubleNegationElimination C a))

theorem contraposition (C : Closed P) (a b : M) :
    P (impValue (impValue a b) (impValue (negValue b) (negValue a))) := by
  let pa : Ctx P [a, negValue b, impValue a b] a := .assumption (by simp)
  let pab : Ctx P [a, negValue b, impValue a b] (impValue a b) := .assumption (by simp)
  let pnb : Ctx P [a, negValue b, impValue a b] (negValue b) := .assumption (by simp)
  exact Ctx.empty C (Ctx.deduction C (Ctx.deduction C (Ctx.deduction C
    (Ctx.mp (.mp pa pab) pnb))))

theorem contrapose (C : Closed P) {a b : M} (p : P (impValue a b)) :
    P (impValue (negValue b) (negValue a)) :=
  C.mp _ _ p (contraposition C a b)

/-- From `¬(a → b)`: `a`. -/
theorem negImpLeft (C : Closed P) {a b : M} (g : P (negValue (impValue a b))) : P a := by
  let ha : Ctx P [a, negValue a] a := .assumption (by simp)
  let hn : Ctx P [a, negValue a] (negValue a) := .assumption (by simp)
  let hi : Ctx P [negValue a] (impValue a b) :=
    Ctx.deduction C (Ctx.explosion C b (Ctx.mp ha hn))
  exact Ctx.empty C (Ctx.dne C (Ctx.deduction C (Ctx.mp hi (.closed g))))

/-- From `¬(a → b)`: `¬b`. -/
theorem negImpRight (C : Closed P) {a b : M} (g : P (negValue (impValue a b))) :
    P (negValue b) := by
  let hb : Ctx P [b] b := .assumption (by simp)
  exact Ctx.empty C (Ctx.deduction C (Ctx.mp (Ctx.lift C hb a) (.closed g)))

/-- From `a` and `¬b`: `¬(a → b)`. -/
theorem negImpIntro (C : Closed P) {a b : M} (ha : P a) (hb : P (negValue b)) :
    P (negValue (impValue a b)) := by
  let hi : Ctx P [impValue a b] (impValue a b) := .assumption (by simp)
  exact Ctx.empty C (Ctx.deduction C (Ctx.mp (Ctx.mp (.closed ha) hi) (.closed hb)))

/-! ## Vacuity -/

theorem negationVacuity (C : Closed P) (x a : M) (hv : P (impValue a (allValue x a))) :
    P (impValue (negValue a) (allValue x (negValue a))) := by
  have hc := contrapose C hv
  have hg := C.gen x _ hc
  have hl := C.mp _ _ hg (C.r2 x (negValue (allValue x a)) (negValue a))
  have hr := contrapose C (C.r6 x a)
  have hf := C.trans hr (doubleNegationElimination C (allValue x (negValue (allValue x a))))
  exact C.trans hf hl

noncomputable def Ctx.casesOnFormula (C : Closed P) {Γ : List M} (a : M) {c : M}
    (p : Ctx P (a :: Γ) c) (q : Ctx P (negValue a :: Γ) c) : Ctx P Γ c := by
  let hn : Ctx P (negValue c :: Γ) (negValue c) := .assumption (by simp)
  let hp : Ctx P (negValue c :: Γ) (impValue a c) := (Ctx.deduction C p).up (negValue c)
  let hna : Ctx P (negValue c :: Γ) (negValue a) :=
    .mp hn (.mp hp (.closed (contraposition C a c)))
  let hc : Ctx P (negValue c :: Γ) c := .mp hna ((Ctx.deduction C q).up (negValue c))
  exact Ctx.dne C (Ctx.deduction C (Ctx.mp hc hn))

theorem implicationVacuity (C : Closed P) (x a b : M)
    (ha : P (impValue a (allValue x a))) (hb : P (impValue b (allValue x b))) :
    P (impValue (impValue a b) (allValue x (impValue a b))) := by
  have hbLift : P (impValue b (allValue x (impValue a b))) :=
    C.trans hb (C.mp _ _ (C.gen x _ (C.k b a)) (C.r2 x b (impValue a b)))
  let hn : Ctx P [a, negValue a] (negValue a) := .assumption (by simp)
  let hp : Ctx P [a, negValue a] a := .assumption (by simp)
  have hnot : P (impValue (negValue a) (impValue a b)) :=
    Ctx.empty C (Ctx.deduction C (Ctx.deduction C (Ctx.explosion C b (Ctx.mp hp hn))))
  have haLift : P (impValue (negValue a) (allValue x (impValue a b))) :=
    C.trans (negationVacuity C x a ha)
      (C.mp _ _ (C.gen x _ hnot) (C.r2 x (negValue a) (impValue a b)))
  let pa : Ctx P [a, impValue a b] a := .assumption (by simp)
  let pab : Ctx P [a, impValue a b] (impValue a b) := .assumption (by simp)
  let pc : Ctx P [a, impValue a b] (allValue x (impValue a b)) :=
    .mp (.mp pa pab) (.closed hbLift)
  let pna : Ctx P [negValue a, impValue a b] (negValue a) := .assumption (by simp)
  let pnc : Ctx P [negValue a, impValue a b] (allValue x (impValue a b)) :=
    .mp pna (.closed haLift)
  exact Ctx.empty C (Ctx.deduction C (Ctx.casesOnFormula C a pc pnc))

theorem universalVacuity (C : Closed P) (x y a : M) (h : P (impValue a (allValue x a))) :
    P (impValue (allValue y a) (allValue x (allValue y a))) :=
  C.trans (C.mp _ _ (C.gen y _ h) (C.r2 y a (allValue x a))) (C.r4 y x a)

/-! ## Vacuity of every code at a label above it -/

local instance cantorDefinable (ℌ : HierarchySymbol) : ℌ-Function₂ (cantor : M → M → M) :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.cantor_defined (V := M)).to_definable.of_zero

theorem components_lt_tag (a b k : M) (hk : 0 < k) :
    a < 4 * cantor a b + k ∧ b < 4 * cantor a b + k := by
  have ht : cantor a b ≤ 4 * cantor a b := PA194ModelLogic.le_four_mul _
  have hp : 4 * cantor a b < 4 * cantor a b + k := lt_add_of_pos_right _ hk
  exact ⟨lt_of_le_of_lt (le_trans (components_le a b).1 ht) hp,
    lt_of_le_of_lt (le_trans (components_le a b).2 ht) hp⟩

/-- Every code is vacuous at every label that is not below it. -/
theorem vacuity (C : Closed P) (hP : 𝚺₁-Predicate P) (A : AtomVac P) (c B : M) (h : B ≤ c) :
    P (impValue B (allValue c B)) := by
  haveI := hP
  have hdef : 𝚺₁-Predicate
      (fun B : M => B ≤ c → P (4 * cantor B (4 * cantor B c + 2))) := by
    definability
  suffices key : ∀ B : M, B ≤ c → P (4 * cantor B (4 * cantor B c + 2)) from key B h
  intro B
  refine ISigma1.sigma1_order_induction hdef ?_ B
  intro x ih hx
  obtain ⟨a, b, h | h | h | h⟩ := PA194SourceOutputWF.source_cases x
  · rw [h] at ih hx ⊢
    by_cases hz : 4 * cantor a b = 0
    · rw [hz]
      exact C.mp _ _ (C.gen c 0 C.zero) (C.k (allValue c 0) 0)
    · have ha := (PA194SourceOutputWF.components_lt_imp a b hz).1
      have hb := (PA194SourceOutputWF.components_lt_imp a b hz).2
      exact implicationVacuity C c a b (ih a ha (le_trans (le_of_lt ha) hx))
        (ih b hb (le_trans (le_of_lt hb) hx))
  · rw [h] at hx ⊢
    have hs := components_lt_tag a b 1 (by norm_num)
    exact A.mem a b c (ne_of_gt (lt_of_lt_of_le hs.1 hx)) (ne_of_gt (lt_of_lt_of_le hs.2 hx))
  · rw [h] at ih hx ⊢
    have hs := PA194SourceOutputWF.first_lt_universal a b
    exact universalVacuity C c b a (ih a hs (le_trans (le_of_lt hs) hx))
  · rw [h] at hx ⊢
    have hs := components_lt_tag a b 3 (by norm_num)
    exact A.eq a b c (ne_of_gt (lt_of_lt_of_le hs.1 hx)) (ne_of_gt (lt_of_lt_of_le hs.2 hx))

/-- The diagonal `Γ(B) = B → U(B, B)` of every code. -/
theorem diagonal (C : Closed P) (hP : 𝚺₁-Predicate P) (A : AtomVac P) (B : M) :
    P (diagonalValue B) :=
  vacuity C hP A B B (le_refl B)

#print axioms Ctx.deduction
#print axioms explosion
#print axioms implicationVacuity
#print axioms vacuity
#print axioms diagonal
end models
end ConPA.Calc
