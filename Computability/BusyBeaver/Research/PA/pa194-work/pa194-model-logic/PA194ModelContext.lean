import PA194ModelPropositional

/-!
# Finite-context proofs in the numerical calculus, in models

The context machinery of `pa194-reverse-rewrite` (`PA194LogicDeduction`,
`PA194LogicConnectives`, `PA194LogicVacuity`), with natural numbers replaced by the elements
of a candidate-PRA model `M` with an IΣ₁ reduct and the derivation type replaced by
`TargetProvable`.

A context `Γ : List M` is a list of standard length whose entries are arbitrary model
elements, and `Ctx Γ a` is a proof tree of standard size from the hypotheses `Γ`, the
closed theorems of the calculus and modus ponens. The deduction theorem `Ctx.deduction` and
the derived rules are recursions on such trees, so no induction inside the model occurs.

Closed consequences: `explosion`, `dne`, `contraposition`, `negationVacuity`,
`implicationVacuity`, `universalVacuity`, `conjunctionVacuity`, `existentialMonotonicity`,
`liftImp`, and the membership rewriting rules `memRight`, `memLeft`.
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

/-! ## The quantifier and equality heads -/

/-- Distribution of a universal quantifier over an implication. -/
theorem r2 (d a h : M) :
    TargetProvable (impValue (allValue d (impValue a h))
      (impValue (allValue d a) (allValue d h))) :=
  tp_mp (head6_provable d a h) (imp_exchange (allValue d a) (allValue d (impValue a h)) (allValue d h))

theorem r4 (d a h : M) :
    TargetProvable (impValue (allValue d (allValue a h)) (allValue a (allValue d h))) :=
  head2_provable d a h

theorem r6 (d h : M) : TargetProvable (impValue (exValue d (allValue d h)) h) := by
  have h1 := head1_provable d h
  rw [machineHead1_model] at h1
  exact h1

theorem r1 (d h : M) : TargetProvable (exValue d (eqValue h d)) := head5_provable d h

theorem memRight (a b c : M) :
    TargetProvable (impValue (eqValue a b) (impValue (memValue c a) (memValue c b))) :=
  head4_provable b c a

theorem memLeft (a b c : M) :
    TargetProvable (impValue (eqValue a b) (impValue (memValue a c) (memValue b c))) :=
  tp_mp (head3_provable c b a) (imp_exchange (memValue a c) (eqValue a b) (memValue b c))

/-! ## Contexts -/

/-- Proof trees from the hypotheses `Γ`. -/
inductive Ctx (Γ : List M) : M → Type where
  | assumption {a : M} : a ∈ Γ → Ctx Γ a
  | closed {a : M} : TargetProvable a → Ctx Γ a
  | mp {a b : M} : Ctx Γ a → Ctx Γ (impValue a b) → Ctx Γ b

noncomputable def Ctx.cut {Γ Δ : List M} {a : M} (d : Ctx Γ a)
    (subst : ∀ b, b ∈ Γ → Ctx Δ b) : Ctx Δ a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => .closed p
  | .mp p q => .mp (p.cut subst) (q.cut subst)

theorem Ctx.close {Γ : List M} {a : M} (d : Ctx Γ a)
    (subst : ∀ b, b ∈ Γ → TargetProvable b) : TargetProvable a := by
  induction d with
  | assumption h => exact subst _ h
  | closed p => exact p
  | mp _ _ ihp ihq => exact tp_mp ihp ihq

theorem Ctx.empty {a : M} (d : Ctx ([] : List M) a) : TargetProvable a :=
  d.close (fun _ h => False.elim (List.not_mem_nil h))

noncomputable def Ctx.lift {Γ : List M} {a : M} (d : Ctx Γ a) (h : M) :
    Ctx Γ (impValue h a) := .mp d (.closed (imp_k a h))

open Classical in
noncomputable def Ctx.deduction {Γ : List M} {h a : M} (d : Ctx (h :: Γ) a) :
    Ctx Γ (impValue h a) :=
  match d with
  | .assumption ha =>
    if e : a = h then (by subst e; exact Ctx.closed (imp_refl _))
    else (Ctx.assumption ((List.mem_cons.mp ha).resolve_left e)).lift h
  | .closed p => (Ctx.closed p).lift h
  | .mp (a := b) p q => .mp p.deduction (.mp q.deduction (.closed (imp_s h b a)))

noncomputable def Ctx.up {Γ : List M} {a : M} (p : Ctx Γ a) (h : M) : Ctx (h :: Γ) a :=
  p.cut (fun _ hb => .assumption (List.mem_cons_of_mem h hb))

/-- From the contradiction code `1` everything follows. -/
noncomputable def Ctx.explosion {Γ : List M} (a : M) (d : Ctx Γ (1 : M)) : Ctx Γ a :=
  .mp (.mp d (.closed (imp_k 1 (allValue 0 (negValue (allValue 0 a)))))) (.closed (r6 0 a))

theorem explosion (a : M) : TargetProvable (impValue 1 a) :=
  ((Ctx.assumption (Γ := [(1 : M)]) (by simp) : Ctx [(1 : M)] 1).explosion a).deduction.empty

theorem doubleNegationElimination (a : M) :
    TargetProvable (impValue (negValue (negValue a)) a) := by
  let p : Ctx [negValue a, negValue (negValue a)] (negValue a) := .assumption (by simp)
  let q : Ctx [negValue a, negValue (negValue a)] (negValue (negValue a)) :=
    .assumption (by simp)
  let contradiction : Ctx [negValue a, negValue (negValue a)] (1 : M) := .mp p q
  let conditional : Ctx [negValue (negValue a)] (impValue (negValue a) a) :=
    (contradiction.explosion a).deduction
  exact (Ctx.mp conditional (.closed (imp_peirce a 1))).deduction.empty

noncomputable def Ctx.dne {Γ : List M} {a : M} (p : Ctx Γ (negValue (negValue a))) : Ctx Γ a :=
  .mp p (.closed (doubleNegationElimination a))

noncomputable def Ctx.andIntro {Γ : List M} {a b : M} (p : Ctx Γ a) (q : Ctx Γ b) :
    Ctx Γ (conjValue a b) :=
  (Ctx.mp (q.up (impValue a (negValue b)))
    (.mp (p.up (impValue a (negValue b)))
      (Ctx.assumption List.mem_cons_self :
        Ctx (impValue a (negValue b) :: Γ) (impValue a (negValue b))))).deduction

noncomputable def Ctx.andLeft {Γ : List M} {a b : M} (p : Ctx Γ (conjValue a b)) : Ctx Γ a := by
  let ha : Ctx (a :: negValue a :: Γ) a := .assumption (by simp)
  let hn : Ctx (a :: negValue a :: Γ) (negValue a) := .assumption (by simp)
  let arrow : Ctx (negValue a :: Γ) (impValue a (negValue b)) :=
    ((Ctx.mp ha hn).explosion (negValue b)).deduction
  exact (Ctx.mp arrow (p.up (negValue a))).deduction.dne

noncomputable def Ctx.andRight {Γ : List M} {a b : M} (p : Ctx Γ (conjValue a b)) : Ctx Γ b := by
  let hn : Ctx (negValue b :: Γ) (negValue b) := .assumption (by simp)
  exact (Ctx.mp (hn.lift a) (p.up (negValue b))).deduction.dne

theorem contraposition (a b : M) :
    TargetProvable (impValue (impValue a b) (impValue (negValue b) (negValue a))) := by
  let pa : Ctx [a, negValue b, impValue a b] a := .assumption (by simp)
  let pab : Ctx [a, negValue b, impValue a b] (impValue a b) := .assumption (by simp)
  let pnb : Ctx [a, negValue b, impValue a b] (negValue b) := .assumption (by simp)
  exact (Ctx.mp (.mp pa pab) pnb).deduction.deduction.deduction.empty

theorem contrapose {a b : M} (p : TargetProvable (impValue a b)) :
    TargetProvable (impValue (negValue b) (negValue a)) :=
  tp_mp p (contraposition a b)

noncomputable def Ctx.forallMP {Γ : List M} (x : M) {a b : M}
    (p : Ctx Γ (allValue x a)) (q : Ctx Γ (allValue x (impValue a b))) : Ctx Γ (allValue x b) :=
  .mp p (.mp q (.closed (r2 x a b)))

/-- Generalization under hypotheses that do not depend on the label `x`. -/
noncomputable def Ctx.generalize {Γ : List M} {a : M} (p : Ctx Γ a) (x : M)
    (vacuity : ∀ h, h ∈ Γ → TargetProvable (impValue h (allValue x h))) :
    Ctx Γ (allValue x a) :=
  match p with
  | .assumption h => .mp (.assumption h) (.closed (vacuity _ h))
  | .closed d => .closed (tp_gen x d)
  | .mp p q => (p.generalize x vacuity).forallMP x (q.generalize x vacuity)

noncomputable def Ctx.arrowCompose {Γ : List M} {a b c : M}
    (p : Ctx Γ (impValue a b)) (q : Ctx Γ (impValue b c)) : Ctx Γ (impValue a c) :=
  .mp q (.mp p (.closed (imp_comp a b c)))

/-! ## Vacuity and quantifier rules -/

theorem negImpLeft {a b : M} (g : TargetProvable (negValue (impValue a b))) :
    TargetProvable a := by
  let ha : Ctx [a, negValue a] a := .assumption (by simp)
  let hn : Ctx [a, negValue a] (negValue a) := .assumption (by simp)
  let hi : Ctx [negValue a] (impValue a b) := ((Ctx.mp ha hn).explosion b).deduction
  exact (Ctx.mp hi (.closed g)).deduction.dne.empty

theorem negImpRight {a b : M} (g : TargetProvable (negValue (impValue a b))) :
    TargetProvable (negValue b) := by
  let hb : Ctx [b] b := .assumption (by simp)
  exact (Ctx.mp (hb.lift a) (.closed g)).deduction.empty

theorem negationVacuity (x a : M) (hv : TargetProvable (impValue a (allValue x a))) :
    TargetProvable (impValue (negValue a) (allValue x (negValue a))) := by
  have hc := contrapose hv
  have hg := tp_gen x hc
  have hl := tp_mp hg (r2 x (negValue (allValue x a)) (negValue a))
  have hr := contrapose (r6 x a)
  have hf := imp_trans hr (doubleNegationElimination (allValue x (negValue (allValue x a))))
  exact imp_trans hf hl

noncomputable def Ctx.casesOnFormula {Γ : List M} (a : M) {c : M}
    (p : Ctx (a :: Γ) c) (q : Ctx (negValue a :: Γ) c) : Ctx Γ c := by
  let hn : Ctx (negValue c :: Γ) (negValue c) := .assumption (by simp)
  let hp : Ctx (negValue c :: Γ) (impValue a c) := p.deduction.up (negValue c)
  let hna : Ctx (negValue c :: Γ) (negValue a) :=
    .mp hn (.mp hp (.closed (contraposition a c)))
  let hc : Ctx (negValue c :: Γ) c := .mp hna (q.deduction.up (negValue c))
  exact (Ctx.mp hc hn).deduction.dne

theorem implicationVacuity (x a b : M)
    (ha : TargetProvable (impValue a (allValue x a)))
    (hb : TargetProvable (impValue b (allValue x b))) :
    TargetProvable (impValue (impValue a b) (allValue x (impValue a b))) := by
  have hbLift : TargetProvable (impValue b (allValue x (impValue a b))) :=
    imp_trans hb (tp_mp (tp_gen x (imp_k b a)) (r2 x b (impValue a b)))
  let hn : Ctx [a, negValue a] (negValue a) := .assumption (by simp)
  let hp : Ctx [a, negValue a] a := .assumption (by simp)
  have hnot : TargetProvable (impValue (negValue a) (impValue a b)) :=
    ((Ctx.mp hp hn).explosion b).deduction.deduction.empty
  have haLift : TargetProvable (impValue (negValue a) (allValue x (impValue a b))) :=
    imp_trans (negationVacuity x a ha)
      (tp_mp (tp_gen x hnot) (r2 x (negValue a) (impValue a b)))
  let pa : Ctx [a, impValue a b] a := .assumption (by simp)
  let pab : Ctx [a, impValue a b] (impValue a b) := .assumption (by simp)
  let pc : Ctx [a, impValue a b] (allValue x (impValue a b)) :=
    .mp (.mp pa pab) (.closed hbLift)
  let pna : Ctx [negValue a, impValue a b] (negValue a) := .assumption (by simp)
  let pnc : Ctx [negValue a, impValue a b] (allValue x (impValue a b)) :=
    .mp pna (.closed haLift)
  exact (Ctx.casesOnFormula a pc pnc).deduction.empty

theorem universalVacuity (x y a : M) (h : TargetProvable (impValue a (allValue x a))) :
    TargetProvable (impValue (allValue y a) (allValue x (allValue y a))) :=
  imp_trans (tp_mp (tp_gen y h) (r2 y a (allValue x a))) (r4 y x a)

theorem conjunctionVacuity (x a b : M)
    (ha : TargetProvable (impValue a (allValue x a)))
    (hb : TargetProvable (impValue b (allValue x b))) :
    TargetProvable (impValue (conjValue a b) (allValue x (conjValue a b))) :=
  negationVacuity x (impValue a (negValue b))
    (implicationVacuity x a (negValue b) ha (negationVacuity x b hb))

noncomputable def Ctx.existsElim {Γ : List M} (x : M) {a b : M}
    (hv : TargetProvable (impValue b (allValue x b)))
    (p : Ctx Γ (allValue x (impValue a b))) (q : Ctx Γ (exValue x a)) : Ctx Γ b := by
  let hn : Ctx (negValue b :: Γ) (negValue b) := .assumption (by simp)
  let hnb : Ctx (negValue b :: Γ) (allValue x (negValue b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Ctx (negValue b :: Γ) (allValue x (impValue (negValue b) (negValue a))) :=
    (p.up (negValue b)).forallMP x (.closed (tp_gen x (contraposition a b)))
  let ha : Ctx (negValue b :: Γ) (allValue x (negValue a)) := hnb.forallMP x hc
  exact (Ctx.mp ha (q.up (negValue b))).deduction.dne

theorem existentialMonotonicity (x : M) {a b : M} (p : TargetProvable (impValue a b)) :
    TargetProvable (impValue (exValue x a) (exValue x b)) :=
  contrapose (tp_mp (tp_gen x (contrapose p)) (r2 x (negValue b) (negValue a)))

theorem liftImp (x : M) {a b : M} (p : TargetProvable (impValue a b)) :
    TargetProvable (impValue (allValue x a) (allValue x b)) :=
  tp_mp (tp_gen x p) (r2 x a b)

#print axioms Ctx.deduction
#print axioms explosion
#print axioms doubleNegationElimination
#print axioms contraposition
#print axioms implicationVacuity
#print axioms conjunctionVacuity
#print axioms existentialMonotonicity
end models
end PA194ModelLogic
