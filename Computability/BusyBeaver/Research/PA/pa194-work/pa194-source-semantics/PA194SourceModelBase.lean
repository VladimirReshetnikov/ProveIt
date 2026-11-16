import PA194SemanticSupply
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The source formulas in a structure

For a structure `N` of the relational source language in which equality is equality, the
formulas of the relational source development (zero, successor, ordinal domain, Kuratowski
pairs, graphs, addition and multiplication traces) are given their meaning as statements
about the membership relation `Mem x a` (`x` is a member of `a`). The structure need not be
extensional.

* `se_*`: truth of each formula at arbitrary terms is the corresponding statement.
* `mD_iff`, `mZ_iff`, `mS_iff`, `mA_iff`, `mMu_iff`, `mE_iff`: the letters of
  `sourceLetters` are these statements.
* `kur_inj`: an object is a Kuratowski pair of at most one pair of components.
* `sep_spec`: a separation instance, as the existence of the subset defined by a formula
  with parameters.
-/
namespace PA194SourceModel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.PairGraph

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section base
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

/-- `x` is a member of `a`. -/
def Mem (x a : N) : Prop := s.rel Relation.mem ![x, a]

theorem rel_eq_iff (a b : N) : s.rel Relation.eq ![a, b] ↔ a = b := by
  have h : (FirstOrder.Semiformula.Operator.Eq.eq (L := SourceL)).val ![a, b] ↔ a = b :=
    Structure.Eq.eq (L := SourceL) (M := N) a b
  have e : s.rel Relation.eq ![a, b] ↔
      (FirstOrder.Semiformula.Operator.Eq.eq (L := SourceL)).val ![a, b] := Iff.rfl
  exact e.trans h

/-! ### Statements about membership -/

def SZero (a : N) : Prop := ∀ x : N, ¬Mem x a
def SSucc (a b : N) : Prop := ∀ x : N, Mem x b ↔ (Mem x a ∨ x = a)
def SSubset (a b : N) : Prop := ∀ x : N, Mem x a → Mem x b
def STrans (a : N) : Prop := ∀ x y : N, Mem x a ∧ Mem y x → Mem y a
def SMemTrans (a : N) : Prop := ∀ x : N, Mem x a → STrans x
def SMemLinear (a : N) : Prop := ∀ x y : N, Mem x a ∧ Mem y a → (x = y ∨ (Mem x y ∨ Mem y x))
def SNonempty (a : N) : Prop := ∃ x : N, Mem x a
def SLeast (t m : N) : Prop := Mem m t ∧ ∀ x : N, Mem x t → (m = x ∨ Mem m x)
def SGreatest (t m : N) : Prop := Mem m t ∧ ∀ x : N, Mem x t → (x = m ∨ Mem x m)
def SExtrema (a : N) : Prop :=
  ∀ t : N, (SSubset t a ∧ SNonempty t) → ((∃ m : N, SLeast t m) ∧ (∃ m : N, SGreatest t m))
def SRep (a : N) : Prop := STrans a ∧ (SMemTrans a ∧ (SMemLinear a ∧ SExtrema a))
def SMemIr (a : N) : Prop := ∀ x : N, Mem x a → ¬Mem x x
/-- `a` is an ordinal representative. -/
def SDom (a : N) : Prop := SRep a ∧ SMemIr a

def SSing (a t : N) : Prop := ∀ x : N, Mem x t ↔ x = a
def SPair (a b p : N) : Prop := ∀ x : N, Mem x p ↔ (x = a ∨ x = b)
/-- `p` is a Kuratowski pair of `a` and `b`. -/
def SKur (p a b : N) : Prop := ∃ t q : N, SSing a t ∧ (SPair a b q ∧ SPair t q p)
/-- The graph `g` has an entry for the pair of `a` and `b`. -/
def SEdge (g a b : N) : Prop := ∃ p : N, Mem p g ∧ SKur p a b
def SGraphDom (top g : N) : Prop := ∀ x : N, (∃ y : N, SEdge g x y) ↔ (Mem x top ∨ x = top)
def SFun (g : N) : Prop := ∀ x y z : N, (SEdge g x y ∧ SEdge g x z) → y = z
def SRange (g : N) : Prop := ∀ x y : N, SEdge g x y → SDom y
def SAddRec (g : N) : Prop :=
  ∀ a b c : N, (SEdge g a b ∧ SSucc c a) → ∃ d : N, SEdge g c d ∧ SSucc d b
def SAddPrefix (top base zero g : N) : Prop :=
  SGraphDom top g ∧ (SFun g ∧ (SRange g ∧ (SEdge g zero base ∧ SAddRec g)))
/-- `z` is a sum of `x` and `y`. -/
def SAdd (x y z : N) : Prop := ∃ e g : N, SZero e ∧ (SAddPrefix x y e g ∧ SEdge g x z)
def SMulRec (g base : N) : Prop :=
  ∀ a b c : N, (SEdge g a b ∧ SSucc c a) → ∃ d : N, SEdge g c d ∧ SAdd d base b
def SMulPrefix (top base zero g : N) : Prop :=
  SGraphDom top g ∧ (SFun g ∧ (SRange g ∧ (SEdge g zero zero ∧ SMulRec g base)))
/-- `z` is a product of `x` and `y`. -/
def SMul (x y z : N) : Prop := ∃ e g : N, SZero e ∧ (SMulPrefix x y e g ∧ SEdge g x z)

/-! ### Truth of the formulas -/

section eval
variable {n : ℕ} (b : Fin n → N) (f : ℕ → N)

/-- The value of a term. -/
abbrev sv (t : Term n) : N := FirstOrder.Semiterm.val (s := s) b f t
/-- Truth of a formula. -/
abbrev se (φ : Formula n) : Prop := FirstOrder.Semiformula.Eval (s := s) b f φ

@[simp] theorem se_mem (a x : Term n) : se b f (mem a x) ↔ Mem (sv b f x) (sv b f a) :=
  iff_of_eq (congrArg (s.rel Relation.mem) (cv2 (FirstOrder.Semiterm.val (s := s) b f) x a))
@[simp] theorem se_eq (x y : Term n) : se b f (eq x y) ↔ sv b f x = sv b f y :=
  (iff_of_eq (congrArg (s.rel Relation.eq) (cv2 (FirstOrder.Semiterm.val (s := s) b f) x y))).trans
    (rel_eq_iff _ _)
@[simp] theorem se_imply (φ ψ : Formula n) :
    se b f (sourceImply φ ψ) ↔ (se b f φ → se b f ψ) := by
  show FirstOrder.Semiformula.Eval (s := s) b f (∼φ ⋎ ψ) ↔ _
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  tauto
@[simp] theorem se_iff (φ ψ : Formula n) :
    se b f (sourceIff φ ψ) ↔ (se b f φ ↔ se b f ψ) := by
  show FirstOrder.Semiformula.Eval (s := s) b f (sourceImply φ ψ ⋏ sourceImply ψ φ) ↔ _
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  have h1 := se_imply b f φ ψ
  have h2 := se_imply b f ψ φ
  constructor
  · rintro ⟨u, v⟩
    exact ⟨h1.mp u, h2.mp v⟩
  · intro h
    exact ⟨h1.mpr h.mp, h2.mpr h.mpr⟩

@[simp] theorem se_zero (a : Term n) : se b f (Ordinal.zero a) ↔ SZero (sv b f a) := by
  simp [Ordinal.zero, SZero]
@[simp] theorem se_successor (a c : Term n) :
    se b f (Ordinal.successor a c) ↔ SSucc (sv b f a) (sv b f c) := by
  simp [Ordinal.successor, SSucc]
@[simp] theorem se_subset (a c : Term n) :
    se b f (Ordinal.subset a c) ↔ SSubset (sv b f a) (sv b f c) := by
  simp [Ordinal.subset, SSubset]
@[simp] theorem se_transitive (a : Term n) :
    se b f (Ordinal.transitive a) ↔ STrans (sv b f a) := by
  simp [Ordinal.transitive, STrans]
@[simp] theorem se_memberTransitive (a : Term n) :
    se b f (Ordinal.memberTransitive a) ↔ SMemTrans (sv b f a) := by
  simp [Ordinal.memberTransitive, SMemTrans]
@[simp] theorem se_memberLinear (a : Term n) :
    se b f (Ordinal.memberLinear a) ↔ SMemLinear (sv b f a) := by
  simp [Ordinal.memberLinear, SMemLinear]
@[simp] theorem se_nonempty (a : Term n) :
    se b f (Ordinal.nonempty a) ↔ SNonempty (sv b f a) := by
  simp [Ordinal.nonempty, SNonempty]
@[simp] theorem se_least (t m : Term n) :
    se b f (Ordinal.least t m) ↔ SLeast (sv b f t) (sv b f m) := by
  simp [Ordinal.least, SLeast]
@[simp] theorem se_greatest (t m : Term n) :
    se b f (Ordinal.greatest t m) ↔ SGreatest (sv b f t) (sv b f m) := by
  simp [Ordinal.greatest, SGreatest]
@[simp] theorem se_internalExtrema (a : Term n) :
    se b f (Ordinal.internalExtrema a) ↔ SExtrema (sv b f a) := by
  simp [Ordinal.internalExtrema, SExtrema]
@[simp] theorem se_representative (a : Term n) :
    se b f (Ordinal.representative a) ↔ SRep (sv b f a) := by
  simp [Ordinal.representative, SRep]
@[simp] theorem se_memberIr (a : Term n) :
    se b f (Ordinal.memberIr a) ↔ SMemIr (sv b f a) := by
  simp [Ordinal.memberIr, SMemIr]
@[simp] theorem se_domain (a : Term n) : se b f (Ordinal.domain a) ↔ SDom (sv b f a) := by
  simp [Ordinal.domain, SDom]

@[simp] theorem se_singleton (a t : Term n) :
    se b f (PairGraph.singleton a t) ↔ SSing (sv b f a) (sv b f t) := by
  simp [PairGraph.singleton, SSing]
@[simp] theorem se_pair (a c p : Term n) :
    se b f (PairGraph.pair a c p) ↔ SPair (sv b f a) (sv b f c) (sv b f p) := by
  simp [PairGraph.pair, SPair]
@[simp] theorem se_kuratowski (p a c : Term n) :
    se b f (PairGraph.kuratowski p a c) ↔ SKur (sv b f p) (sv b f a) (sv b f c) := by
  simp [PairGraph.kuratowski, SKur]
@[simp] theorem se_edge (g a c : Term n) :
    se b f (PairGraph.edge g a c) ↔ SEdge (sv b f g) (sv b f a) (sv b f c) := by
  simp [PairGraph.edge, SEdge]
@[simp] theorem se_graphDomain (top g : Term n) :
    se b f (PairGraph.graphDomain top g) ↔ SGraphDom (sv b f top) (sv b f g) := by
  simp [PairGraph.graphDomain, SGraphDom]
@[simp] theorem se_graphFunctional (g : Term n) :
    se b f (PairGraph.graphFunctional g) ↔ SFun (sv b f g) := by
  simp [PairGraph.graphFunctional, SFun]
@[simp] theorem se_graphRange (g : Term n) :
    se b f (PairGraph.graphRange g) ↔ SRange (sv b f g) := by
  simp [PairGraph.graphRange, SRange]
@[simp] theorem se_addRecurrence (g : Term n) :
    se b f (PairGraph.addRecurrence g) ↔ SAddRec (sv b f g) := by
  simp [PairGraph.addRecurrence, SAddRec]
@[simp] theorem se_addPrefix (top base zero g : Term n) :
    se b f (PairGraph.addPrefix top base zero g) ↔
      SAddPrefix (sv b f top) (sv b f base) (sv b f zero) (sv b f g) := by
  simp [PairGraph.addPrefix, SAddPrefix]
@[simp] theorem se_addResult (x y z : Term n) :
    se b f (PairGraph.addResult x y z) ↔ SAdd (sv b f x) (sv b f y) (sv b f z) := by
  simp [PairGraph.addResult, SAdd]
@[simp] theorem se_mulRecurrence (g base : Term n) :
    se b f (PairGraph.mulRecurrence g base) ↔ SMulRec (sv b f g) (sv b f base) := by
  simp [PairGraph.mulRecurrence, SMulRec]
@[simp] theorem se_mulPrefix (top base zero g : Term n) :
    se b f (PairGraph.mulPrefix top base zero g) ↔
      SMulPrefix (sv b f top) (sv b f base) (sv b f zero) (sv b f g) := by
  simp [PairGraph.mulPrefix, SMulPrefix]
@[simp] theorem se_mulResult (x y z : Term n) :
    se b f (PairGraph.mulResult x y z) ↔ SMul (sv b f x) (sv b f y) (sv b f z) := by
  simp [PairGraph.mulResult, SMul]

end eval

/-! ### The letters -/

section letters
variable (f : ℕ → N)

theorem mD_iff (x : N) : @mD N (sourceLetters s f) x ↔ SDom x := by
  show se ![x] f (Ordinal.domain (.bvar 0)) ↔ _
  simp
theorem mE_iff (x y : N) : @mE N (sourceLetters s f) x y ↔ x = y := by
  show se ![x, y] f (eq (.bvar 0) (.bvar 1)) ↔ _
  simp
theorem mZ_iff (x : N) : @mZ N (sourceLetters s f) x ↔ SZero x := by
  show se ![x] f (Ordinal.zero (.bvar 0)) ↔ _
  simp
theorem mS_iff (x y : N) : @mS N (sourceLetters s f) x y ↔ SSucc x y := by
  show se ![x, y] f (Ordinal.successor (.bvar 0) (.bvar 1)) ↔ _
  simp
theorem mA_iff (x y z : N) : @mA N (sourceLetters s f) x y z ↔ SAdd x y z := by
  show se ![x, y, z] f (PairGraph.addResult (.bvar 0) (.bvar 1) (.bvar 2)) ↔ _
  simp
theorem mMu_iff (x y z : N) : @mMu N (sourceLetters s f) x y z ↔ SMul x y z := by
  show se ![x, y, z] f (PairGraph.mulResult (.bvar 0) (.bvar 1) (.bvar 2)) ↔ _
  simp

end letters

/-! ### Pairs -/

theorem kur_inj {p a c a' c' : N} (h : SKur p a c) (h' : SKur p a' c') : a = a' ∧ c = c' := by
  obtain ⟨t, q, ht, hq, hp⟩ := h
  obtain ⟨t', q', ht', hq', hp'⟩ := h'
  have at' : Mem a' t' := (ht' a').mpr rfl
  have aq : Mem a q := (hq a).mpr (Or.inl rfl)
  have cq : Mem c q := (hq c).mpr (Or.inr rfl)
  have aq' : Mem a' q' := (hq' a').mpr (Or.inl rfl)
  have cq' : Mem c' q' := (hq' c').mpr (Or.inr rfl)
  have e1 : a = a' := by
    rcases (hp t').mp ((hp' t').mpr (Or.inl rfl)) with e | e
    · rw [e] at at'
      exact ((ht a').mp at').symm
    · rw [← e] at aq
      exact (ht' a).mp aq
  subst e1
  refine ⟨rfl, ?_⟩
  rcases (hp q').mp ((hp' q').mpr (Or.inr rfl)) with e | e
  · -- q' = t
    rw [e] at cq'
    have c'a : c' = a := (ht c').mp cq'
    rcases (hp' q).mp ((hp q).mpr (Or.inr rfl)) with e2 | e2
    · rw [e2] at cq
      rw [c'a]
      exact (ht' c).mp cq
    · rw [e2, e] at cq
      rw [c'a]
      exact (ht c).mp cq
  · -- q' = q
    rw [e] at cq'
    rcases (hq c').mp cq' with h1 | h1
    · rw [← e] at cq
      rcases (hq' c).mp cq with h2 | h2
      · rw [h1, h2]
      · exact h2
    · exact h1.symm

theorem edge_unique_pair {g a c : N} (h : SEdge g a c) :
    ∃ p : N, Mem p g ∧ SKur p a c := h

/-! ### Separation -/

/-- A separation instance at an assignment of its parameters: the subset of `a` defined by
`p` exists. -/
theorem sep_spec
    (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
      FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
    (p : Semiproposition SourceL 1) (f : ℕ → N) (a : N) :
    ∃ c : N, ∀ x : N, Mem x c ↔ (Mem x a ∧ FirstOrder.Semiformula.Eval (s := s) ![x] f p) := by
  have h := hsep p f
  have h' : ∀ a : N, ∃ c : N, ∀ x : N,
      FirstOrder.Semiformula.Eval (s := s) (x :> c :> a :> ![]) f
        (sourceIff (memAtom 1 0) (memAtom 2 0 ⋏ liftMember p)) := h
  obtain ⟨c, hc⟩ := h' a
  refine ⟨c, fun x => ?_⟩
  have hx := (se_iff (x :> c :> a :> ![]) f (memAtom 1 0) (memAtom 2 0 ⋏ liftMember p)).mp (hc x)
  have e1 : se (x :> c :> a :> ![]) f (memAtom 1 0) ↔ Mem x c :=
    iff_of_eq (congrArg (s.rel Relation.mem)
      (cv2 (FirstOrder.Semiterm.val (s := s) (x :> c :> a :> ![]) f) (.bvar 0) (.bvar 1)))
  have e2 : se (x :> c :> a :> ![]) f (memAtom 2 0) ↔ Mem x a :=
    iff_of_eq (congrArg (s.rel Relation.mem)
      (cv2 (FirstOrder.Semiterm.val (s := s) (x :> c :> a :> ![]) f) (.bvar 0) (.bvar 2)))
  have e3 : se (x :> c :> a :> ![]) f (liftMember p) ↔
      FirstOrder.Semiformula.Eval (s := s) ![x] f p := by
    show FirstOrder.Semiformula.Eval (s := s) (x :> c :> a :> ![]) f
      (Rewriting.app (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id) p) ↔ _
    rw [FirstOrder.Semiformula.eval_rew]
    have eb : (fun i : Fin 1 => FirstOrder.Semiterm.val (s := s) (x :> c :> a :> ![]) f
        ((Rew.map (L := SourceL) (fun _ : Fin 1 => (0 : Fin 3)) (id : ℕ → ℕ)) #i)) = ![x] := by
      funext i
      simp
    have ef : (fun z : ℕ => FirstOrder.Semiterm.val (s := s) (x :> c :> a :> ![]) f
        ((Rew.map (L := SourceL) (fun _ : Fin 1 => (0 : Fin 3)) (id : ℕ → ℕ)) &z)) = f := by
      funext z
      simp
    simp only [Function.comp_def] at *
    rw [eb, ef]
  have e4 : se (x :> c :> a :> ![]) f (memAtom 2 0 ⋏ liftMember p) ↔
      (Mem x a ∧ FirstOrder.Semiformula.Eval (s := s) ![x] f p) := by
    show FirstOrder.Semiformula.Eval (s := s) (x :> c :> a :> ![]) f
      (memAtom 2 0 ⋏ liftMember p) ↔ _
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    exact and_congr e2 e3
  exact e1.symm.trans (hx.trans e4)

#print axioms kur_inj
#print axioms sep_spec
#print axioms mD_iff
#print axioms mA_iff
#print axioms mMu_iff
end base
end PA194SourceModel
