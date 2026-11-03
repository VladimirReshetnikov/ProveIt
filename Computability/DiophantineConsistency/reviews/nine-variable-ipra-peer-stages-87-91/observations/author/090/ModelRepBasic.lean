import DiophantineConsistency.ModelRepCore
import DiophantineConsistency.ModelScalarPR
import DiophantineConsistency.ScalarPRRepresentation
import DiophantineConsistency.ComputationRepresentation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Internal correctness of the basic representation combinators

For every combinator used by `ScalarPRCode.graphRep` except the
primitive-recursion trace `ScalarPRRepresentation.recursionCoordinates`, this
file proves `ModelRep.Holds`/`ModelRep.GraphHolds` for an explicit model-uniform
predicate or function: equality, conjunction, disjunction, finite conjunction,
existential blocks, reindexing, composition, graph substitution, constants,
coordinates, addition, multiplication, the comparison relations, Mathlib's
pairing graph and its inverse projections, and existential acceptance.

All arguments go through the ring of differences: a model-level zero of the
split-natural syntax is a zero of the ordinary ring evaluation
`residual e u = e.evalRing (ι ∘ u)` in `DiffRing V`
(`ModelDifferenceRing.internalZero_iff`).

`graphRep_holds` then proves, by induction on programs, that the compiled
graph `c.graphRep` is internally correct for `ModelScalarPR.evalV c`, with the
primitive-recursion case supplied as the hypothesis `PrecCase`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepBasic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR
open AdaptiveEquationSyntax2011 (InternalZero)

/-! ### Ring evaluation of renamed syntax -/

theorem evalRing_rename {σ τ R : Type*} [CommRing R] (e : Expr σ) (f : σ → τ) (u : τ → R) :
    (e.rename f).evalRing u = e.evalRing (u ∘ f) := by
  induction e with
  | constant z => rfl
  | var i => rfl
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | sub p q hp hq => exact congrArg₂ (· - ·) hp hq
  | mul p q hp hq => exact congrArg₂ (· * ·) hp hq

theorem append_castAdd {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) :
    Fin.append a b ∘ Fin.castAdd n = a :=
  funext fun i => Fin.append_left a b i

theorem append_natAdd {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) :
    Fin.append a b ∘ Fin.natAdd m = b :=
  funext fun i => Fin.append_right a b i

section Residual
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ordinary ring value of syntax at a model valuation. -/
def residual {σ : Type*} (e : Expr σ) (u : σ → V) : DiffRing V :=
  e.evalRing (fun i => ι (u i))

theorem internalZero_iff_residual {σ : Type*} (e : Expr σ) (u : σ → V) :
    InternalZero e u ↔ residual e u = 0 :=
  internalZero_iff e u

theorem residual_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) (u : τ → V) :
    residual (e.rename f) u = residual e (u ∘ f) :=
  evalRing_rename e f (fun i => ι (u i))

theorem residual_add {σ : Type*} (p q : Expr σ) (u : σ → V) :
    residual (p + q) u = residual p u + residual q u := rfl

theorem residual_sub {σ : Type*} (p q : Expr σ) (u : σ → V) :
    residual (p - q) u = residual p u - residual q u := rfl

theorem residual_mul {σ : Type*} (p q : Expr σ) (u : σ → V) :
    residual (p * q) u = residual p u * residual q u := rfl

theorem internalZero_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) (u : τ → V) :
    InternalZero (e.rename f) u ↔ InternalZero e (u ∘ f) := by
  rw [internalZero_iff_residual, internalZero_iff_residual, residual_rename]

theorem ι_eq_ι {a b : V} : (ι a : DiffRing V) = ι b ↔ a = b := ι_injective.eq_iff

theorem ι_add' (a b : V) : (ι (a + b) : DiffRing V) = ι a + ι b := map_add ι a b

theorem ι_mul' (a b : V) : (ι (a * b) : DiffRing V) = ι a * ι b := map_mul ι a b

theorem ι_one' : (ι (1 : V) : DiffRing V) = 1 := map_one ι

theorem ι_natCast' (n : ℕ) : (ι (n : V) : DiffRing V) = n := map_natCast ι n

end Residual

/-! ### Generic combinators -/

section Generic
variable {σ τ : Type*}

/-- An equality of syntax holds internally as equality of ring values. -/
theorem holds_equality (p q : Expr σ) :
    Holds (Rep.equality p q) (fun V _ _ v => residual p v = residual q v) := by
  intro V _ _ v
  have key : ∀ w : Fin 0 → V,
      InternalZero (Rep.equality p q).expression (Sum.elim v w) ↔
        residual p v - residual q v = 0 := by
    intro w
    have h1 : residual (Rep.equality p q).expression (Sum.elim v w) =
        residual (p - q) (Sum.elim v w ∘ Sum.inl) :=
      residual_rename (p - q) Sum.inl (Sum.elim v w)
    have h2 : (Sum.elim v w ∘ Sum.inl : σ → V) = v := rfl
    rw [internalZero_iff_residual, h1, h2, residual_sub]
  show residual p v = residual q v ↔ _
  constructor
  · intro h
    exact ⟨Fin.elim0, (key _).mpr (sub_eq_zero.mpr h)⟩
  · rintro ⟨w, hw⟩
    exact sub_eq_zero.mp ((key w).mp hw)

theorem holds_reindex {P : (σ → ℕ) → Prop} {r : Rep σ P} {Q : ModelPred σ}
    (hr : Holds r Q) (f : σ → τ) :
    Holds (r.reindex f) (fun V _ _ v => Q V (v ∘ f)) := by
  intro V _ _ v
  have key : ∀ w : Fin r.witnessCount → V,
      InternalZero (r.reindex f).expression (Sum.elim v w) ↔
        InternalZero r.expression (Sum.elim (v ∘ f) w) := by
    intro w
    have hc : Sum.elim v w ∘ Sum.map f id = Sum.elim (v ∘ f) w := by
      funext x
      cases x <;> rfl
    change InternalZero (r.expression.rename (Sum.map f id)) (Sum.elim v w) ↔ _
    rw [internalZero_rename, hc]
  exact (hr V (v ∘ f)).trans (exists_congr fun w => (key w).symm)

theorem holds_conjunction {P P' : (σ → ℕ) → Prop} {r : Rep σ P} {s : Rep σ P'}
    {Q Q' : ModelPred σ} (hr : Holds r Q) (hs : Holds s Q') :
    Holds (r.conjunction s) (fun V _ _ v => Q V v ∧ Q' V v) := by
  intro V _ _ v
  have key : ∀ w : Fin (r.witnessCount + s.witnessCount) → V,
      InternalZero (r.conjunction s).expression (Sum.elim v w) ↔
        InternalZero r.expression (Sum.elim v (w ∘ Fin.castAdd s.witnessCount)) ∧
        InternalZero s.expression (Sum.elim v (w ∘ Fin.natAdd r.witnessCount)) := by
    intro w
    have hl : Sum.elim v w ∘ Sum.map id (Fin.castAdd s.witnessCount) =
        Sum.elim v (w ∘ Fin.castAdd s.witnessCount) := by
      funext x
      cases x <;> rfl
    have hr' : Sum.elim v w ∘ Sum.map id (Fin.natAdd r.witnessCount) =
        Sum.elim v (w ∘ Fin.natAdd r.witnessCount) := by
      funext x
      cases x <;> rfl
    change InternalZero
      (r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount)) *
          r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount)) +
        s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount)) *
          s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))) (Sum.elim v w) ↔ _
    rw [internalZero_iff_residual, internalZero_iff_residual, internalZero_iff_residual,
      residual_add, residual_mul, residual_mul, residual_rename, residual_rename, hl, hr']
    exact mul_self_add_mul_self_eq_zero
  show Q V v ∧ Q' V v ↔ _
  constructor
  · rintro ⟨hq, hq'⟩
    obtain ⟨a, ha⟩ := (hr V v).mp hq
    obtain ⟨b, hb⟩ := (hs V v).mp hq'
    refine ⟨Fin.append a b, (key _).mpr ⟨?_, ?_⟩⟩
    · rw [append_castAdd]
      exact ha
    · rw [append_natAdd]
      exact hb
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (key w).mp hw
    exact ⟨(hr V v).mpr ⟨_, h1⟩, (hs V v).mpr ⟨_, h2⟩⟩

theorem holds_disjunction {P P' : (σ → ℕ) → Prop} {r : Rep σ P} {s : Rep σ P'}
    {Q Q' : ModelPred σ} (hr : Holds r Q) (hs : Holds s Q') :
    Holds (r.disjunction s) (fun V _ _ v => Q V v ∨ Q' V v) := by
  intro V _ _ v
  have key : ∀ w : Fin (r.witnessCount + s.witnessCount) → V,
      InternalZero (r.disjunction s).expression (Sum.elim v w) ↔
        InternalZero r.expression (Sum.elim v (w ∘ Fin.castAdd s.witnessCount)) ∨
        InternalZero s.expression (Sum.elim v (w ∘ Fin.natAdd r.witnessCount)) := by
    intro w
    have hl : Sum.elim v w ∘ Sum.map id (Fin.castAdd s.witnessCount) =
        Sum.elim v (w ∘ Fin.castAdd s.witnessCount) := by
      funext x
      cases x <;> rfl
    have hr' : Sum.elim v w ∘ Sum.map id (Fin.natAdd r.witnessCount) =
        Sum.elim v (w ∘ Fin.natAdd r.witnessCount) := by
      funext x
      cases x <;> rfl
    change InternalZero
      (r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount)) *
        s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))) (Sum.elim v w) ↔ _
    rw [internalZero_iff_residual, internalZero_iff_residual, internalZero_iff_residual,
      residual_mul, residual_rename, residual_rename, hl, hr']
    exact mul_eq_zero
  show Q V v ∨ Q' V v ↔ _
  constructor
  · rintro (hq | hq')
    · obtain ⟨a, ha⟩ := (hr V v).mp hq
      refine ⟨Fin.append a (fun _ => 0), (key _).mpr (Or.inl ?_)⟩
      rw [append_castAdd]
      exact ha
    · obtain ⟨b, hb⟩ := (hs V v).mp hq'
      refine ⟨Fin.append (fun _ => 0) b, (key _).mpr (Or.inr ?_)⟩
      rw [append_natAdd]
      exact hb
  · rintro ⟨w, hw⟩
    rcases (key w).mp hw with h | h
    · exact Or.inl ((hr V v).mpr ⟨_, h⟩)
    · exact Or.inr ((hs V v).mpr ⟨_, h⟩)

theorem holds_existsBlock {k : ℕ} {P : (σ ⊕ Fin k → ℕ) → Prop} {r : Rep (σ ⊕ Fin k) P}
    {Q : ModelPred (σ ⊕ Fin k)} (hr : Holds r Q) :
    Holds r.existsBlock (fun V _ _ v => ∃ a : Fin k → V, Q V (Sum.elim v a)) := by
  intro V _ _ v
  have key : ∀ w : Fin (k + r.witnessCount) → V,
      InternalZero r.existsBlock.expression (Sum.elim v w) ↔
        InternalZero r.expression
          (Sum.elim (Sum.elim v (w ∘ Fin.castAdd r.witnessCount)) (w ∘ Fin.natAdd k)) := by
    intro w
    obtain ⟨idx, hidx, hexpr⟩ :
        ∃ idx : (σ ⊕ Fin k) ⊕ Fin r.witnessCount → σ ⊕ Fin (k + r.witnessCount),
          Sum.elim v w ∘ idx =
              Sum.elim (Sum.elim v (w ∘ Fin.castAdd r.witnessCount)) (w ∘ Fin.natAdd k) ∧
            r.existsBlock.expression = r.expression.rename idx :=
      ⟨_, funext fun x => by rcases x with (i | i) | i <;> rfl, rfl⟩
    have hz : InternalZero r.existsBlock.expression (Sum.elim v w) ↔
        InternalZero (r.expression.rename idx) (Sum.elim v w) :=
      Iff.of_eq (congrArg (fun e => InternalZero e (Sum.elim v w)) hexpr)
    rw [hz, internalZero_rename, hidx]
  show (∃ a : Fin k → V, Q V (Sum.elim v a)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (hr V (Sum.elim v a)).mp ha
    refine ⟨Fin.append a b, (key _).mpr ?_⟩
    rw [append_castAdd, append_natAdd]
    exact hb
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ Fin.castAdd r.witnessCount,
      (hr V _).mpr ⟨w ∘ Fin.natAdd k, (key w).mp hw⟩⟩

/-- Finite conjunctions, by recursion on the length as in `Rep.allFin`. -/
theorem holds_allFin : ∀ (n : ℕ) (P : Fin n → (σ → ℕ) → Prop) (rs : ∀ i, Rep σ (P i))
    (Q : Fin n → ModelPred σ), (∀ i, Holds (rs i) (Q i)) →
      Holds (Rep.allFin n P rs) (fun V _ _ v => ∀ i, Q i V v)
  | 0, P, rs, Q, _ => by
    refine (holds_congr _ ?_ (holds_equality (0 : Expr σ) 0))
    intro V _ _ v
    exact ⟨fun _ i => i.elim0, fun _ => rfl⟩
  | n + 1, P, rs, Q, h => by
    have ih := holds_allFin n (fun i => P i.succ) (fun i => rs i.succ) (fun i => Q i.succ)
      (fun i => h i.succ)
    refine (holds_congr _ ?_ (holds_conjunction (h 0) ih))
    intro V _ _ v
    exact (Fin.forall_fin_succ (P := fun i => Q i V v)).symm

/-- Substitution of a finite family of graphs into a predicate. -/
theorem holds_compose {n : ℕ} {P : (Fin n → ℕ) → Prop} {f : Fin n → (σ → ℕ) → ℕ}
    {r : Rep (Fin n) P} {g : ∀ i, GraphRep (f i)} {Q : ModelPred (Fin n)}
    {G : Fin n → ModelFun σ} (hr : Holds r Q) (hg : ∀ i, GraphHolds (g i) (G i)) :
    Holds (Rep.compose r g) (fun V _ _ v => Q V (fun i => G i V v)) := by
  refine (holds_congr _ ?_
    (holds_existsBlock (holds_conjunction (holds_reindex hr Sum.inr)
      (holds_allFin n _ _ _ (fun i => holds_reindex (hg i) _)))))
  intro V _ _ v
  change (∃ a : Fin n → V, Q V a ∧ ∀ i, a i = G i V v) ↔ Q V (fun i => G i V v)
  constructor
  · rintro ⟨a, ha, hi⟩
    have hfun : a = fun i => G i V v := funext hi
    subst hfun
    exact ha
  · intro h
    exact ⟨fun i => G i V v, h, fun _ => rfl⟩

end Generic

/-! ### Graph combinators -/

section Graphs
variable {σ τ : Type*}

/-- Assign the distinguished output coordinate of a model valuation. -/
def withOutputV {V : Type} (v : σ → V) (a : V) : Option σ → V
  | none => a
  | some i => v i

theorem graphHolds_of_eq {f : (σ → ℕ) → ℕ} {r : GraphRep f} {F G : ModelFun σ}
    (h : GraphHolds r F)
    (e : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (v : σ → V), F V v = G V v) :
    GraphHolds r G := by
  refine holds_congr _ ?_ h
  intro V _ _ v
  show v none = F V (fun i => v (some i)) ↔ v none = G V (fun i => v (some i))
  rw [e V (fun i => v (some i))]

theorem graphHolds_constant (n : ℕ) :
    GraphHolds (GraphRep.constant (σ := σ) n) (fun V _ _ _ => (n : V)) := by
  refine (holds_congr _ ?_ (holds_equality _ _))
  intro V _ _ v
  change ι (v none) = ((n : ℤ) : DiffRing V) ↔ v none = (n : V)
  rw [Int.cast_natCast, ← ι_natCast' (V := V), ι_eq_ι (V := V)]

theorem graphHolds_coordinate (i : σ) :
    GraphHolds (GraphRep.coordinate i) (fun V _ _ v => v i) := by
  refine (holds_congr _ ?_ (holds_equality _ _))
  intro V _ _ v
  change ι (v none) = ι (v (some i)) ↔ v none = v (some i)
  exact ι_eq_ι

theorem graphHolds_reindex {f : (σ → ℕ) → ℕ} {r : GraphRep f} {F : ModelFun σ}
    (hr : GraphHolds r F) (h : σ → τ) :
    GraphHolds (r.reindex h) (fun V _ _ v => F V (fun i => v (h i))) :=
  (holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_reindex hr (Option.map h)))

/-- `bindGraph` with its coordinate map exposed. -/
theorem holds_bindCore {P : (Option σ → ℕ) → Prop} {f : (σ → ℕ) → ℕ}
    {r : Rep (Option σ) P} {g : GraphRep f} {Q : ModelPred (Option σ)} {F : ModelFun σ}
    (hr : Holds r Q) (hg : GraphHolds g F) (idx : Option σ → σ ⊕ Fin 1)
    (hnone : idx none = Sum.inr 0) (hsome : ∀ i, idx (some i) = Sum.inl i) :
    Holds (((r.conjunction g).reindex idx).existsBlock)
      (fun V _ _ v => Q V (withOutputV v (F V v))) := by
  refine holds_congr _ ?_ (holds_existsBlock (holds_reindex (holds_conjunction hr hg) idx))
  intro V _ _ v
  have hval : ∀ a : Fin 1 → V, Sum.elim v a ∘ idx = withOutputV v (a 0) := by
    intro a
    funext x
    cases x with
    | none => exact (congrArg (Sum.elim v a) hnone).trans rfl
    | some i => exact (congrArg (Sum.elim v a) (hsome i)).trans rfl
  simp only [hval]
  constructor
  · rintro ⟨a, ha, hout⟩
    have h0 : a 0 = F V v := hout
    rw [h0] at ha
    exact ha
  · intro h
    exact ⟨fun _ => F V v, h, rfl⟩

/-- Substituting a represented function for the distinguished coordinate. -/
theorem holds_bindGraph {P : (Option σ → ℕ) → Prop} {f : (σ → ℕ) → ℕ}
    {r : Rep (Option σ) P} {g : GraphRep f} {Q : ModelPred (Option σ)} {F : ModelFun σ}
    (hr : Holds r Q) (hg : GraphHolds g F) :
    Holds (r.bindGraph g) (fun V _ _ v => Q V (withOutputV v (F V v))) :=
  (holds_bindCore hr hg _ (by rfl) (by intro i; rfl))

theorem graphHolds_add {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.add s) (fun V _ _ v => F V v + G V v) := by
  refine (holds_congr _ ?_
    (holds_bindGraph (holds_bindGraph (holds_equality _ _) (graphHolds_reindex hs _))
      (graphHolds_reindex hr _)))
  intro V _ _ v
  change ι (v none) = ι (F V (fun i => v (some i))) + ι (G V (fun i => v (some i))) ↔
    v none = F V (fun i => v (some i)) + G V (fun i => v (some i))
  rw [← ι_add' (V := V), ι_eq_ι (V := V)]

theorem graphHolds_mul {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.mul s) (fun V _ _ v => F V v * G V v) := by
  refine (holds_congr _ ?_
    (holds_bindGraph (holds_bindGraph (holds_equality _ _) (graphHolds_reindex hs _))
      (graphHolds_reindex hr _)))
  intro V _ _ v
  change ι (v none) = ι (F V (fun i => v (some i))) * ι (G V (fun i => v (some i))) ↔
    v none = F V (fun i => v (some i)) * G V (fun i => v (some i))
  rw [← ι_mul' (V := V), ι_eq_ι (V := V)]

/-- Composition of a represented function with a finite family of graphs. -/
theorem graphHolds_compose {n : ℕ} {f : (Fin n → ℕ) → ℕ} {g : Fin n → (σ → ℕ) → ℕ}
    {r : GraphRep f} {s : ∀ i, GraphRep (g i)} {F : ModelFun (Fin n)}
    {G : Fin n → ModelFun σ} (hr : GraphHolds r F) (hs : ∀ i, GraphHolds (s i) (G i)) :
    GraphHolds (GraphRep.compose r s) (fun V _ _ v => F V (fun i => G i V v)) := by
  refine (holds_congr _ ?_
    (holds_compose (holds_reindex hr _)
      (G := fun j => Fin.cases (motive := fun _ => ModelFun (Option σ))
        (fun V _ _ v => v none) (fun i V _ _ v => G i V (fun x => v (some x))) j) ?_))
  · intro V _ _ v
    exact Iff.rfl
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact graphHolds_coordinate none
    · exact graphHolds_reindex (hs i) some

end Graphs

/-! ### Comparisons and pairing -/

section Pairing
variable {σ : Type*}

theorem holds_le (a b : σ) :
    Holds (ArithmeticRep.le a b) (fun V _ _ v => v a ≤ v b) := by
  intro V _ _ v
  have key : ∀ w : Fin 1 → V,
      InternalZero (ArithmeticRep.le a b).expression (Sum.elim v w) ↔
        ι (v a) + ι (w 0) - ι (v b) = 0 :=
    fun w => internalZero_iff_residual _ _
  show v a ≤ v b ↔ _
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨fun _ => c, (key _).mpr ?_⟩
    show ι (v a) + ι c - ι (v b) = 0
    rw [hc, ι_add' (V := V)]
    ring
  · rintro ⟨(w : Fin 1 → V), hw⟩
    have h : ι (v a) + ι (w 0) - ι (v b) = 0 := (key w).mp hw
    have hw0 : (0 : DiffRing V) ≤ ι (w 0) := ι_nonneg (w 0)
    have hle : (ι (v a) : DiffRing V) ≤ ι (v b) := by linarith
    exact ι_le_ι.mp hle

theorem holds_lt (a b : σ) :
    Holds (ArithmeticRep.lt a b) (fun V _ _ v => v a < v b) := by
  intro V _ _ v
  have key : ∀ w : Fin 1 → V,
      InternalZero (ArithmeticRep.lt a b).expression (Sum.elim v w) ↔
        ι (v a) + ι (w 0) + ((1 : ℤ) : DiffRing V) - ι (v b) = 0 :=
    fun w => internalZero_iff_residual _ _
  show v a < v b ↔ _
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_add_of_le (succ_le_iff_lt.mpr h)
    refine ⟨fun _ => c, (key _).mpr ?_⟩
    show ι (v a) + ι c + ((1 : ℤ) : DiffRing V) - ι (v b) = 0
    rw [hc, ι_add' (V := V), ι_add' (V := V), ι_one' (V := V), Int.cast_one]
    ring
  · rintro ⟨(w : Fin 1 → V), hw⟩
    have h : ι (v a) + ι (w 0) + ((1 : ℤ) : DiffRing V) - ι (v b) = 0 := (key w).mp hw
    rw [Int.cast_one] at h
    have hw0 : (0 : DiffRing V) ≤ ι (w 0) := ι_nonneg (w 0)
    have hlt : (ι (v a) : DiffRing V) < ι (v b) := by linarith
    exact ι_lt_ι.mp hlt

/-- Mathlib's two-branch pairing graph computes the internal pairing. -/
theorem graphHolds_pairCoordinates :
    GraphHolds GraphRep.pairCoordinates (fun V _ _ v => mpair (v 0) (v 1)) := by
  refine (holds_congr _ ?_ (holds_disjunction
    (holds_conjunction (holds_lt _ _) ((holds_equality _ _)))
    (holds_conjunction (holds_le _ _) ((holds_equality _ _)))))
  intro V _ _ v
  have e1 : ι (v (some 1)) * ι (v (some 1)) + ι (v (some 0)) =
      (ι (v (some 1) * v (some 1) + v (some 0)) : DiffRing V) := by
    rw [ι_add' (V := V), ι_mul' (V := V)]
  have e2 : ι (v (some 0)) * ι (v (some 0)) + ι (v (some 0)) + ι (v (some 1)) =
      (ι (v (some 0) * v (some 0) + v (some 0) + v (some 1)) : DiffRing V) := by
    rw [ι_add' (V := V), ι_add' (V := V), ι_mul' (V := V)]
  change ((v (some 0) < v (some 1) ∧
        ι (v none) = ι (v (some 1)) * ι (v (some 1)) + ι (v (some 0))) ∨
      (v (some 1) ≤ v (some 0) ∧
        ι (v none) = ι (v (some 0)) * ι (v (some 0)) + ι (v (some 0)) + ι (v (some 1)))) ↔
    v none = mpair (v (some 0)) (v (some 1))
  rw [e1, e2, ι_eq_ι (V := V), ι_eq_ι (V := V)]
  exact mpair_eq_iff.symm

theorem graphHolds_pair {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.pair s) (fun V _ _ v => mpair (F V v) (G V v)) := by
  refine graphHolds_compose
    (G := fun i => Fin.cases (motive := fun _ => ModelFun σ) F (fun _ => G) i)
    graphHolds_pairCoordinates ?_
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hr
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact hs

theorem graphHolds_unpairLeftCoordinate :
    GraphHolds GraphRep.unpairLeftCoordinate (fun V _ _ v => munpair₁ (v 0)) := by
  refine (holds_congr _ ?_
    (holds_existsBlock (holds_reindex graphHolds_pairCoordinates _)))
  intro V _ _ v
  change (∃ w : Fin 1 → V, v (some 0) = mpair (v none) (w 0)) ↔
    v none = munpair₁ (v (some 0))
  constructor
  · rintro ⟨w, hw⟩
    rw [hw, munpair₁_mpair]
  · intro h
    refine ⟨fun _ => munpair₂ (v (some 0)), ?_⟩
    rw [h]
    exact (mpair_unpair _).symm

theorem graphHolds_unpairRightCoordinate :
    GraphHolds GraphRep.unpairRightCoordinate (fun V _ _ v => munpair₂ (v 0)) := by
  refine (holds_congr _ ?_
    (holds_existsBlock (holds_reindex graphHolds_pairCoordinates _)))
  intro V _ _ v
  change (∃ w : Fin 1 → V, v (some 0) = mpair (w 0) (v none)) ↔
    v none = munpair₂ (v (some 0))
  constructor
  · rintro ⟨w, hw⟩
    rw [hw, munpair₂_mpair]
  · intro h
    refine ⟨fun _ => munpair₁ (v (some 0)), ?_⟩
    rw [h]
    exact (mpair_unpair _).symm

theorem graphHolds_unpairLeft {f : (σ → ℕ) → ℕ} {r : GraphRep f} {F : ModelFun σ}
    (hr : GraphHolds r F) :
    GraphHolds r.unpairLeft (fun V _ _ v => munpair₁ (F V v)) :=
  graphHolds_compose (G := fun _ => F) graphHolds_unpairLeftCoordinate (fun _ => hr)

theorem graphHolds_unpairRight {f : (σ → ℕ) → ℕ} {r : GraphRep f} {F : ModelFun σ}
    (hr : GraphHolds r F) :
    GraphHolds r.unpairRight (fun V _ _ v => munpair₂ (F V v)) :=
  graphHolds_compose (G := fun _ => F) graphHolds_unpairRightCoordinate (fun _ => hr)

end Pairing

/-! ### Existential acceptance -/

/-- `existsValue` holds internally: some model input attains the accepted value. -/
theorem holds_existsValue {f : ℕ → ℕ} {r : GraphRep (fun v : Fin 1 → ℕ => f (v 0))}
    {F : ModelFun (Fin 1)} (hr : GraphHolds r F) (accepted : ℕ) :
    Holds (GraphRep.existsValue r accepted)
      (fun V _ _ _ => ∃ t : V, F V (fun _ => t) = (accepted : V)) := by
  refine (holds_congr _ ?_ (holds_existsBlock (holds_conjunction
    (holds_reindex hr _) ((holds_equality _ _)))))
  intro V _ _ v
  have hacc : ((accepted : ℤ) : DiffRing V) = ι (accepted : V) := by
    rw [Int.cast_natCast, ι_natCast' (V := V)]
  change (∃ w : Fin 2 → V, w 0 = F V (fun _ => w 1) ∧
      ι (w 0) = ((accepted : ℤ) : DiffRing V)) ↔ ∃ t : V, F V (fun _ => t) = (accepted : V)
  rw [hacc]
  constructor
  · rintro ⟨w, hw, ha⟩
    exact ⟨w 1, hw.symm.trans (ι_eq_ι.mp ha)⟩
  · rintro ⟨t, ht⟩
    exact ⟨![(accepted : V), t], ht.symm, rfl⟩

/-! ### Compiled scalar programs -/

/-- The internal semantics of a program as a model-uniform unary function. -/
abbrev evalFun (c : ScalarPRCode) : ModelFun (Fin 1) := fun V _ _ v => evalV c (v 0)

/-- The primitive-recursion case of `graphRep_holds`, to be discharged separately
(beta-function trace and bounded universal quantification). -/
abbrev PrecCase : Prop :=
  ∀ f g : ScalarPRCode, GraphHolds f.graphRep (evalFun f) →
    GraphHolds g.graphRep (evalFun g) →
    GraphHolds (ScalarPRCode.prec f g).graphRep (evalFun (ScalarPRCode.prec f g))

/-- Every compiled program graph is internally correct for `evalV`, given the
primitive-recursion case. -/
theorem graphRep_holds (hprec : PrecCase) (c : ScalarPRCode) :
    GraphHolds c.graphRep (evalFun c) := by
  induction c with
  | zero =>
    exact graphHolds_of_eq (graphHolds_constant 0) (by
      intro V _ _ v
      show ((0 : ℕ) : V) = evalV ScalarPRCode.zero (v 0)
      rw [Nat.cast_zero, evalV_zero])
  | succ =>
    exact graphHolds_of_eq
      (graphHolds_add (graphHolds_coordinate (0 : Fin 1)) (graphHolds_constant 1)) (by
      intro V _ _ v
      show v 0 + ((1 : ℕ) : V) = evalV ScalarPRCode.succ (v 0)
      rw [Nat.cast_one, evalV_succ])
  | left =>
    exact graphHolds_of_eq (graphHolds_unpairLeft (graphHolds_coordinate (0 : Fin 1))) (by
      intro V _ _ v
      exact (evalV_left (v 0)).symm)
  | right =>
    exact graphHolds_of_eq (graphHolds_unpairRight (graphHolds_coordinate (0 : Fin 1))) (by
      intro V _ _ v
      exact (evalV_right (v 0)).symm)
  | pair f g ihf ihg =>
    exact graphHolds_of_eq (graphHolds_pair ihf ihg) (by
      intro V _ _ v
      exact (evalV_pair f g (v 0)).symm)
  | comp f g ihf ihg =>
    exact graphHolds_of_eq (graphHolds_compose (G := fun _ => evalFun g) ihf (fun _ => ihg)) (by
      intro V _ _ v
      exact (evalV_comp f g (v 0)).symm)
  | prec f g ihf ihg => exact hprec f g ihf ihg

/-- Internal correctness of existential acceptance for a compiled program. -/
theorem existsValue_holds (hprec : PrecCase) (c : ScalarPRCode) (accepted : ℕ) :
    Holds (GraphRep.existsValue c.graphRep accepted)
      (fun V _ _ _ => ∃ t : V, evalV c t = (accepted : V)) :=
  holds_existsValue (graphRep_holds hprec c) accepted

end DiophantineConsistency.ModelRepBasic
