import DiophantineConsistency.ModelRepBasic
import DiophantineConsistency.NaturalExpressionSemiring

/-! # Internal correctness of the arithmetic graph constructors

This file extends `ModelRepBasic` with `ModelRep.Holds`/`ModelRep.GraphHolds`
for the arithmetic constructors used by the primitive-recursion trace and by the
bounded-universal certificate:

* natural expressions (`NatExpr.graphRep`, internally `NatExpr.evalSemiring`),
  and the natural relations `PellRepresentation.NaturalRelation.*`;
* divisibility and congruence (`ArithmeticRep.dvd`, `ArithmeticRep.modEq`,
  `PowerRepresentation.modEqGraphs`), internally `∣` and equality of residues
  `a % m = b % m` (Foundation's `%`, with `a % 0 = a`);
* truncated subtraction, remainder and quotient (`GraphRep.sub`, `GraphRep.mod`,
  `GraphRep.div`), internally Foundation's `-`, `%`, `/`.

Several source constructors use private helpers (`equalityGraphs`, `zeroAt`,
`compareTwo`, `dvdGraphs`). `Holds r Q` only inspects `r.witnessCount` and
`r.expression`, and `Rep.ofIff` changes neither, so each private helper is
matched by a public definition with the same syntax (`twoArgs`,
`equalityGraphsRep`); unification unfolds `Holds` to compare them. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepArith
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR ModelRepBasic
open AdaptiveEquationSyntax2011 (InternalZero)

/-! ### Ring-value helpers -/

section Helpers
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residual_ofNat {σ : Type*} (n : ℕ) (u : σ → V) :
    residual (OfNat.ofNat n : Expr σ) u = (n : DiffRing V) :=
  Expr.evalRing_ofNat _ n

theorem residual_zero {σ : Type*} (u : σ → V) : residual (0 : Expr σ) u = 0 :=
  (residual_ofNat 0 u).trans Nat.cast_zero

theorem ι_eq_zero_iff {a : V} : (ι a : DiffRing V) = 0 ↔ a = 0 := by
  constructor
  · intro h
    exact ι_injective (h.trans (map_zero (ι (V := V))).symm)
  · intro h
    rw [h]
    exact map_zero (ι (V := V))

/-- A natural witness block of length one for a linear quotient equation. -/
theorem exists_ι_quotient (z y x : V) :
    (∃ q : Fin 1 → V, ι z + ι y * ι (q 0) = (ι x : DiffRing V)) ↔
      ∃ q : V, z + y * q = x := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q 0, ι_injective (by rw [ι_add', ι_mul']; exact hq)⟩
  · rintro ⟨q, hq⟩
    refine ⟨fun _ => q, ?_⟩
    show ι z + ι y * ι q = ι x
    rw [← ι_mul', ← ι_add', hq]

/-- Internal truncated subtraction, by its two branches. -/
theorem sub_graph_iff (z x y : V) :
    (x = z + y ∨ (x ≤ y ∧ z = 0)) ↔ z = x - y := by
  constructor
  · rintro (h | ⟨h, rfl⟩)
    · rw [h, add_tsub_cancel_right]
    · exact (tsub_eq_zero_of_le h).symm
  · intro h
    rcases le_total y x with hyx | hxy
    · left
      rw [h, tsub_add_cancel_of_le hyx]
    · right
      exact ⟨hxy, by rw [h, tsub_eq_zero_of_le hxy]⟩

/-- Internal remainder, with Foundation's convention `x % 0 = x`. -/
theorem remainder_iff (z x y : V) :
    ((y = 0 ∨ z < y) ∧ ∃ q : V, z + y * q = x) ↔ z = x % y := by
  constructor
  · rintro ⟨hy, q, hq⟩
    rcases hy with h0 | hlt
    · subst h0
      rw [zero_mul, add_zero] at hq
      rw [mod_zero, hq]
    · rw [← hq, mod_add_mul' z q (lt_of_le_of_lt (Arithmetic.zero_le z) hlt), mod_eq_self_of_lt hlt]
  · intro hz
    subst hz
    refine ⟨?_, x / y, ?_⟩
    · rcases eq_zero_or_pos y with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (mod_lt x hpos)
    · rw [add_comm]
      exact div_add_mod x y

/-- Internal quotient, with Foundation's convention `x / 0 = 0`. -/
theorem division_iff (z x y : V) :
    ((y = 0 ∧ z = 0) ∨ (z * y ≤ x ∧ x < (z + 1) * y)) ↔ z = x / y := by
  rw [div_graph]
  constructor
  · rintro (⟨hy, hz⟩ | ⟨h1, h2⟩)
    · exact ⟨fun hpos => absurd hy hpos.ne', fun _ => hz⟩
    · refine ⟨fun _ => ⟨by rw [mul_comm]; exact h1, by rw [mul_comm]; exact h2⟩, fun hy => ?_⟩
      rw [hy, mul_zero] at h2
      exact absurd h2 (not_lt.mpr (Arithmetic.zero_le x))
  · rintro ⟨h1, h2⟩
    rcases eq_zero_or_pos y with hy | hpos
    · exact Or.inl ⟨hy, h2 hy⟩
    · obtain ⟨h3, h4⟩ := h1 hpos
      exact Or.inr ⟨by rw [mul_comm]; exact h3, by rw [mul_comm]; exact h4⟩

end Helpers

/-! ### Finite argument families -/

section Families
variable {σ : Type*}

/-- The two-argument family used by every binary graph substitution in the source. -/
def twoArgs {f g : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    ∀ i : Fin 2, GraphRep (![f, g] i) :=
  Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))

/-- The three-argument family of `PowerRepresentation.modEqGraphs`. -/
def threeArgs {f g h : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) :
    ∀ i : Fin 3, GraphRep (![f, g, h] i) :=
  Fin.cases r (Fin.cases s (Fin.cases t (fun i => Fin.elim0 i)))

/-- The model functions of a two-argument family. -/
abbrev pairFun (F G : ModelFun σ) : Fin 2 → ModelFun σ :=
  fun i => Fin.cases (motive := fun _ => ModelFun σ) F (fun _ => G) i

/-- The model functions of a three-argument family. -/
abbrev tripleFun (F G H : ModelFun σ) : Fin 3 → ModelFun σ :=
  fun i => Fin.cases (motive := fun _ => ModelFun σ) F
    (fun j => Fin.cases (motive := fun _ => ModelFun σ) G (fun _ => H) j) i

theorem holds_composeTwo {P : (Fin 2 → ℕ) → Prop} {f g : (σ → ℕ) → ℕ}
    {r : Rep (Fin 2) P} {Q : ModelPred (Fin 2)} {s : GraphRep f} {t : GraphRep g}
    {F G : ModelFun σ} (hr : Holds r Q) (hs : GraphHolds s F) (ht : GraphHolds t G) :
    Holds (Rep.compose r (twoArgs s t)) (fun V _ _ v => Q V (fun i => pairFun F G i V v)) := by
  refine holds_compose (G := pairFun F G) hr ?_
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact ht

theorem graphHolds_composeTwo {h : (Fin 2 → ℕ) → ℕ} {f g : (σ → ℕ) → ℕ}
    {r : GraphRep h} {H : ModelFun (Fin 2)} {s : GraphRep f} {t : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r H) (hs : GraphHolds s F) (ht : GraphHolds t G) :
    GraphHolds (GraphRep.compose r (twoArgs s t))
      (fun V _ _ v => H V (fun i => pairFun F G i V v)) := by
  refine graphHolds_compose (G := pairFun F G) hr ?_
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact ht

theorem holds_composeThree {P : (Fin 3 → ℕ) → Prop} {f g h : (σ → ℕ) → ℕ}
    {r : Rep (Fin 3) P} {Q : ModelPred (Fin 3)} {s : GraphRep f} {t : GraphRep g}
    {u : GraphRep h} {F G H : ModelFun σ} (hr : Holds r Q) (hs : GraphHolds s F)
    (ht : GraphHolds t G) (hu : GraphHolds u H) :
    Holds (Rep.compose r (threeArgs s t u))
      (fun V _ _ v => Q V (fun i => tripleFun F G H i V v)) := by
  refine holds_compose (G := tripleFun F G H) hr ?_
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact ht
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      exact hu

end Families

/-! ### Natural expressions and natural relations -/

section Natural
variable {σ : Type*}

/-- The compiled graph of a natural expression computes `evalSemiring`. -/
theorem graphHolds_natExpr :
    ∀ e : NatExpr σ, GraphHolds e.graphRep (fun V _ _ v => e.evalSemiring v)
  | .constant a => graphHolds_constant a
  | .var i => graphHolds_coordinate i
  | .add p q => graphHolds_add (graphHolds_natExpr p) (graphHolds_natExpr q)
  | .mul p q => graphHolds_mul (graphHolds_natExpr p) (graphHolds_natExpr q)

theorem holds_naturalEquality (p q : NatExpr σ) :
    Holds (PellRepresentation.NaturalRelation.equality p q)
      (fun V _ _ v => p.evalSemiring v = q.evalSemiring v) := by
  refine holds_congr _ ?_ (holds_compose (holds_equality (Expr.var (0 : Fin 2)) (Expr.var 1))
    (g := fun i => (![p, q] i).graphRep) (G := fun i V _ _ v => (![p, q] i).evalSemiring v)
    (fun i => graphHolds_natExpr (![p, q] i)))
  intro V _ _ v
  change ι (p.evalSemiring v) = ι (q.evalSemiring v) ↔ _
  exact ι_eq_ι

theorem holds_naturalLe (p q : NatExpr σ) :
    Holds (PellRepresentation.NaturalRelation.le p q)
      (fun V _ _ v => p.evalSemiring v ≤ q.evalSemiring v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl) (holds_compose (holds_le (0 : Fin 2) 1)
    (g := fun i => (![p, q] i).graphRep) (G := fun i V _ _ v => (![p, q] i).evalSemiring v)
    (fun i => graphHolds_natExpr (![p, q] i)))

theorem holds_naturalLt (p q : NatExpr σ) :
    Holds (PellRepresentation.NaturalRelation.lt p q)
      (fun V _ _ v => p.evalSemiring v < q.evalSemiring v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl) (holds_compose (holds_lt (0 : Fin 2) 1)
    (g := fun i => (![p, q] i).graphRep) (G := fun i V _ _ v => (![p, q] i).evalSemiring v)
    (fun i => graphHolds_natExpr (![p, q] i)))

end Natural

/-! ### Divisibility and congruence -/

section Divisibility
variable {σ : Type*}

theorem holds_dvd (a b : σ) :
    Holds (ArithmeticRep.dvd a b) (fun V _ _ v => v a ∣ v b) := by
  intro V _ _ v
  have key : ∀ w : Fin 1 → V,
      InternalZero (ArithmeticRep.dvd a b).expression (Sum.elim v w) ↔
        ι (v a) * ι (w 0) - ι (v b) = 0 :=
    fun w => internalZero_iff_residual _ _
  show v a ∣ v b ↔ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, (key _).mpr ?_⟩
    show ι (v a) * ι c - ι (v b) = 0
    rw [hc, ι_mul' (V := V), _root_.sub_self]
  · rintro ⟨(w : Fin 1 → V), hw⟩
    have h : ι (v a) * ι (w 0) - ι (v b) = 0 := (key w).mp hw
    refine ⟨w 0, ι_injective ?_⟩
    rw [ι_mul' (V := V)]
    exact (sub_eq_zero.mp h).symm

/-- Congruence is equality of internal residues, also for modulus zero. -/
theorem holds_modEq (a b m : σ) :
    Holds (ArithmeticRep.modEq a b m) (fun V _ _ v => v a % v m = v b % v m) := by
  intro V _ _ v
  have key : ∀ w : Fin 2 → V,
      InternalZero (ArithmeticRep.modEq a b m).expression (Sum.elim v w) ↔
        (ι (v a) + ι (v m) * ι (w 0)) - (ι (v b) + ι (v m) * ι (w 1)) = 0 :=
    fun w => internalZero_iff_residual _ _
  show v a % v m = v b % v m ↔ _
  constructor
  · intro h
    refine ⟨![v b / v m, v a / v m], (key _).mpr ?_⟩
    show (ι (v a) + ι (v m) * ι (v b / v m)) - (ι (v b) + ι (v m) * ι (v a / v m)) = 0
    have ha := div_add_mod (v a) (v m)
    have hb := div_add_mod (v b) (v m)
    have e : v a + v m * (v b / v m) = v b + v m * (v a / v m) := by
      calc v a + v m * (v b / v m)
          = (v m * (v a / v m) + v a % v m) + v m * (v b / v m) := by rw [ha]
        _ = (v m * (v b / v m) + v b % v m) + v m * (v a / v m) := by rw [h]; ring
        _ = v b + v m * (v a / v m) := by rw [hb]
    rw [← ι_mul' (V := V), ← ι_mul' (V := V), ← ι_add' (V := V), ← ι_add' (V := V), e,
      _root_.sub_self]
  · rintro ⟨(w : Fin 2 → V), hw⟩
    have h : (ι (v a) + ι (v m) * ι (w 0)) - (ι (v b) + ι (v m) * ι (w 1)) = 0 :=
      (key w).mp hw
    have e : v a + v m * w 0 = v b + v m * w 1 := by
      apply ι_injective
      rw [ι_add' (V := V), ι_add' (V := V), ι_mul' (V := V), ι_mul' (V := V)]
      exact sub_eq_zero.mp h
    rcases eq_zero_or_pos (v m) with h0 | hpos
    · simp only [h0, zero_mul, add_zero] at e
      rw [e]
    · have he := congrArg (· % v m) e
      simpa only [mod_add_mul' _ _ hpos] using he

theorem holds_naturalDvd (p q : NatExpr σ) :
    Holds (PellRepresentation.NaturalRelation.dvd p q)
      (fun V _ _ v => p.evalSemiring v ∣ q.evalSemiring v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl) (holds_compose (holds_dvd (0 : Fin 2) 1)
    (g := fun i => (![p, q] i).graphRep) (G := fun i V _ _ v => (![p, q] i).evalSemiring v)
    (fun i => graphHolds_natExpr (![p, q] i)))

theorem holds_naturalModEq (p q modulus : NatExpr σ) :
    Holds (PellRepresentation.NaturalRelation.modEq p q modulus)
      (fun V _ _ v => p.evalSemiring v % modulus.evalSemiring v =
        q.evalSemiring v % modulus.evalSemiring v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl) (holds_compose (holds_modEq (0 : Fin 3) 1 2)
    (g := fun i => (![p, q, modulus] i).graphRep)
    (G := fun i V _ _ v => (![p, q, modulus] i).evalSemiring v)
    (fun i => graphHolds_natExpr (![p, q, modulus] i)))

/-- Divisibility of two represented functions (the shape of the private
`BoundedForallRepresentation.dvdGraphs`). -/
theorem holds_dvdGraphs {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    Holds (Rep.compose (ArithmeticRep.dvd (0 : Fin 2) 1) (twoArgs r s))
      (fun V _ _ v => F V v ∣ G V v) :=
  holds_composeTwo (holds_dvd (0 : Fin 2) 1) hr hs

/-- `PowerRepresentation.modEqGraphs`: congruence of represented functions. -/
theorem holds_modEqGraphs {f g h : (σ → ℕ) → ℕ} {rf : GraphRep f} {rg : GraphRep g}
    {rh : GraphRep h} {F G H : ModelFun σ}
    (hf : GraphHolds rf F) (hg : GraphHolds rg G) (hh : GraphHolds rh H) :
    Holds (PowerRepresentation.modEqGraphs rf rg rh)
      (fun V _ _ v => F V v % H V v = G V v % H V v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_composeThree (holds_modEq (0 : Fin 3) 1 2) hf hg hh)

end Divisibility

/-! ### Equality of two represented functions -/

section Equality
variable {σ : Type*}

/-- The same syntax (and the same type) as the private
`ScalarPRRepresentation.equalityGraphs`. -/
def equalityGraphsRep {f g : (σ → ℕ) → ℕ} (r : GraphRep f) (s : GraphRep g) :
    Rep σ (fun v => f v = g v) :=
  (Rep.compose (PellRepresentation.NaturalRelation.equality
    (.var (0 : Fin 2)) (.var 1)) (twoArgs r s)).ofIff (fun _ => Iff.rfl)

theorem holds_equalityGraphsRep {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    Holds (equalityGraphsRep r s) (fun V _ _ v => F V v = G V v) :=
  holds_congr _ (by intro V _ _ v; exact Iff.rfl)
    (holds_composeTwo (holds_naturalEquality (.var (0 : Fin 2)) (.var 1)) hr hs)

end Equality

/-! ### Subtraction, remainder and quotient -/

section Division
variable {σ : Type*}

/-- `v i = 0`, the shape of the private `RemainderRepresentation.zeroAt`. -/
theorem holds_zeroAt (i : σ) :
    Holds (Rep.equality (Expr.var i) (0 : Expr σ)) (fun V _ _ v => v i = 0) := by
  refine holds_congr _ ?_ (holds_equality (Expr.var i) (0 : Expr σ))
  intro V _ _ v
  change ι (v i) = residual (0 : Expr σ) v ↔ v i = 0
  rw [residual_zero]
  exact ι_eq_zero_iff

theorem graphHolds_subCoordinates :
    GraphHolds GraphRep.subCoordinates (fun V _ _ v => v 0 - v 1) := by
  refine holds_congr _ ?_ (holds_disjunction
    (holds_equality (Expr.var (some (0 : Fin 2)))
      (Expr.var none + Expr.var (some (1 : Fin 2))))
    (holds_conjunction (holds_le (some (0 : Fin 2)) (some (1 : Fin 2)))
      (holds_equality (Expr.var (none : Option (Fin 2))) 0)))
  intro V _ _ v
  change (ι (v (some 0)) = ι (v none) + ι (v (some 1)) ∨
      (v (some 0) ≤ v (some 1) ∧ ι (v none) = residual (0 : Expr (Option (Fin 2))) v)) ↔
    v none = v (some 0) - v (some 1)
  rw [residual_zero, ι_eq_zero_iff, ← ι_add' (V := V), ι_eq_ι (V := V)]
  exact sub_graph_iff _ _ _

theorem graphHolds_sub {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.sub s) (fun V _ _ v => F V v - G V v) :=
  graphHolds_composeTwo graphHolds_subCoordinates hr hs

theorem graphHolds_modCoordinates :
    GraphHolds GraphRep.modCoordinates (fun V _ _ v => v 0 % v 1) := by
  refine holds_congr _ ?_ (holds_conjunction
    (holds_disjunction (holds_zeroAt (some (1 : Fin 2)))
      (holds_lt (none : Option (Fin 2)) (some 1)))
    (holds_existsBlock (holds_equality
      (Expr.var (Sum.inl none : Option (Fin 2) ⊕ Fin 1) +
        Expr.var (Sum.inl (some 1) : Option (Fin 2) ⊕ Fin 1) *
          Expr.var (Sum.inr 0 : Option (Fin 2) ⊕ Fin 1))
      (Expr.var (Sum.inl (some 0) : Option (Fin 2) ⊕ Fin 1)))))
  intro V _ _ v
  change ((v (some 1) = 0 ∨ v none < v (some 1)) ∧
      ∃ q : Fin 1 → V, ι (v none) + ι (v (some 1)) * ι (q 0) = ι (v (some 0))) ↔
    v none = v (some 0) % v (some 1)
  rw [exists_ι_quotient]
  exact remainder_iff _ _ _

theorem graphHolds_mod {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.mod s) (fun V _ _ v => F V v % G V v) :=
  graphHolds_composeTwo graphHolds_modCoordinates hr hs

theorem graphHolds_divCoordinates :
    GraphHolds GraphRep.divCoordinates (fun V _ _ v => v 0 / v 1) := by
  refine holds_congr _ ?_ (holds_disjunction
    (holds_conjunction (holds_zeroAt (some (1 : Fin 2))) (holds_zeroAt (none : Option (Fin 2))))
    (holds_conjunction
      (holds_composeTwo (holds_le (0 : Fin 2) 1)
        (graphHolds_mul (graphHolds_coordinate (none : Option (Fin 2)))
          (graphHolds_coordinate (some (1 : Fin 2))))
        (graphHolds_coordinate (some (0 : Fin 2))))
      (holds_composeTwo (holds_lt (0 : Fin 2) 1)
        (graphHolds_coordinate (some (0 : Fin 2)))
        (graphHolds_mul
          (graphHolds_add (graphHolds_coordinate (none : Option (Fin 2))) (graphHolds_constant 1))
          (graphHolds_coordinate (some (1 : Fin 2)))))))
  intro V _ _ v
  change ((v (some 1) = 0 ∧ v none = 0) ∨
      (v none * v (some 1) ≤ v (some 0) ∧
        v (some 0) < (v none + ((1 : ℕ) : V)) * v (some 1))) ↔
    v none = v (some 0) / v (some 1)
  rw [Nat.cast_one]
  exact division_iff _ _ _

theorem graphHolds_div {f g : (σ → ℕ) → ℕ} {r : GraphRep f} {s : GraphRep g}
    {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.div s) (fun V _ _ v => F V v / G V v) :=
  graphHolds_composeTwo graphHolds_divCoordinates hr hs

end Division

end DiophantineConsistency.ModelRepArith
