import DiophantineConsistency.ExecutableJonesCore
import DiophantineConsistency.WeightedExpressionDegree

/-! # Ring evaluation of the executable Jones syntax

`ExecutableJones.expression` evaluated in an arbitrary commutative ring:
the combiner of the evaluated free quantities, with the coding polynomials
`e`, `l`, `λ` as explicit finite sums. This is the ring-generic counterpart
of the integer evaluation lemmas of `ExecutableJones` and `JonesSyntax`; it
imports neither Foundation nor Mathlib's matrices, so model-internal modules
can apply it in the ring of differences of a model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelJonesSyntax
open ExecutableJones NinePolynomial

variable {R : Type*} [CommRing R]

theorem evalRing_subst {σ τ : Type*} (f : σ → Expr τ) (e : Expr σ) (v : τ → R) :
    (e.subst f).evalRing v = e.evalRing (fun i => (f i).evalRing v) := by
  induction e <;> simp_all [Expr.subst, Expr.evalRing]

theorem evalRing_removeInput (e : Expr (Fin 10)) (a : Fin 9 → R) :
    (JonesSyntax.removeInput e).evalRing a = e.evalRing (Fin.cons 1 a) := by
  rw [JonesSyntax.removeInput, evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Expr.evalRing]
  · simp [Expr.evalRing]

theorem evalRing_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → R) :
    (QuarticSyntax.sumExpressions es).evalRing v = (es.map (Expr.evalRing v)).sum := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.evalRing]
  | cons e es ih =>
    simp only [QuarticSyntax.sumExpressions, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

theorem evalRing_rangeSum {σ : Type*} (n : ℕ) (f : Fin n → Expr σ) (v : σ → R) :
    (rangeSum n f).evalRing v = ∑ i, (f i).evalRing v := by
  rw [rangeSum, evalRing_sumExpressions, List.map_ofFn, List.sum_ofFn]
  rfl

theorem evalRing_vectorSum {σ : Type*} (n : ℕ) (f : (Fin n → Fin 5) → Expr σ) (v : σ → R) :
    (vectorSum n f).evalRing v = ∑ k, (f k).evalRing v := by
  induction n with
  | zero =>
    simp only [vectorSum, Fintype.sum_unique]
    exact congrArg (fun k => (f k).evalRing v) (Subsingleton.elim _ _)
  | succ n ih =>
    simp only [vectorSum, evalRing_rangeSum, ih]
    calc
      _ = ∑ p : Fin 5 × (Fin n → Fin 5), (f (Fin.cons p.1 p.2)).evalRing v :=
        (Fintype.sum_prod_type (fun p : Fin 5 × (Fin n → Fin 5) =>
          (f (Fin.cons p.1 p.2)).evalRing v)).symm
      _ = _ := Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin 5)
        (fun p => (f (Fin.cons p.1 p.2)).evalRing v) (fun k => (f k).evalRing v) (fun _ => rfl)

/-- Reindex the bounded-vector enumeration by the degree-four star. -/
theorem sum_bounded_eq_codingStar {M : Type*} [AddCommMonoid M] (ν : ℕ)
    (f : (Fin (ν + 2) → ℕ) → M) :
    (∑ k : Fin (ν + 2) → Fin 5,
      if (∑ j, (k j : ℕ)) = 4 then f (fun j => (k j : ℕ)) else 0) =
      ∑ k ∈ codingStar ν 4, f k := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ j => (k j : ℕ))
  · intro k hk
    simpa [codingStar, Finset.mem_piAntidiag] using (Finset.mem_filter.1 hk).2
  · intro a _ b _ h
    funext j
    exact Fin.ext (congrFun h j)
  · intro k hk
    have hsum : ∑ j, k j = 4 := by simpa [codingStar, Finset.mem_piAntidiag] using hk
    have hle : ∀ j, k j ≤ 4 := fun j => by
      have := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    let b : Fin (ν + 2) → Fin 5 := fun j => ⟨k j, by have := hle j; omega⟩
    refine ⟨b, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsum⟩
  · intro k _
    rfl

theorem evalRing_starSum {σ : Type*} (ν : ℕ) (f : (Fin (ν + 2) → ℕ) → Expr σ) (v : σ → R) :
    (starSum ν f).evalRing v = ∑ k ∈ codingStar ν 4, (f k).evalRing v := by
  rw [starSum, evalRing_vectorSum]
  have h := sum_bounded_eq_codingStar ν (fun k => (f k).evalRing v)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Expr.evalRing]

theorem evalRing_eExpression {σ : Type*} {ν : ℕ} (e : Expr (Fin (ν + 1))) (z : ℕ)
    (B : Expr σ) (v : σ → R) :
    (eExpression e z B).evalRing v = ∑ k ∈ codingStar ν 4,
      ((z : R) + (pCoefficient e k : R)) * B.evalRing v ^ (codingLexp ν 4 - codingExpo ν 4 k) := by
  rw [eExpression, evalRing_starSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Expr.evalRing]

theorem evalRing_lExpression {σ : Type*} (B : Expr σ) (ν : ℕ) (v : σ → R) :
    (lExpression B ν).evalRing v = ∑ i ∈ Finset.range ν, B.evalRing v ^ (5 ^ (i + 1)) := by
  induction ν with
  | zero => simp [lExpression, Expr.evalRing]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [lExpression, Expr.evalRing]

theorem evalRing_lamExpression {σ : Type*} (ν : ℕ) (B : Expr σ) (v : σ → R) :
    (lamExpression ν B).evalRing v =
      ∑ i ∈ Finset.range (4 * codingLexp ν 4), B.evalRing v ^ i := by
  rw [lamExpression, evalRing_rangeSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-! ### The free-quantity record -/

/-- Apply a function to every free quantity. -/
def mapVars {A B : Type*} (f : A → B) (v : RingVars A) : RingVars B :=
  ⟨f v.R, f v.N, f v.b, f v.g, f v.G, f v.h, f v.s, f v.w, f v.φ, f v.i, f v.j⟩

section Vars
variable {σ : Type*} (v : RingVars (Expr σ)) (a : σ → R)

local notation "ev" => Expr.evalRing a

private theorem e_U : ev v.U = (mapVars ev v).U := by
  simp [RingVars.U, mapVars, Expr.evalRing]
private theorem e_Y : ev v.Y = (mapVars ev v).Y := by
  simp [RingVars.Y, mapVars, Expr.evalRing]
private theorem e_M : ev v.M = (mapVars ev v).M := by
  simp only [RingVars.M, Expr.evalRing, e_Y]; rfl
private theorem e_P : ev v.P = (mapVars ev v).P := by
  simp [RingVars.P, Expr.evalRing, e_M, e_U]
private theorem e_K : ev v.K = (mapVars ev v).K := by
  simp [RingVars.K, Expr.evalRing, e_P, mapVars]
private theorem e_A : ev v.A = (mapVars ev v).A := by
  simp [RingVars.A, Expr.evalRing, e_M, e_U]
private theorem e_B' : ev v.B' = (mapVars ev v).B' := by
  simp [RingVars.B', Expr.evalRing, mapVars]
private theorem e_W : ev v.W = (mapVars ev v).W := by
  simp [RingVars.W, Expr.evalRing, mapVars]
private theorem e_C : ev v.C = (mapVars ev v).C := by
  simp [RingVars.C, Expr.evalRing, e_B', e_W, mapVars]
private theorem e_J : ev v.J = (mapVars ev v).J := by
  simp [RingVars.J, Expr.evalRing, e_A]
private theorem e_Q : ev v.Q = (mapVars ev v).Q := by
  simp [RingVars.Q, Expr.evalRing, e_W, e_C]
private theorem e_D : ev v.D = (mapVars ev v).D := by
  simp [RingVars.D, Expr.evalRing, e_A, e_C]
private theorem e_E : ev v.E = (mapVars ev v).E := by
  simp [RingVars.E, Expr.evalRing, e_J, e_D, e_C, mapVars]
private theorem e_F : ev v.F = (mapVars ev v).F := by
  simp [RingVars.F, Expr.evalRing, e_A, e_E]
private theorem e_Gp : ev v.Gp = (mapVars ev v).Gp := by
  simp [RingVars.Gp, Expr.evalRing, e_A, e_F, e_C, e_D]
private theorem e_H : ev v.H = (mapVars ev v).H := by
  simp [RingVars.H, Expr.evalRing, e_B', e_C, mapVars]
private theorem e_I : ev v.I = (mapVars ev v).I := by
  simp [RingVars.I, Expr.evalRing, e_Gp, e_H]

theorem evalRing_rad0 : ev (v.rad 0) = (mapVars ev v).rad 0 := by
  change ev ((v.P ^ 2 - 1) * v.K ^ 2 + 1) = (mapVars ev v).rad 0
  simp [Expr.evalRing, e_P, e_K, RingVars.rad]
theorem evalRing_rad1 : ev (v.rad 1) = (mapVars ev v).rad 1 := by
  change ev (v.D * v.F * v.I) = (mapVars ev v).rad 1
  simp [Expr.evalRing, e_D, e_F, e_I, RingVars.rad]
theorem evalRing_wt0 : ev (v.wt 0) = (mapVars ev v).wt 0 := by
  change ev (v.rad 0 ^ 2 + 2) = (mapVars ev v).rad 0 ^ 2 + 2
  simp [Expr.evalRing, evalRing_rad0]
theorem evalRing_wt1 : ev (v.wt 1) = (mapVars ev v).wt 1 := by
  change ev (v.rad 1 ^ 2 + 2) = (mapVars ev v).rad 1 ^ 2 + 2
  simp [Expr.evalRing, evalRing_rad1]
theorem evalRing_dvsr : ev v.dvsr = (mapVars ev v).dvsr := by
  simp [RingVars.dvsr, Expr.evalRing, e_J, e_F]
theorem evalRing_dvnd : ev v.dvnd = (mapVars ev v).dvnd := by
  simp [RingVars.dvnd, Expr.evalRing, e_Q, e_F, e_J, e_H, e_C]
theorem evalRing_marg : ev v.marg = (mapVars ev v).marg := by
  simp [RingVars.marg, Expr.evalRing, e_K, e_C, e_Y, mapVars]

end Vars

theorem evalRing_value {σ : Type*} (A0 A1 V0 V1 n B C D : Expr σ) (a : σ → R) :
    (RefinedPair.value A0 A1 V0 V1 n B C D).evalRing a =
      RefinedPair.value (A0.evalRing a) (A1.evalRing a) (V0.evalRing a) (V1.evalRing a)
        (n.evalRing a) (B.evalRing a) (C.evalRing a) (D.evalRing a) := by
  simp [RefinedPair.value, Expr.evalRing]

/-- The input-carrying syntax evaluates to the combiner of the evaluated record. -/
theorem evalRing_withInput {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) (a : Fin 10 → R) :
    (withInput seed z y).evalRing a =
      let w := mapVars (Expr.evalRing a) (syntaxVars seed z y)
      RefinedPair.value (w.rad 0) (w.rad 1) (w.wt 0) (w.wt 1) (a 9) w.dvsr w.dvnd w.marg := by
  simp only [withInput, evalRing_value, Expr.evalRing_var, evalRing_rad0, evalRing_rad1, evalRing_wt0,
    evalRing_wt1, evalRing_dvsr, evalRing_dvnd, evalRing_marg]

theorem evalRing_rankCode {σ : Type*} (x z b e g l n q θ lam : Expr σ) (a : σ → R) :
    (rankCode x z b e g l n q θ lam).evalRing a =
      rankCode (x.evalRing a) (z.evalRing a) (b.evalRing a) (e.evalRing a) (g.evalRing a)
        (l.evalRing a) (n.evalRing a) (q.evalRing a) (θ.evalRing a) (lam.evalRing a) := by
  simp [rankCode, Expr.evalRing]

/-- The evaluated free quantities, with the coding polynomials as finite sums. -/
theorem mapVars_syntaxVars {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) (a : Fin 10 → R) :
    mapVars (Expr.evalRing a) (syntaxVars seed z y) =
      let b := a 0 * (y : R) + 1 + a 1
      let B := b ^ 5
      let q := B ^ codingL4 ν
      let n := q ^ 16
      let e := ∑ k ∈ codingStar ν 4,
        ((z : R) + (pCoefficient seed k : R)) * B ^ (codingLexp ν 4 - codingExpo ν 4 k)
      let l := ∑ i ∈ Finset.range ν, B ^ (5 ^ (i + 1))
      let lam := ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i
      let g := a 2 + 1
      let θ := B - 2 * (z : R)
      ⟨rankCode (a 0) (z : R) b e g l n q θ lam, n, b, g, 32 * b * B ^ (5 ^ ν),
        a 3 + 1, a 4 + 1, a 5 + 1, a 6, a 7 + 1, a 8 + 1⟩ := by
  simp only [syntaxVars, mapVars, evalRing_rankCode, evalRing_eExpression, evalRing_lExpression,
    evalRing_lamExpression, Expr.evalRing_pow, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_natCast, Nat.cast_ofNat, Nat.cast_one]

/-- **The nine-variable syntax in any commutative ring**: the combiner of
the evaluated free quantities at input `1`. -/
theorem evalRing_expression {ν : ℕ} (seed : Expr (Fin (ν + 1))) (bound : ℕ) (a : Fin 9 → R) :
    (ExecutableJones.expression seed bound).evalRing a =
      let w := mapVars (Expr.evalRing (Fin.cons 1 a : Fin 10 → R))
        (syntaxVars seed (indexZ seed bound) (indexY seed bound))
      RefinedPair.value (w.rad 0) (w.rad 1) (w.wt 0) (w.wt 1) (a 8) w.dvsr w.dvnd w.marg := by
  rw [ExecutableJones.expression, evalRing_removeInput, evalRing_withInput]
  rfl

end DiophantineConsistency.ModelJonesSyntax
