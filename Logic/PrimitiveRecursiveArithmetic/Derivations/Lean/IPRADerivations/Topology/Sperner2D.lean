import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Topology.CrossingParity
import IPRADerivations.Core.LinearCombination

/-!
# The two-dimensional cubical Sperner parity lemma (`dimension_invariance_ipra`, `thm:sperner`)

Packet: `topology/dimension_invariance_ipra`, Section "A complete finite cubical Sperner
argument". For `d = 2` the Kuhn simplices of the grid `{0, …, N}²` are the two triangles of
each cell `(a, b)`, `a, b < N`:

* `(a, b), (a + 1, b), (a + 1, b + 1)` (permutation `(1, 2)`), and
* `(a, b), (a, b + 1), (a + 1, b + 1)` (permutation `(2, 1)`).

The labelling is an arbitrary ternary primitive recursive symbol `f(x, y, p)` with a runtime
parameter `p`. Its colour classes are `{0}`, `{1}` and `{≥ 2}`, with indicator bits
`b0 = [f = 0]`, `b1 = [f = 1]`, `b2 = 1 ∸ (b0 + b1)`, so every labelling by `0, 1, 2` is
covered and no range hypothesis is needed. A triangle is *full* when its vertices carry the
three classes; its indicator is the permanent of the bit matrix. An edge is a *door* when its
ends carry the classes `0` and `1`.

The grid size `N` and the parameter `p` are variables of the object theory.

* `triangle_doors`: for a triangle, `doors = full + 2 E` is a polynomial identity that uses
  only the row sums `b0 + b1 + b2 = 1`, so no case distinction on the colours is made;
* `boundary_doors`: for **every** labelling, the number of full triangles plus the number of
  doors on the four sides of the square is even. Interior edges cancel by telescoping
  (`straddle2`), once along the rows and once along the columns;
* `sperner_2d`: if `f(0, y) = 0`, `f(N, y) ≠ 0`, `f(x, 0) ≤ 1` and `f(x, N) ≠ 1` for all
  `x, y ≤ N` (the packet's admissibility conditions `eq:lower`, `eq:upper` with coordinates
  numbered from zero), then the number of full triangles is odd;
* `sperner_2d_pos`: in that case the number of full triangles is not zero.

The hypotheses of `sperner_2d` are literal bounded universal formulas and stay outside every
induction formula; the inductions are on equations between primitive recursive terms.

The general-dimension parity lemma, with `d` a variable or an external parameter, is not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.Sperner2D

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum2_zero_of_bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Two-parameter sums: additivity, parity and telescoping -/

theorem inst3_add (f g : PTm 3) (i p q : PTm n) :
    inst3 (f + g) i p q = inst3 f i p q + inst3 g i p q := by simp [inst3]

theorem inst3_mul (f g : PTm 3) (i p q : PTm n) :
    inst3 (f * g) i p q = inst3 f i p q * inst3 g i p q := by simp [inst3]

theorem inst3_two (i p q : PTm n) : inst3 (two : PTm 3) i p q = two := by simp [inst3]

/-- `g(i + 1, p, q)`. -/
def sh0 (g : PTm 3) : PTm 3 := Syn.subst ![succ (var 0), var 1, var 2] g

/-- `g(i, p + 1, q)`. -/
def sh1 (g : PTm 3) : PTm 3 := Syn.subst ![var 0, succ (var 1), var 2] g

theorem inst3_sh0 (g : PTm 3) (i p q : PTm n) : inst3 (sh0 g) i p q = inst3 g (succ i) p q := by
  simp only [inst3, sh0, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem inst3_sh1 (g : PTm 3) (i p q : PTm n) : inst3 (sh1 g) i p q = inst3 g i (succ p) q := by
  simp only [inst3, sh1, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev addF (f g : PTm 3) : Fm PTm 3 :=
  ap3 (sum2F (f + g)) (var 0) (var 1) (var 2) ≐
    ap3 (sum2F f) (var 0) (var 1) (var 2) + ap3 (sum2F g) (var 0) (var 1) (var 2)

private theorem sum2_add₀ (f g : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] addF f g := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      inst_two, ConciseIPRA.PTm.subst_zero]
    refine withEq (sum2_zero (Γ := []) (f + g) (var 0 : PTm 2) (var 1)) fun e₀ =>
      withEq (sum2_zero (Γ := []) f (var 0 : PTm 2) (var 1)) fun e₁ =>
      withEq (sum2_zero (Γ := []) g (var 0 : PTm 2) (var 1)) fun e₂ => ?_
    ipra_lc e₀ - e₁ - e₂
  · simp only [Fm.subst_eq, PTm.subst_add, subst_ap3, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have s₀ := sum2_succ (Γ := [addF f g]) (f + g) (var 0) (var 1) (var 2)
    rw [inst3_add] at s₀
    refine withEq Prf.hyp0 fun e₁ => withEq s₀ fun e₀ =>
      withEq (sum2_succ f (var 0) (var 1) (var 2)) fun e₂ =>
      withEq (sum2_succ g (var 0) (var 1) (var 2)) fun e₃ => ?_
    ipra_lc e₀ - e₂ - e₃ + e₁

/-- `∑ (f + g) = ∑ f + ∑ g`. -/
theorem sum2_add (f g : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F (f + g)) N p q ≐ ap3 (sum2F f) N p q + ap3 (sum2F g) N p q := by
  have h := inst (Γ := Γ) (sum2_add₀ f g) (![N, p, q] : Fin 3 → PTm n)
  simpa using h

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev evenF (t : PTm 3) : Fm PTm 3 := par (ap3 (sum2F t) (var 0) (var 1) (var 2)) ≐ zero

private theorem sum2_even₀ (t : PTm 3)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i p q : PTm m), Δ ⊢[PRAAx] par (inst3 t i p q) ≐ zero) :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] evenF t := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap1, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero]
    exact (congrAp1 parF (sum2_zero _ _ _)).eqTrans par_zero
  · simp only [Fm.subst_eq, subst_ap1, subst_ap3, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (congrAp1 parF (sum2_succ t (var 0) (var 1) (var 2))).eqTrans
      ((par_add_even _ (h _ _ _)).eqTrans Prf.hyp0)

/-- A sum of terms that are even at all arguments is even. -/
theorem sum2_even (t : PTm 3)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i p q : PTm m), Δ ⊢[PRAAx] par (inst3 t i p q) ≐ zero)
    (N p q : PTm n) : Γ ⊢[PRAAx] par (ap3 (sum2F t) N p q) ≐ zero := by
  have i := inst (Γ := Γ) (sum2_even₀ t h) (![N, p, q] : Fin 3 → PTm n)
  simpa using i

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev teleF (h : PTm 3) : Fm PTm 3 :=
  par (ap3 (sum2F (h + sh0 h)) (var 0) (var 1) (var 2) +
    (inst3 h zero (var 1) (var 2) + inst3 h (var 0) (var 1) (var 2))) ≐ zero

private theorem tele₀ (h : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] teleF h := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap1, subst_ap3, PTm.subst_add, subst_inst3, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have e : ([] : List (Fm PTm 2)) ⊢[PRAAx]
        ap3 (sum2F (h + sh0 h)) zero (var 0) (var 1) +
          (inst3 h zero (var 0) (var 1) + inst3 h zero (var 0) (var 1)) ≐
        two * inst3 h zero (var 0) (var 1) := by
      ipra_lc natEq (sum2_zero (Γ := ([] : List (Fm PTm 2))) (h + sh0 h) (var 0) (var 1))
    exact (congrAp1 parF e).eqTrans (par_double _)
  · simp only [Fm.subst_eq, subst_ap1, subst_ap3, PTm.subst_add, subst_inst3, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have s := sum2_succ (Γ := [teleF h]) (h + sh0 h) (var 0) (var 1) (var 2)
    rw [inst3_add, inst3_sh0] at s
    have e : [teleF h] ⊢[PRAAx]
        ap3 (sum2F (h + sh0 h)) (succ (var 0)) (var 1) (var 2) +
          (inst3 h zero (var 1) (var 2) + inst3 h (succ (var 0)) (var 1) (var 2)) ≐
        (ap3 (sum2F (h + sh0 h)) (var 0) (var 1) (var 2) +
          (inst3 h zero (var 1) (var 2) + inst3 h (var 0) (var 1) (var 2))) +
          two * inst3 h (succ (var 0)) (var 1) (var 2) := by
      ipra_lc natEq s
    exact (congrAp1 parF e).eqTrans ((par_add_two _ _).eqTrans Prf.hyp0)

/-- Telescoping modulo two: `par (∑_{i<N} (h(i) + h(i + 1)) + (h(0) + h(N))) = 0`. -/
theorem straddle2 (h : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] par (ap3 (sum2F (h + sh0 h)) N p q + (inst3 h zero p q + inst3 h N p q)) ≐ zero := by
  have i := inst (Γ := Γ) (tele₀ h) (![N, p, q] : Fin 3 → PTm n)
  simpa [subst_inst3] using i

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev sh1F (g : PTm 3) : Fm PTm 3 :=
  ap3 (sum2F (sh1 g)) (var 0) (var 1) (var 2) ≐ ap3 (sum2F g) (var 0) (succ (var 1)) (var 2)

private theorem sum2_sh1₀ (g : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] sh1F g := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (sum2_zero _ _ _).eqTrans (sum2_zero _ _ _).eqSymm
  · simp only [Fm.subst_eq, subst_ap3, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (sum2_succ _ _ _ _).eqTrans (.eqTrans ?_ (sum2_succ _ _ _ _).eqSymm)
    rw [inst3_sh1]
    exact congrAdd Prf.hyp0 (.eqRefl _)

/-- A sum of a body shifted in its first parameter is the sum at the shifted parameter. -/
theorem sum2_sh1 (g : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F (sh1 g)) N p q ≐ ap3 (sum2F g) N (succ p) q := by
  have i := inst (Γ := Γ) (sum2_sh1₀ g) (![N, p, q] : Fin 3 → PTm n)
  simpa using i

theorem par_one : Γ ⊢[PRAAx] par (one : PTm n) ≐ one :=
  (par_succ zero).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _))

/-! ## The colour bits of a value -/

theorem zero_ne_one (φ : Fm PTm n) (h : Γ ⊢[PRAAx] (zero : PTm n) ≐ one) : Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ h.eqSymm

/-- For `c = 0`: `[c = 0] = 1` and `[c = 1] = 0`. -/
theorem bits_of_zero {c : PTm n} (h : Γ ⊢[PRAAx] c ≐ zero) :
    Γ ⊢[PRAAx] (eqb c zero ≐ one) ⋏ (eqb c one ≐ zero) :=
  .andI (eqb_of_eq h) (eqb_of_ne (.impI (zero_ne_one _ (h.wk.eqSymm.eqTrans Prf.hyp0))))

/-- `[c = 0] + [c = 1] ≤ 1`. -/
theorem bits_le (c : PTm n) : Γ ⊢[PRAAx] le (eqb c zero + eqb c one) one := by
  refine .orE (eq_or_ne c zero) ?_ ?_
  · have hb := bits_of_zero (Γ := (c ≐ zero) :: Γ) Prf.hyp0
    exact le_congr ((congrAdd (.andE₁ hb) (.andE₂ hb)).eqTrans (add_zero _)).eqSymm (.eqRefl _)
      (le_refl one)
  · have h0 : (neg (c ≐ zero) :: Γ) ⊢[PRAAx] eqb c zero ≐ zero := eqb_of_ne Prf.hyp0
    refine .orE (eq_or_ne c one) ?_ ?_
    · exact le_congr ((congrAdd h0.wk (eqb_of_eq Prf.hyp0)).eqTrans (zero_add _)).eqSymm (.eqRefl _)
        (le_refl one)
    · exact le_congr ((congrAdd h0.wk (eqb_of_ne Prf.hyp0)).eqTrans (zero_add _)).eqSymm (.eqRefl _)
        (zero_le one)

/-- For `c ≤ 1`: `[c = 0] + [c = 1] = 1`. -/
theorem bits_of_le_one {c : PTm n} (h : Γ ⊢[PRAAx] le c one) :
    Γ ⊢[PRAAx] eqb c zero + eqb c one ≐ one := by
  refine .orE (eq_or_ne c zero) ?_ ?_
  · have hb := bits_of_zero (Γ := (c ≐ zero) :: Γ) Prf.hyp0
    exact (congrAdd (.andE₁ hb) (.andE₂ hb)).eqTrans (add_zero _)
  · have h0 : (neg (c ≐ zero) :: Γ) ⊢[PRAAx] eqb c zero ≐ zero := eqb_of_ne Prf.hyp0
    have h1 : (neg (c ≐ zero) :: Γ) ⊢[PRAAx] c ≐ one := by
      refine .orE (lt_or_eq_of_le h.wk) ?_ Prf.hyp0
      have hc : (lt c one :: neg (c ≐ zero) :: Γ) ⊢[PRAAx] c ≐ zero :=
        (monus_zero c).eqSymm.eqTrans ((succ_monus_succ c zero).eqSymm.eqTrans Prf.hyp0)
      exact .botE _ (.impE Prf.hyp1 hc)
    exact (congrAdd h0 (eqb_of_eq h1)).eqTrans (zero_add _)

/-! ## Doors and full triangles, as polynomials in the bits -/

/-- The door indicator of an edge whose ends have the bits `(x0, x1)` and `(y0, y1)`. -/
def drT (x0 x1 y0 y1 : PTm n) : PTm n := x0 * y1 + x1 * y0

/-- The permanent of the bit matrix of three vertices: the full-triangle indicator. -/
def permT (x0 x1 x2 y0 y1 y2 z0 z1 z2 : PTm n) : PTm n :=
  x0 * y1 * z2 + x0 * y2 * z1 + x1 * y0 * z2 + x1 * y2 * z0 + x2 * y0 * z1 + x2 * y1 * z0

/-- The indicator that the three vertices carry the classes `0` and `1` only, and both. -/
def twoT (x0 x1 y0 y1 z0 z1 : PTm n) : PTm n :=
  x0 * y0 * z1 + x0 * y1 * z0 + x1 * y0 * z0 + x0 * y1 * z1 + x1 * y0 * z1 + x1 * y1 * z0

/-- The doors of a triangle: `doors = full + 2 E`. Only the three row sums are used. -/
theorem triangle_doors {x0 x1 x2 y0 y1 y2 z0 z1 z2 : PTm n}
    (hx : Γ ⊢[PRAAx] x0 + x1 + x2 ≐ one) (hy : Γ ⊢[PRAAx] y0 + y1 + y2 ≐ one)
    (hz : Γ ⊢[PRAAx] z0 + z1 + z2 ≐ one) :
    Γ ⊢[PRAAx] drT x0 x1 y0 y1 + drT y0 y1 z0 z1 + drT x0 x1 z0 z1 ≐
      permT x0 x1 x2 y0 y1 y2 z0 z1 z2 + two * twoT x0 x1 y0 y1 z0 z1 := by
  ipra_lc [drT, permT, twoT] (-(𝔞 x0 * 𝔞 y1 + 𝔞 x1 * 𝔞 y0)) * natEq hz + (-(𝔞 y0 * 𝔞 z1 + 𝔞 y1 * 𝔞 z0)) * natEq hx +
    (-(𝔞 x0 * 𝔞 z1 + 𝔞 x1 * 𝔞 z0)) * natEq hy

/-- A grid cell with corners `P`, `Q` (right of `P`), `S` (above `P`) and `R` (opposite `P`):
the full triangles `PQR`, `PSR` and the doors on the four sides have an even total. -/
theorem cell_even {p0 p1 p2 q0 q1 q2 r0 r1 r2 s0 s1 s2 : PTm n}
    (hp : Γ ⊢[PRAAx] p0 + p1 + p2 ≐ one) (hq : Γ ⊢[PRAAx] q0 + q1 + q2 ≐ one)
    (hr : Γ ⊢[PRAAx] r0 + r1 + r2 ≐ one) (hs : Γ ⊢[PRAAx] s0 + s1 + s2 ≐ one) :
    Γ ⊢[PRAAx] par ((permT p0 p1 p2 q0 q1 q2 r0 r1 r2 + permT p0 p1 p2 s0 s1 s2 r0 r1 r2) +
      ((drT p0 p1 q0 q1 + drT s0 s1 r0 r1) + (drT p0 p1 s0 s1 + drT q0 q1 r0 r1))) ≐ zero := by
  have e : Γ ⊢[PRAAx]
      ((permT p0 p1 p2 q0 q1 q2 r0 r1 r2 + permT p0 p1 p2 s0 s1 s2 r0 r1 r2) +
        ((drT p0 p1 q0 q1 + drT s0 s1 r0 r1) + (drT p0 p1 s0 s1 + drT q0 q1 r0 r1))) +
        two * (twoT p0 p1 q0 q1 r0 r1 + twoT p0 p1 s0 s1 r0 r1) ≐
      two * (((drT p0 p1 q0 q1 + drT s0 s1 r0 r1) + (drT p0 p1 s0 s1 + drT q0 q1 r0 r1)) +
        drT p0 p1 r0 r1) := by
    ipra_lc [drT, permT, twoT] (-1) * natEq (triangle_doors hp hq hr) + (-1) * natEq (triangle_doors hp hs hr)
  exact (par_add_two _ _).eqSymm.eqTrans ((congrAp1 parF e).eqTrans (par_double _))

/-! ## The labelling -/

variable (f : PR 3)

/-- `[f(X, Y, P) = 0]`. -/
def b0 (X Y P : PTm n) : PTm n := eqb (ap3 f X Y P) zero
/-- `[f(X, Y, P) = 1]`. -/
def b1 (X Y P : PTm n) : PTm n := eqb (ap3 f X Y P) one
/-- `[f(X, Y, P) ≥ 2]`. -/
def b2 (X Y P : PTm n) : PTm n := monus one (b0 f X Y P + b1 f X Y P)

@[simp] theorem subst_b0 {m : ℕ} (σ : Fin n → PTm m) (X Y P : PTm n) :
    Syn.subst σ (b0 f X Y P) = b0 f (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ P) := by
  simp [b0]

@[simp] theorem subst_b1 {m : ℕ} (σ : Fin n → PTm m) (X Y P : PTm n) :
    Syn.subst σ (b1 f X Y P) = b1 f (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ P) := by
  simp [b1]

@[simp] theorem subst_b2 {m : ℕ} (σ : Fin n → PTm m) (X Y P : PTm n) :
    Syn.subst σ (b2 f X Y P) = b2 f (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ P) := by
  simp [b2]

/-- The three bits of a vertex add up to one. -/
theorem bits_sum (X Y P : PTm n) : Γ ⊢[PRAAx] b0 f X Y P + b1 f X Y P + b2 f X Y P ≐ one :=
  (eq_add_of_le (bits_le (ap3 f X Y P))).eqSymm

/-- The door indicator of the edge `(X₁, Y₁) – (X₂, Y₂)`. -/
def dr (X₁ Y₁ X₂ Y₂ P : PTm n) : PTm n :=
  drT (b0 f X₁ Y₁ P) (b1 f X₁ Y₁ P) (b0 f X₂ Y₂ P) (b1 f X₂ Y₂ P)

/-- The full-triangle indicator of the triangle with the three given vertices. -/
def full (X₁ Y₁ X₂ Y₂ X₃ Y₃ P : PTm n) : PTm n :=
  permT (b0 f X₁ Y₁ P) (b1 f X₁ Y₁ P) (b2 f X₁ Y₁ P) (b0 f X₂ Y₂ P) (b1 f X₂ Y₂ P) (b2 f X₂ Y₂ P)
    (b0 f X₃ Y₃ P) (b1 f X₃ Y₃ P) (b2 f X₃ Y₃ P)

@[simp] theorem subst_dr {m : ℕ} (σ : Fin n → PTm m) (X₁ Y₁ X₂ Y₂ P : PTm n) :
    Syn.subst σ (dr f X₁ Y₁ X₂ Y₂ P) =
      dr f (Syn.subst σ X₁) (Syn.subst σ Y₁) (Syn.subst σ X₂) (Syn.subst σ Y₂) (Syn.subst σ P) := by
  simp [dr, drT]

@[simp] theorem subst_full {m : ℕ} (σ : Fin n → PTm m) (X₁ Y₁ X₂ Y₂ X₃ Y₃ P : PTm n) :
    Syn.subst σ (full f X₁ Y₁ X₂ Y₂ X₃ Y₃ P) =
      full f (Syn.subst σ X₁) (Syn.subst σ Y₁) (Syn.subst σ X₂) (Syn.subst σ Y₂) (Syn.subst σ X₃)
        (Syn.subst σ Y₃) (Syn.subst σ P) := by
  simp [full, permT]

/-- An edge whose ends both lack the class `1` is not a door. -/
theorem dr_zero_of_b1 {X₁ Y₁ X₂ Y₂ P : PTm n} (h₁ : Γ ⊢[PRAAx] b1 f X₁ Y₁ P ≐ zero)
    (h₂ : Γ ⊢[PRAAx] b1 f X₂ Y₂ P ≐ zero) : Γ ⊢[PRAAx] dr f X₁ Y₁ X₂ Y₂ P ≐ zero := by
  ipra_lc [dr, drT] (𝔞 (b0 f X₁ Y₁ P)) * natEq h₂ + (𝔞 (b0 f X₂ Y₂ P)) * natEq h₁

/-- An edge whose ends both lack the class `0` is not a door. -/
theorem dr_zero_of_b0 {X₁ Y₁ X₂ Y₂ P : PTm n} (h₁ : Γ ⊢[PRAAx] b0 f X₁ Y₁ P ≐ zero)
    (h₂ : Γ ⊢[PRAAx] b0 f X₂ Y₂ P ≐ zero) : Γ ⊢[PRAAx] dr f X₁ Y₁ X₂ Y₂ P ≐ zero := by
  ipra_lc [dr, drT] (𝔞 (b1 f X₂ Y₂ P)) * natEq h₁ + (𝔞 (b1 f X₁ Y₁ P)) * natEq h₂

/-- On an edge whose ends carry the classes `0`, `1` only, the door indicator is the sum of the
`1`-bits of the ends modulo two. -/
theorem edge_of_two_classes {X₁ Y₁ X₂ Y₂ P : PTm n}
    (h₁ : Γ ⊢[PRAAx] b0 f X₁ Y₁ P + b1 f X₁ Y₁ P ≐ one)
    (h₂ : Γ ⊢[PRAAx] b0 f X₂ Y₂ P + b1 f X₂ Y₂ P ≐ one) :
    Γ ⊢[PRAAx] dr f X₁ Y₁ X₂ Y₂ P + two * (b1 f X₁ Y₁ P * b1 f X₂ Y₂ P) ≐
      b1 f X₁ Y₁ P + b1 f X₂ Y₂ P := by
  ipra_lc [dr, drT] (𝔞 (b1 f X₂ Y₂ P)) * natEq h₁ + (𝔞 (b1 f X₁ Y₁ P)) * natEq h₂

/-! ## The cells of a row

Variables of the bodies: `0 = b` (the summation index), `1 = a`, `2 = p`. -/

/-- The full triangles of the cell `(a, b)`. -/
def cellB : PTm 3 :=
  full f (var 1) (var 0) (succ (var 1)) (var 0) (succ (var 1)) (succ (var 0)) (var 2) +
    full f (var 1) (var 0) (var 1) (succ (var 0)) (succ (var 1)) (succ (var 0)) (var 2)

/-- The horizontal edge `(a, b) – (a + 1, b)`. -/
def dhB : PTm 3 := dr f (var 1) (var 0) (succ (var 1)) (var 0) (var 2)

/-- The vertical edge `(a, b) – (a, b + 1)`. -/
def dvB : PTm 3 := dr f (var 1) (var 0) (var 1) (succ (var 0)) (var 2)

theorem inst3_cellB (b a p : PTm n) : inst3 (cellB f) b a p =
    full f a b (succ a) b (succ a) (succ b) p + full f a b a (succ b) (succ a) (succ b) p := by
  simp [inst3, cellB]

theorem inst3_dhB (b a p : PTm n) : inst3 (dhB f) b a p = dr f a b (succ a) b p := by
  simp [inst3, dhB]

theorem inst3_dvB (b a p : PTm n) : inst3 (dvB f) b a p = dr f a b a (succ b) p := by
  simp [inst3, dvB]

/-- Full triangles and side doors of the cell `(a, b)`. -/
abbrev evB : PTm 3 := cellB f + ((dhB f + sh0 (dhB f)) + (dvB f + sh1 (dvB f)))

theorem evB_even (b a p : PTm n) : Γ ⊢[PRAAx] par (inst3 (evB f) b a p) ≐ zero := by
  have e : inst3 (evB f) b a p =
      (full f a b (succ a) b (succ a) (succ b) p + full f a b a (succ b) (succ a) (succ b) p) +
        ((dr f a b (succ a) b p + dr f a (succ b) (succ a) (succ b) p) +
          (dr f a b a (succ b) p + dr f (succ a) b (succ a) (succ b) p)) := by
    simp only [evB, inst3_add, inst3_sh0, inst3_sh1, inst3_cellB, inst3_dhB, inst3_dvB]
  rw [e]
  exact cell_even (bits_sum f a b p) (bits_sum f (succ a) b p) (bits_sum f (succ a) (succ b) p)
    (bits_sum f a (succ b) p)

/-- For the row `a`: the full triangles of the row, the doors `(a, 0) – (a + 1, 0)` and
`(a, N) – (a + 1, N)`, and the doors on the vertical lines `x = a`, `x = a + 1` have an even
total. -/
theorem row_even (N a p : PTm n) :
    Γ ⊢[PRAAx] par (ap3 (sum2F (cellB f)) N a p +
      ((dr f a zero (succ a) zero p + dr f a N (succ a) N p) +
        (ap3 (sum2F (dvB f)) N a p + ap3 (sum2F (dvB f)) N (succ a) p))) ≐ zero := by
  have hev : Γ ⊢[PRAAx] par (ap3 (sum2F (cellB f + ((dhB f + sh0 (dhB f)) + (dvB f + sh1 (dvB f)))))
      N a p) ≐ zero := sum2_even (evB f) (fun i p q => evB_even f i p q) N a p
  have st := straddle2 (Γ := Γ) (dhB f) N a p
  simp only [inst3_dhB] at st
  have e : Γ ⊢[PRAAx]
      (ap3 (sum2F (cellB f)) N a p +
        ((dr f a zero (succ a) zero p + dr f a N (succ a) N p) +
          (ap3 (sum2F (dvB f)) N a p + ap3 (sum2F (dvB f)) N (succ a) p))) +
        two * ap3 (sum2F (dhB f + sh0 (dhB f))) N a p ≐
      ap3 (sum2F (cellB f + ((dhB f + sh0 (dhB f)) + (dvB f + sh1 (dvB f))))) N a p +
        (ap3 (sum2F (dhB f + sh0 (dhB f))) N a p +
          (dr f a zero (succ a) zero p + dr f a N (succ a) N p)) := by
    ipra_lc (-1) * natEq (sum2_add (Γ := Γ) (cellB f) ((dhB f + sh0 (dhB f)) + (dvB f + sh1 (dvB f))) N a p) +
      (-1) * natEq (sum2_add (Γ := Γ) (dhB f + sh0 (dhB f)) (dvB f + sh1 (dvB f)) N a p) +
      (-1) * natEq (sum2_add (Γ := Γ) (dvB f) (sh1 (dvB f)) N a p) + (-1) * natEq (sum2_sh1 (Γ := Γ) (dvB f) N a p)
  exact (par_add_two _ _).eqSymm.eqTrans
    ((congrAp1 parF e).eqTrans ((par_add_even _ st).eqTrans hev))

/-! ## The grid

Variables of the bodies: `0 = a` (the summation index), `1 = N`, `2 = p`. -/

/-- The full triangles of the row `a`. -/
def RB : PTm 3 := ap3 (sum2F (cellB f)) (var 1) (var 0) (var 2)

/-- The bottom edge `(a, 0) – (a + 1, 0)`. -/
def h0B : PTm 3 := dr f (var 0) zero (succ (var 0)) zero (var 2)

/-- The top edge `(a, N) – (a + 1, N)`. -/
def hNB : PTm 3 := dr f (var 0) (var 1) (succ (var 0)) (var 1) (var 2)

/-- The doors on the vertical line `x = a`. -/
def WB : PTm 3 := ap3 (sum2F (dvB f)) (var 1) (var 0) (var 2)

theorem inst3_RB (a N p : PTm n) : inst3 (RB f) a N p = ap3 (sum2F (cellB f)) N a p := by
  simp [inst3, RB]

theorem inst3_h0B (a N p : PTm n) : inst3 (h0B f) a N p = dr f a zero (succ a) zero p := by
  simp [inst3, h0B]

theorem inst3_hNB (a N p : PTm n) : inst3 (hNB f) a N p = dr f a N (succ a) N p := by
  simp [inst3, hNB]

theorem inst3_WB (a N p : PTm n) : inst3 (WB f) a N p = ap3 (sum2F (dvB f)) N a p := by
  simp [inst3, WB]

/-- The contribution of the row `a`. -/
abbrev outB : PTm 3 := RB f + ((h0B f + hNB f) + (WB f + sh0 (WB f)))

theorem outB_even (a N p : PTm n) : Γ ⊢[PRAAx] par (inst3 (outB f) a N p) ≐ zero := by
  have e : inst3 (outB f) a N p = ap3 (sum2F (cellB f)) N a p +
      ((dr f a zero (succ a) zero p + dr f a N (succ a) N p) +
        (ap3 (sum2F (dvB f)) N a p + ap3 (sum2F (dvB f)) N (succ a) p)) := by
    simp only [outB, inst3_add, inst3_sh0, inst3_RB, inst3_h0B, inst3_hNB, inst3_WB]
  rw [e]
  exact row_even f N a p

/-- The number of full triangles of the grid `{0, …, N}²`. -/
def fullCount (N p : PTm n) : PTm n := ap3 (sum2F (RB f)) N N p

/-- The number of doors on the side `y = 0`. -/
def bottom (N p : PTm n) : PTm n := ap3 (sum2F (h0B f)) N N p

/-- The number of doors on the side `y = N`. -/
def top (N p : PTm n) : PTm n := ap3 (sum2F (hNB f)) N N p

/-- The number of doors on the side `x = 0`. -/
def left (N p : PTm n) : PTm n := ap3 (sum2F (dvB f)) N zero p

/-- The number of doors on the side `x = N`. -/
def right (N p : PTm n) : PTm n := ap3 (sum2F (dvB f)) N N p

@[simp] theorem subst_fullCount {m : ℕ} (σ : Fin n → PTm m) (N p : PTm n) :
    Syn.subst σ (fullCount f N p) = fullCount f (Syn.subst σ N) (Syn.subst σ p) := by
  simp [fullCount]

/-- For every labelling, the number of full triangles plus the number of doors on the boundary
of the square is even. -/
theorem boundary_doors (N p : PTm n) :
    Γ ⊢[PRAAx] par (fullCount f N p +
      ((bottom f N p + top f N p) + (left f N p + right f N p))) ≐ zero := by
  have hev : Γ ⊢[PRAAx] par (ap3 (sum2F (RB f + ((h0B f + hNB f) + (WB f + sh0 (WB f))))) N N p) ≐
      zero := sum2_even (outB f) (fun i p q => outB_even f i p q) N N p
  have st := straddle2 (Γ := Γ) (WB f) N N p
  simp only [inst3_WB] at st
  have e : Γ ⊢[PRAAx]
      (ap3 (sum2F (RB f)) N N p +
        ((ap3 (sum2F (h0B f)) N N p + ap3 (sum2F (hNB f)) N N p) +
          (ap3 (sum2F (dvB f)) N zero p + ap3 (sum2F (dvB f)) N N p))) +
        two * ap3 (sum2F (WB f + sh0 (WB f))) N N p ≐
      ap3 (sum2F (RB f + ((h0B f + hNB f) + (WB f + sh0 (WB f))))) N N p +
        (ap3 (sum2F (WB f + sh0 (WB f))) N N p +
          (ap3 (sum2F (dvB f)) N zero p + ap3 (sum2F (dvB f)) N N p)) := by
    ipra_lc (-1) * natEq (sum2_add (Γ := Γ) (RB f) ((h0B f + hNB f) + (WB f + sh0 (WB f))) N N p) +
      (-1) * natEq (sum2_add (Γ := Γ) (h0B f + hNB f) (WB f + sh0 (WB f)) N N p) +
      (-1) * natEq (sum2_add (Γ := Γ) (h0B f) (hNB f) N N p)
  exact (par_add_two _ _).eqSymm.eqTrans
    ((congrAp1 parF e).eqTrans ((par_add_even _ st).eqTrans hev))

/-! ## Admissible labellings -/

/-- `∀ i ≤ N. g(i, p, q) = 0`. -/
def ballZ (g : PTm 3) (N p q : PTm n) : Fm PTm n :=
  Fm.all (le (var 0) (Syn.shift N) ⟶ (inst3 g (var 0) (Syn.shift p) (Syn.shift q) ≐ zero))

@[simp] theorem subst_ballZ {m : ℕ} (σ : Fin n → PTm m) (g : PTm 3) (N p q : PTm n) :
    (ballZ g N p q).subst σ = ballZ g (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) := by
  simp [ballZ, subst_up_shift', Syn.up]

theorem ballZ_shift {g : PTm 3} {N p q : PTm n} (h : Γ ⊢[PRAAx] ballZ g N p q) :
    Γ.map Fm.shift ⊢[PRAAx] ballZ g (Syn.shift N) (Syn.shift p) (Syn.shift q) := by
  have e := h.shift
  simp only [Fm.shift, subst_ballZ] at e
  exact e

theorem ballZ_elim {g : PTm 3} {N p q t : PTm n} (h : Γ ⊢[PRAAx] ballZ g N p q)
    (ht : Γ ⊢[PRAAx] le t N) : Γ ⊢[PRAAx] inst3 g t p q ≐ zero := by
  have a := Prf.allE t h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_inst3, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at a
  exact .impE a ht

theorem shift_zero : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]

/-- `f(0, y, p)`; the hypothesis `f(0, y, p) = 0` for `y ≤ N` (`eq:lower`, first coordinate).
Variables: `0 = y`, `1 = N`, `2 = p`. -/
def leftB : PTm 3 := ap3 f zero (var 0) (var 2)

/-- `[f(N, y, p) = 0]`; the hypothesis `f(N, y, p) ≠ 0` for `y ≤ N` (`eq:upper`, first
coordinate). -/
def rightB : PTm 3 := eqb (ap3 f (var 1) (var 0) (var 2)) zero

/-- `f(x, 0, p) ∸ 1`; the hypothesis `f(x, 0, p) ≤ 1` for `x ≤ N` (`eq:lower`, second
coordinate). Variables: `0 = x`, `1 = N`, `2 = p`. -/
def bottomB : PTm 3 := monus (ap3 f (var 0) zero (var 2)) one

/-- `[f(x, N, p) = 1]`; the hypothesis `f(x, N, p) ≠ 1` for `x ≤ N` (`eq:upper`, second
coordinate). -/
def topB : PTm 3 := eqb (ap3 f (var 0) (var 1) (var 2)) one

theorem inst3_leftB (t N p : PTm n) : inst3 (leftB f) t N p = ap3 f zero t p := by
  simp [inst3, leftB]

theorem inst3_rightB (t N p : PTm n) : inst3 (rightB f) t N p = b0 f N t p := by
  simp [inst3, rightB, b0]

theorem inst3_bottomB (t N p : PTm n) : inst3 (bottomB f) t N p = monus (ap3 f t zero p) one := by
  simp [inst3, bottomB]

theorem inst3_topB (t N p : PTm n) : inst3 (topB f) t N p = b1 f t N p := by
  simp [inst3, topB, b1]

section Admissible

variable {f} {N p t : PTm n}

theorem left_bits (hl : Γ ⊢[PRAAx] ballZ (leftB f) N N p) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] (b0 f zero t p ≐ one) ⋏ (b1 f zero t p ≐ zero) := by
  have a := ballZ_elim hl ht
  rw [inst3_leftB] at a
  exact bits_of_zero a

theorem right_bit (hr : Γ ⊢[PRAAx] ballZ (rightB f) N N p) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] b0 f N t p ≐ zero := by
  have a := ballZ_elim hr ht
  rw [inst3_rightB] at a
  exact a

theorem bottom_bits (hb : Γ ⊢[PRAAx] ballZ (bottomB f) N N p) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] b0 f t zero p + b1 f t zero p ≐ one := by
  have a := ballZ_elim hb ht
  rw [inst3_bottomB] at a
  exact bits_of_le_one a

theorem top_bit (hT : Γ ⊢[PRAAx] ballZ (topB f) N N p) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] b1 f t N p ≐ zero := by
  have a := ballZ_elim hT ht
  rw [inst3_topB] at a
  exact a

/-- No door on the side `x = 0`. -/
theorem left_zero (hl : Γ ⊢[PRAAx] ballZ (leftB f) N N p) : Γ ⊢[PRAAx] left f N p ≐ zero := by
  show Γ ⊢[PRAAx] ap3 (sum2F (dvB f)) N zero p ≐ zero
  refine sum2_zero_of_bounded (dvB f) (.allI (.impI ?_))
  rw [inst3_dvB, shift_zero]
  have hl' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      ballZ (leftB f) (Syn.shift N) (Syn.shift N) (Syn.shift p) := (ballZ_shift hl).wk
  have h₀ := left_bits hl' (le_of_lt Prf.hyp0)
  have h₁ := left_bits hl' (t := succ (var 0)) Prf.hyp0
  exact dr_zero_of_b1 f (.andE₂ h₀) (.andE₂ h₁)

/-- No door on the side `x = N`. -/
theorem right_zero (hr : Γ ⊢[PRAAx] ballZ (rightB f) N N p) : Γ ⊢[PRAAx] right f N p ≐ zero := by
  show Γ ⊢[PRAAx] ap3 (sum2F (dvB f)) N N p ≐ zero
  refine sum2_zero_of_bounded (dvB f) (.allI (.impI ?_))
  rw [inst3_dvB]
  have hr' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      ballZ (rightB f) (Syn.shift N) (Syn.shift N) (Syn.shift p) := (ballZ_shift hr).wk
  exact dr_zero_of_b0 f (right_bit hr' (le_of_lt Prf.hyp0)) (right_bit hr' (t := succ (var 0)) Prf.hyp0)

/-- No door on the side `y = N`. -/
theorem top_zero (hT : Γ ⊢[PRAAx] ballZ (topB f) N N p) : Γ ⊢[PRAAx] top f N p ≐ zero := by
  show Γ ⊢[PRAAx] ap3 (sum2F (hNB f)) N N p ≐ zero
  refine sum2_zero_of_bounded (hNB f) (.allI (.impI ?_))
  rw [inst3_hNB]
  have hT' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      ballZ (topB f) (Syn.shift N) (Syn.shift N) (Syn.shift p) := (ballZ_shift hT).wk
  exact dr_zero_of_b1 f (top_bit hT' (le_of_lt Prf.hyp0)) (top_bit hT' (t := succ (var 0)) Prf.hyp0)

end Admissible

/-- The `1`-bit of the bottom vertex `(a, 0)`; variables `0 = a`, `1 = N`, `2 = p`. -/
def e1B : PTm 3 := b1 f (var 0) zero (var 2)

theorem inst3_e1B (a N p : PTm n) : inst3 (e1B f) a N p = b1 f a zero p := by
  simp [inst3, e1B]

/-- The number of doors on the side `y = 0` is odd: the one-dimensional Sperner lemma. -/
theorem bottom_odd {N p : PTm n} (hl : Γ ⊢[PRAAx] ballZ (leftB f) N N p)
    (hr : Γ ⊢[PRAAx] ballZ (rightB f) N N p) (hb : Γ ⊢[PRAAx] ballZ (bottomB f) N N p) :
    Γ ⊢[PRAAx] par (bottom f N p) ≐ one := by
  -- Each bottom edge: `door + 2 e(a) e(a + 1) = e(a) + e(a + 1)`.
  have hA : Γ ⊢[PRAAx] ap3 (sum2F (h0B f + two * (e1B f * sh0 (e1B f)))) N N p ≐
      ap3 (sum2F (e1B f + sh0 (e1B f))) N N p := by
    refine sum2_congr_bounded _ _ N p N p N (.allI (.impI ?_))
    simp only [inst3_add, inst3_mul, inst3_two, inst3_sh0, inst3_h0B, inst3_e1B]
    have hb' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        ballZ (bottomB f) (Syn.shift N) (Syn.shift N) (Syn.shift p) := (ballZ_shift hb).wk
    exact edge_of_two_classes f (bottom_bits hb' (le_of_lt Prf.hyp0))
      (bottom_bits hb' (t := succ (var 0)) Prf.hyp0)
  have hB := sum2_add (Γ := Γ) (h0B f) (two * (e1B f * sh0 (e1B f))) N N p
  have hT : Γ ⊢[PRAAx] par (ap3 (sum2F (two * (e1B f * sh0 (e1B f)))) N N p) ≐ zero :=
    sum2_even _ (fun i p q => by rw [inst3_mul, inst3_two]; exact par_double _) N N p
  have hC := straddle2 (Γ := Γ) (e1B f) N N p
  simp only [inst3_e1B] at hC
  -- The corners: `e(0) = 0` and `e(N) = 1`.
  have c0 : Γ ⊢[PRAAx] b1 f zero zero p ≐ zero := .andE₂ (left_bits hl (zero_le N))
  have cN : Γ ⊢[PRAAx] b1 f N zero p ≐ one :=
    (zero_add _).eqSymm.eqTrans
      ((congrAdd (right_bit hr (zero_le N)) (.eqRefl _)).eqSymm.eqTrans (bottom_bits hb (le_refl N)))
  have h₁ : Γ ⊢[PRAAx] par (bottom f N p) ≐
      par (ap3 (sum2F (h0B f + two * (e1B f * sh0 (e1B f)))) N N p) :=
    (par_add_even _ hT).eqSymm.eqTrans (congrAp1 parF hB.eqSymm)
  refine h₁.eqTrans ((congrAp1 parF hA).eqTrans ((par_eq_of_add_even hC).eqTrans ?_))
  exact (congrAp1 parF ((congrAdd c0 cN).eqTrans (zero_add _))).eqTrans par_one

/-- The cubical Sperner parity lemma in dimension two, at arbitrary terms: an admissible
labelling has an odd number of full triangles. -/
theorem sperner_open {N p : PTm n} (hl : Γ ⊢[PRAAx] ballZ (leftB f) N N p)
    (hr : Γ ⊢[PRAAx] ballZ (rightB f) N N p) (hb : Γ ⊢[PRAAx] ballZ (bottomB f) N N p)
    (hT : Γ ⊢[PRAAx] ballZ (topB f) N N p) : Γ ⊢[PRAAx] par (fullCount f N p) ≐ one := by
  have bd := boundary_doors (Γ := Γ) f N p
  have tz := natEq (top_zero hT); have lz := natEq (left_zero hl); have rz := natEq (right_zero hr)
  have e : Γ ⊢[PRAAx] fullCount f N p +
      ((bottom f N p + top f N p) + (left f N p + right f N p)) ≐ fullCount f N p + bottom f N p := by
    ipra_lc tz + lz + rz
  exact (par_eq_of_add_even ((congrAp1 parF e).eqSymm.eqTrans bd)).eqTrans (bottom_odd f hl hr hb)

/-- Variables: `0 = N`, `1 = p`. -/
abbrev spernerFormula : Fm PTm 2 :=
  ballZ (leftB f) (var 0) (var 0) (var 1) ⟶ ballZ (rightB f) (var 0) (var 0) (var 1) ⟶
    ballZ (bottomB f) (var 0) (var 0) (var 1) ⟶ ballZ (topB f) (var 0) (var 0) (var 1) ⟶
      (par (fullCount f (var 0) (var 1)) ≐ one)

/-- The cubical Sperner parity lemma in dimension two (`thm:sperner`, `d = 2`): for all `N`
and `p`, if `f(0, y, p) = 0`, `f(N, y, p) ≠ 0`, `f(x, 0, p) ≤ 1` and `f(x, N, p) ≠ 1` for all
`x, y ≤ N`, then the number of full Kuhn triangles of the grid `{0, …, N}²` is odd. -/
theorem sperner_2d : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (spernerFormula f) := by
  refine closeUniv 2 (.impI (.impI (.impI (.impI ?_))))
  exact sperner_open f (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0

/-- Variables: `0 = N`, `1 = p`. -/
abbrev spernerPosFormula : Fm PTm 2 :=
  ballZ (leftB f) (var 0) (var 0) (var 1) ⟶ ballZ (rightB f) (var 0) (var 0) (var 1) ⟶
    ballZ (bottomB f) (var 0) (var 0) (var 1) ⟶ ballZ (topB f) (var 0) (var 0) (var 1) ⟶
      neg (fullCount f (var 0) (var 1) ≐ zero)

/-- An admissible labelling has a full triangle: the count is not zero. -/
theorem sperner_2d_pos : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (spernerPosFormula f) := by
  refine closeUniv 2 (.impI (.impI (.impI (.impI (.impI ?_)))))
  have h : ([fullCount f (var 0) (var 1) ≐ zero, ballZ (topB f) (var 0) (var 0) (var 1),
      ballZ (bottomB f) (var 0) (var 0) (var 1), ballZ (rightB f) (var 0) (var 0) (var 1),
      ballZ (leftB f) (var 0) (var 0) (var 1)] : List (Fm PTm 2)) ⊢[PRAAx]
      par (fullCount f (var 0) (var 1)) ≐ one :=
    sperner_open f (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1
  exact zero_ne_one _ (par_zero.eqSymm.eqTrans ((congrAp1 parF Prf.hyp0).eqSymm.eqTrans h))

end LeanProofs.IPRA.Topology.Sperner2D
