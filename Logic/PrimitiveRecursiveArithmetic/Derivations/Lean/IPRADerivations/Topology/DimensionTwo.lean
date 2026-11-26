import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.Topology.Sperner2D
import IPRADerivations.Topology.StaggeredCells

/-!
# The finite dimension obstruction from the square to the line (`thm:finite`, `d = 2`)

Packet: `topology/dimension_invariance_ipra`, Sections "Finite data and the main quantitative
theorem" and "Staggered rational cells and the dimension obstruction". The packet's finite
theorem says that a rational table `F : {0, …, N}^d → ℚ^m` with opposite faces separated by
`h` and with Kuhn simplices of image diameter below `h / d` forces `d ≤ m`. For `d = 2` the
only case with content is `m = 1`: for `m ≥ 2` the conclusion holds, and for `m = 0` the
separation fails. This file derives that case.

The table is an arbitrary ternary primitive recursive symbol `G(x, y, p)` with a runtime
parameter `p`, with natural-number values in units of `h / 2`. (A rational table with a
common denominator that is bounded below has this form after a translation and a change of
unit; the reduction is not formalized here.) In these units separation by `h` is distance
`≥ 2`, and the strict bound `< h / 2` is distance `≤ 1`. The grid size `N` and the parameter
`p` are variables of the object theory.

* `sep0F`: `|G(0, y') − G(N, y)| ≥ 2` for all `y, y' ≤ N` (`eq:sep`, first coordinate);
* `sep1F`: `|G(x', 0) − G(x, N)| ≥ 2` for all `x, x' ≤ N` (`eq:sep`, second coordinate);
* `smallF`: for all `a, b < N`, the vertices of each of the two Kuhn triangles of the cell
  `(a, b)` have values pairwise within `1` (`eq:small`);
* `no_table`, `no_table_closed`: the three conditions are contradictory, for every `N` and
  `p`.

The proof is the packet's. The colour `λ(v)` (`eq:color`) is `0` if the cell of `G(v)` in the
first grid is occupied by a point of the face `x = 0`, else `1` if its cell in the second grid
is occupied by a point of the face `y = 0`, else `2`; membership is a bounded sum of equality
tests (`cnt0`, `cnt1`). Separation makes `λ` admissible, so `Sperner2D.sperner_open` gives an
odd number of full triangles. Conversely no triangle is full: a vertex `u` of colour `0`, a
vertex `v` of colour `1` and a vertex `w` of colour `2` would have `c₀(u) ≠ c₀(w)` and
`c₁(v) ≠ c₁(w)`, which `StaggeredCells.staggered` excludes when the three values are pairwise
within `1`. The count of full triangles is then both odd and zero.

No witness is extracted from the parity: the contradiction is between two equations for the
same primitive recursive count.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.DimensionTwo

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum2_zero_of_bounded)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (term_le_sum2)
open LeanProofs.IPRA.Topology.Sperner2D
open LeanProofs.IPRA.Topology.StaggeredCells

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Shifts of terms -/

theorem shift_ap3 (f : PR 3) (a b c : PTm n) :
    Syn.shift (ap3 f a b c) = ap3 f (Syn.shift a) (Syn.shift b) (Syn.shift c) := by
  simp [Syn.shift]

theorem shift_half (a : PTm n) : Syn.shift (half a) = half (Syn.shift a) := by simp [Syn.shift]

theorem shift_succ (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

theorem shift_var0 : Syn.shift (var 0 : PTm (n + 1)) = (var 1 : PTm (n + 2)) := by
  simp [Syn.shift]

theorem shift_pairT (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

theorem shift_lt' {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) :
    Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_lt h

/-- A sum over `i ≤ M` whose terms vanish is zero. -/
theorem sum2_zero_le (f : PTm 3) {M p q : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift M) ⟶
      (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐ zero))) :
    Γ ⊢[PRAAx] ap3 (sum2F f) (succ M) p q ≐ zero := by
  refine sum2_zero_of_bounded f (.allI (.impI ?_))
  have ho := h.allOpen
  refine .impE ho.wk ?_
  have h0 : (lt (var 0) (Syn.shift (succ M)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (Syn.shift (succ M)) := Prf.hyp0
  rw [shift_succ] at h0
  exact (succ_monus_succ _ _).eqSymm.eqTrans h0

/-! ## Equality tests and small values -/

alias eqb_congr := Common.congrEqb

alias eqb01 := Common.eqb_zero_or_one

alias eqb_le_one' := Common.eqb_le_one

theorem eqb_zero_of_pos {c : PTm n} (h : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx] eqb c zero ≐ zero :=
  eqb_of_ne (.impI (not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 h.wk)))

theorem two_mul_one : Γ ⊢[PRAAx] two * (one : PTm n) ≐ two := by
  ipra_ring

theorem val_e0_zero {e0 e1 : PTm n} (h : Γ ⊢[PRAAx] e0 ≐ zero) :
    Γ ⊢[PRAAx] e0 * (one + e1) ≐ zero := by
  ipra_lc (1 + 𝔞 e1) * natEq h

theorem val_e0_one {e0 e1 : PTm n} (h : Γ ⊢[PRAAx] e0 ≐ one) :
    Γ ⊢[PRAAx] e0 * (one + e1) ≐ succ e1 := by
  ipra_lc (1 + 𝔞 e1) * natEq h

theorem val_e1_zero {e0 e1 : PTm n} (h : Γ ⊢[PRAAx] e1 ≐ zero) :
    Γ ⊢[PRAAx] e0 * (one + e1) ≐ e0 := by
  ipra_lc 𝔞 e0 * natEq h

theorem val_e1_one {e0 e1 : PTm n} (h : Γ ⊢[PRAAx] e1 ≐ one) :
    Γ ⊢[PRAAx] e0 * (one + e1) ≐ two * e0 := by
  ipra_lc 𝔞 e0 * natEq h

theorem prod_zero₁ {x y z : PTm n} (h : Γ ⊢[PRAAx] x ≐ zero) : Γ ⊢[PRAAx] x * y * z ≐ zero := by
  ipra_lc (𝔞 y * 𝔞 z) * natEq h

theorem prod_zero₂ {x y z : PTm n} (h : Γ ⊢[PRAAx] y ≐ zero) : Γ ⊢[PRAAx] x * y * z ≐ zero := by
  ipra_lc (𝔞 x * 𝔞 z) * natEq h

theorem prod_zero₃ {x y z : PTm n} (h : Γ ⊢[PRAAx] z ≐ zero) : Γ ⊢[PRAAx] x * y * z ≐ zero := by
  ipra_lc (𝔞 x * 𝔞 y) * natEq h

/-! ## The colour bits of a vertex with a known value -/

section Bits

variable {f : PR 3} {X Y P : PTm n}

theorem b2_of_zero (h : Γ ⊢[PRAAx] ap3 f X Y P ≐ zero) : Γ ⊢[PRAAx] b2 f X Y P ≐ zero := by
  have hb := bits_of_zero h
  exact (congrMonus (.eqRefl _) ((congrAdd (.andE₁ hb) (.andE₂ hb)).eqTrans (add_zero _))).eqTrans
    (monus_self _)

theorem b2_of_one (h : Γ ⊢[PRAAx] ap3 f X Y P ≐ one) : Γ ⊢[PRAAx] b2 f X Y P ≐ zero := by
  have h0 : Γ ⊢[PRAAx] eqb (ap3 f X Y P) zero ≐ zero :=
    eqb_of_ne (.impI (zero_ne_one _ (Prf.hyp0.eqSymm.eqTrans h.wk)))
  exact (congrMonus (.eqRefl _) ((congrAdd h0 (eqb_of_eq h)).eqTrans (zero_add _))).eqTrans
    (monus_self _)

theorem b0_of_succ {t : PTm n} (h : Γ ⊢[PRAAx] ap3 f X Y P ≐ succ t) :
    Γ ⊢[PRAAx] b0 f X Y P ≐ zero :=
  eqb_of_ne (.impI (succ_ne_zero' _ (h.wk.eqSymm.eqTrans Prf.hyp0)))

theorem b1_of_double {e : PTm n} (he : Γ ⊢[PRAAx] (e ≐ zero) ⋎ (e ≐ one))
    (h : Γ ⊢[PRAAx] ap3 f X Y P ≐ two * e) : Γ ⊢[PRAAx] b1 f X Y P ≐ zero := by
  refine .orE he ?_ ?_
  · have hz : ((e ≐ zero) :: Γ) ⊢[PRAAx] ap3 f X Y P ≐ zero :=
      h.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    exact .andE₂ (bits_of_zero hz)
  · have h2 : ((e ≐ one) :: Γ) ⊢[PRAAx] ap3 f X Y P ≐ two :=
      h.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans two_mul_one)
    refine eqb_of_ne (.impI ?_)
    have e21 : ((ap3 f X Y P ≐ one) :: (e ≐ one) :: Γ) ⊢[PRAAx] (one : PTm n) ≐ zero :=
      succ_inj (h2.wk.eqSymm.eqTrans Prf.hyp0)
    exact succ_ne_zero' _ e21

end Bits

/-! ## The colouring -/

variable (G : PR 3)

/-- `[c₀(0, y') = t]`: the cell of `G(0, y')` in the first grid is `t`.
Variables: `0 = y'`, `1 = t`, `2 = p`. -/
def body0 : PTm 3 := eqb (half (ap3 G zero (var 0) (var 2))) (var 1)

/-- `[c₁(x', 0) = t]`: the cell of `G(x', 0)` in the second grid is `t`.
Variables: `0 = x'`, `1 = t`, `2 = p`. -/
def body1 : PTm 3 := eqb (half (succ (ap3 G (var 0) zero (var 2)))) (var 1)

theorem inst3_body0 (i t p : PTm n) :
    inst3 (body0 G) i t p = eqb (half (ap3 G zero i p)) t := by simp [inst3, body0]

theorem inst3_body1 (i t p : PTm n) :
    inst3 (body1 G) i t p = eqb (half (succ (ap3 G i zero p))) t := by simp [inst3, body1]

/-- The number of points of the face `x = 0` whose first-grid cell is that of `G(X, Y)`. -/
def cnt0 (X Y N p : PTm n) : PTm n :=
  ap3 (sum2F (body0 G)) (succ N) (half (ap3 G X Y p)) p

/-- The number of points of the face `y = 0` whose second-grid cell is that of `G(X, Y)`. -/
def cnt1 (X Y N p : PTm n) : PTm n :=
  ap3 (sum2F (body1 G)) (succ N) (half (succ (ap3 G X Y p))) p

/-- The colour of the vertex `(X, Y)` (`eq:color`). -/
def lamT (X Y N p : PTm n) : PTm n :=
  eqb (cnt0 G X Y N p) zero * (one + eqb (cnt1 G X Y N p) zero)

@[simp] theorem subst_cnt0 {m : ℕ} (σ : Fin n → PTm m) (X Y N p : PTm n) :
    Syn.subst σ (cnt0 G X Y N p) =
      cnt0 G (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ N) (Syn.subst σ p) := by
  simp [cnt0]

@[simp] theorem subst_cnt1 {m : ℕ} (σ : Fin n → PTm m) (X Y N p : PTm n) :
    Syn.subst σ (cnt1 G X Y N p) =
      cnt1 G (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ N) (Syn.subst σ p) := by
  simp [cnt1]

@[simp] theorem subst_lamT {m : ℕ} (σ : Fin n → PTm m) (X Y N p : PTm n) :
    Syn.subst σ (lamT G X Y N p) =
      lamT G (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ N) (Syn.subst σ p) := by
  simp [lamT]

/-- The colour as a term in `x`, `y` and the packed parameter `⟨N, p⟩`. -/
def lam3 : PTm 3 := lamT G (var 0) (var 1) (fstT (var 2)) (sndT (var 2))

/-- The colouring symbol `λ(x, y, ⟨N, p⟩)`. -/
def lamF : PR 3 := PTm.toPR (lam3 G)

theorem lam_at (X Y q : PTm n) :
    Γ ⊢[PRAAx] ap3 (lamF G) X Y q ≐ lamT G X Y (fstT q) (sndT q) := by
  have h := toPR_eq (Γ := Γ) (lam3 G) ![X, Y, q]
  simpa only [lamF, lam3, ap3, subst_lamT, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] using h

theorem lamT_congr {X Y N N' p p' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N') (hp : Γ ⊢[PRAAx] p ≐ p') :
    Γ ⊢[PRAAx] lamT G X Y N p ≐ lamT G X Y N' p' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (lamT G (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![X, Y, N, p]) (σ' := ![X, Y, N', p'])
    (fun j => by fin_cases j <;> first | exact .eqRefl _ | assumption)
  simpa using h

/-- The colour at the packed parameter. -/
theorem lam_eq (X Y N p : PTm n) :
    Γ ⊢[PRAAx] ap3 (lamF G) X Y (pairT N p) ≐ lamT G X Y N p :=
  (lam_at G X Y (pairT N p)).eqTrans (lamT_congr G (fst_pair N p) (snd_pair N p))

/-! ## The bits of a vertex, from its two membership tests -/

section Vertex

variable {X Y N p : PTm n}

theorem vb2_zero_of_e0 (h : Γ ⊢[PRAAx] eqb (cnt0 G X Y N p) zero ≐ zero) :
    Γ ⊢[PRAAx] b2 (lamF G) X Y (pairT N p) ≐ zero := by
  have v : Γ ⊢[PRAAx] lamT G X Y N p ≐ zero := val_e0_zero h
  exact b2_of_zero ((lam_eq G X Y N p).eqTrans v)

theorem vb0_zero_of_e0 (h : Γ ⊢[PRAAx] eqb (cnt0 G X Y N p) zero ≐ one) :
    Γ ⊢[PRAAx] b0 (lamF G) X Y (pairT N p) ≐ zero := by
  have v : Γ ⊢[PRAAx] lamT G X Y N p ≐ succ (eqb (cnt1 G X Y N p) zero) := val_e0_one h
  exact b0_of_succ ((lam_eq G X Y N p).eqTrans v)

theorem vb2_zero_of_e1 (h0 : Γ ⊢[PRAAx] eqb (cnt0 G X Y N p) zero ≐ one)
    (h1 : Γ ⊢[PRAAx] eqb (cnt1 G X Y N p) zero ≐ zero) :
    Γ ⊢[PRAAx] b2 (lamF G) X Y (pairT N p) ≐ zero := by
  have v : Γ ⊢[PRAAx] lamT G X Y N p ≐ succ (eqb (cnt1 G X Y N p) zero) := val_e0_one h0
  exact b2_of_one ((lam_eq G X Y N p).eqTrans (v.eqTrans (congrSucc h1)))

theorem vb1_zero_of_e1 (h1 : Γ ⊢[PRAAx] eqb (cnt1 G X Y N p) zero ≐ one) :
    Γ ⊢[PRAAx] b1 (lamF G) X Y (pairT N p) ≐ zero := by
  have v : Γ ⊢[PRAAx] lamT G X Y N p ≐ two * eqb (cnt0 G X Y N p) zero := val_e1_one h1
  exact b1_of_double (eqb01 _ _) ((lam_eq G X Y N p).eqTrans v)

end Vertex

/-! ## No triangle with small values is full -/

/-- Three vertices `u`, `v`, `w` with values pairwise within `1` do not carry the colours
`0`, `1`, `2` in this order. -/
theorem triple_zero {X₁ Y₁ X₂ Y₂ X₃ Y₃ N p : PTm n}
    (huw : Γ ⊢[PRAAx] near (ap3 G X₁ Y₁ p) (ap3 G X₃ Y₃ p))
    (hvw : Γ ⊢[PRAAx] near (ap3 G X₂ Y₂ p) (ap3 G X₃ Y₃ p))
    (huv : Γ ⊢[PRAAx] near (ap3 G X₁ Y₁ p) (ap3 G X₂ Y₂ p)) :
    Γ ⊢[PRAAx] b0 (lamF G) X₁ Y₁ (pairT N p) * b1 (lamF G) X₂ Y₂ (pairT N p) *
      b2 (lamF G) X₃ Y₃ (pairT N p) ≐ zero := by
  refine .orE (staggered huw hvw huv) ?_ ?_
  · have he : ((half (ap3 G X₁ Y₁ p) ≐ half (ap3 G X₃ Y₃ p)) :: Γ) ⊢[PRAAx]
        eqb (cnt0 G X₁ Y₁ N p) zero ≐ eqb (cnt0 G X₃ Y₃ N p) zero :=
      eqb_congr (congrAp3 _ (.eqRefl _) Prf.hyp0 (.eqRefl _)) (.eqRefl _)
    refine .orE (eqb01 (cnt0 G X₃ Y₃ N p) zero) ?_ ?_
    · exact prod_zero₃ (vb2_zero_of_e0 G Prf.hyp0)
    · exact prod_zero₁ (vb0_zero_of_e0 G (he.wk.eqTrans Prf.hyp0))
  · have he : ((half (succ (ap3 G X₂ Y₂ p)) ≐ half (succ (ap3 G X₃ Y₃ p))) :: Γ) ⊢[PRAAx]
        eqb (cnt1 G X₂ Y₂ N p) zero ≐ eqb (cnt1 G X₃ Y₃ N p) zero :=
      eqb_congr (congrAp3 _ (.eqRefl _) Prf.hyp0 (.eqRefl _)) (.eqRefl _)
    refine .orE (eqb01 (cnt0 G X₃ Y₃ N p) zero) ?_ ?_
    · exact prod_zero₃ (vb2_zero_of_e0 G Prf.hyp0)
    · refine .orE (eqb01 (cnt1 G X₃ Y₃ N p) zero) ?_ ?_
      · exact prod_zero₃ (vb2_zero_of_e1 G Prf.hyp1 Prf.hyp0)
      · exact prod_zero₂ (vb1_zero_of_e1 G (he.wk.wk.eqTrans Prf.hyp0))

/-- A triangle whose three values are pairwise within `1` is not full. -/
theorem full_zero {X₁ Y₁ X₂ Y₂ X₃ Y₃ N p : PTm n}
    (h12 : Γ ⊢[PRAAx] near (ap3 G X₁ Y₁ p) (ap3 G X₂ Y₂ p))
    (h13 : Γ ⊢[PRAAx] near (ap3 G X₁ Y₁ p) (ap3 G X₃ Y₃ p))
    (h23 : Γ ⊢[PRAAx] near (ap3 G X₂ Y₂ p) (ap3 G X₃ Y₃ p)) :
    Γ ⊢[PRAAx] full (lamF G) X₁ Y₁ X₂ Y₂ X₃ Y₃ (pairT N p) ≐ zero := by
  ipra_lc [full, permT] natEq (triple_zero G (N := N) h13 h23 h12) +
    natEq (triple_zero G (N := N) h12 (near_symm h23) h13) + natEq (triple_zero G (N := N) h23 h13 (near_symm h12)) +
    natEq (triple_zero G (N := N) (near_symm h23) h12 (near_symm h13)) +
    natEq (triple_zero G (N := N) (near_symm h12) (near_symm h13) h23) +
    natEq (triple_zero G (N := N) (near_symm h13) (near_symm h12) (near_symm h23))

/-! ## Admissibility of the colouring -/

section Pointwise

variable {N p : PTm n}

/-- A point of the face `x = 0` with the first-grid cell of `G(X, Y)` makes `cnt0` positive. -/
theorem cnt0_pos {X Y y : PTm n} (hy : Γ ⊢[PRAAx] le y N)
    (hc : Γ ⊢[PRAAx] half (ap3 G zero y p) ≐ half (ap3 G X Y p)) :
    Γ ⊢[PRAAx] le one (cnt0 G X Y N p) := by
  have t := term_le_sum2 (Γ := Γ) (body0 G) (p := half (ap3 G X Y p)) (q := p) (succ_le_succ hy)
  rw [inst3_body0] at t
  exact le_congr (eqb_of_eq hc) (.eqRefl _) t

/-- A point of the face `y = 0` with the second-grid cell of `G(X, Y)` makes `cnt1` positive. -/
theorem cnt1_pos {X Y x : PTm n} (hx : Γ ⊢[PRAAx] le x N)
    (hc : Γ ⊢[PRAAx] half (succ (ap3 G x zero p)) ≐ half (succ (ap3 G X Y p))) :
    Γ ⊢[PRAAx] le one (cnt1 G X Y N p) := by
  have t := term_le_sum2 (Γ := Γ) (body1 G) (p := half (succ (ap3 G X Y p))) (q := p)
    (succ_le_succ hx)
  rw [inst3_body1] at t
  exact le_congr (eqb_of_eq hc) (.eqRefl _) t

/-- On the face `x = 0` the colour is `0`. -/
theorem lam_left {y : PTm n} (hy : Γ ⊢[PRAAx] le y N) :
    Γ ⊢[PRAAx] ap3 (lamF G) zero y (pairT N p) ≐ zero := by
  have v : Γ ⊢[PRAAx] lamT G zero y N p ≐ zero :=
    val_e0_zero (eqb_zero_of_pos (cnt0_pos G hy (.eqRefl _)))
  exact (lam_eq G zero y N p).eqTrans v

/-- On the face `y = 0` the colour is at most `1`. -/
theorem lam_bottom {x : PTm n} (hx : Γ ⊢[PRAAx] le x N) :
    Γ ⊢[PRAAx] le (ap3 (lamF G) x zero (pairT N p)) one := by
  have v : Γ ⊢[PRAAx] lamT G x zero N p ≐ eqb (cnt0 G x zero N p) zero :=
    val_e1_zero (eqb_zero_of_pos (cnt1_pos G hx (.eqRefl _)))
  exact le_congr ((lam_eq G x zero N p).eqTrans v).eqSymm (.eqRefl _) (eqb_le_one' _ _)

/-- A vertex whose first-grid cell meets no point of the face `x = 0` has a colour `≠ 0`. -/
theorem lam_right {X Y : PTm n} (hc : Γ ⊢[PRAAx] cnt0 G X Y N p ≐ zero) :
    Γ ⊢[PRAAx] b0 (lamF G) X Y (pairT N p) ≐ zero :=
  vb0_zero_of_e0 G (eqb_of_eq hc)

/-- A vertex whose second-grid cell meets no point of the face `y = 0` has a colour `≠ 1`. -/
theorem lam_top {X Y : PTm n} (hc : Γ ⊢[PRAAx] cnt1 G X Y N p ≐ zero) :
    Γ ⊢[PRAAx] b1 (lamF G) X Y (pairT N p) ≐ zero :=
  vb1_zero_of_e1 G (eqb_of_eq hc)

end Pointwise

/-! ## The three conditions on the table -/

/-- `eq:sep`, first coordinate: `|G(0, y') − G(N, y)| ≥ 2` for all `y, y' ≤ N`. -/
abbrev sep0F (N p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (le (var 1) (Syn.shift (Syn.shift N)) ⟶ (le (var 0) (Syn.shift (Syn.shift N)) ⟶
    le two (dist (ap3 G zero (var 0) (Syn.shift (Syn.shift p)))
      (ap3 G (Syn.shift (Syn.shift N)) (var 1) (Syn.shift (Syn.shift p)))))))

/-- `eq:sep`, second coordinate: `|G(x', 0) − G(x, N)| ≥ 2` for all `x, x' ≤ N`. -/
abbrev sep1F (N p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (le (var 1) (Syn.shift (Syn.shift N)) ⟶ (le (var 0) (Syn.shift (Syn.shift N)) ⟶
    le two (dist (ap3 G (var 0) zero (Syn.shift (Syn.shift p)))
      (ap3 G (var 1) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift p)))))))

/-- `|G(X₁, Y₁) − G(X₂, Y₂)| ≤ 1`. -/
abbrev closeF (X₁ Y₁ X₂ Y₂ p : PTm n) : Fm PTm n :=
  le (dist (ap3 G X₁ Y₁ p) (ap3 G X₂ Y₂ p)) one

/-- `eq:small`: for all `a, b < N`, the vertices of the triangles
`(a, b), (a + 1, b), (a + 1, b + 1)` and `(a, b), (a, b + 1), (a + 1, b + 1)` have values
pairwise within `1`. -/
abbrev smallF (N p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (lt (var 1) (Syn.shift (Syn.shift N)) ⟶ (lt (var 0) (Syn.shift (Syn.shift N)) ⟶
    (closeF G (var 1) (var 0) (succ (var 1)) (var 0) (Syn.shift (Syn.shift p)) ⋏
      (closeF G (succ (var 1)) (var 0) (succ (var 1)) (succ (var 0)) (Syn.shift (Syn.shift p)) ⋏
        (closeF G (var 1) (var 0) (succ (var 1)) (succ (var 0)) (Syn.shift (Syn.shift p)) ⋏
          (closeF G (var 1) (var 0) (var 1) (succ (var 0)) (Syn.shift (Syn.shift p)) ⋏
            closeF G (var 1) (succ (var 0)) (succ (var 1)) (succ (var 0))
              (Syn.shift (Syn.shift p)))))))))

/-! ## The hypotheses of the parity lemma -/

theorem adm_left (N p : PTm n) : Γ ⊢[PRAAx] ballZ (leftB (lamF G)) N N (pairT N p) := by
  refine .allI (.impI ?_)
  rw [inst3_leftB, shift_pairT]
  exact lam_left G Prf.hyp0

theorem adm_bottom (N p : PTm n) : Γ ⊢[PRAAx] ballZ (bottomB (lamF G)) N N (pairT N p) := by
  refine .allI (.impI ?_)
  rw [inst3_bottomB, shift_pairT]
  exact lam_bottom G Prf.hyp0

theorem adm_right {N p : PTm n} (hs : Γ ⊢[PRAAx] sep0F G N p) :
    Γ ⊢[PRAAx] ballZ (rightB (lamF G)) N N (pairT N p) := by
  refine .allI (.impI ?_)
  rw [inst3_rightB, shift_pairT]
  refine lam_right G ?_
  show (le (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
    ap3 (sum2F (body0 G)) (succ (Syn.shift N)) (half (ap3 G (Syn.shift N) (var 0) (Syn.shift p)))
      (Syn.shift p) ≐ zero
  refine sum2_zero_le (body0 G) (.allI (.impI ?_))
  rw [inst3_body0, shift_half, shift_ap3, shift_var0]
  have hs₁ : (le (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Fm.all _ := hs.allOpen.wk
  have hs₂ := hs₁.allOpen
  have hj := shift_le' (Γ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift) Prf.hyp0
  rw [shift_var0] at hj
  exact eqb_of_ne (cell0_ne_of_dist (.impE (.impE hs₂.wk hj.wk) Prf.hyp0))

theorem adm_top {N p : PTm n} (hs : Γ ⊢[PRAAx] sep1F G N p) :
    Γ ⊢[PRAAx] ballZ (topB (lamF G)) N N (pairT N p) := by
  refine .allI (.impI ?_)
  rw [inst3_topB, shift_pairT]
  refine lam_top G ?_
  show (le (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
    ap3 (sum2F (body1 G)) (succ (Syn.shift N))
      (half (succ (ap3 G (var 0) (Syn.shift N) (Syn.shift p)))) (Syn.shift p) ≐ zero
  refine sum2_zero_le (body1 G) (.allI (.impI ?_))
  rw [inst3_body1, shift_half, shift_succ, shift_ap3, shift_var0]
  have hs₁ : (le (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Fm.all _ := hs.allOpen.wk
  have hs₂ := hs₁.allOpen
  have hj := shift_le' (Γ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift) Prf.hyp0
  rw [shift_var0] at hj
  exact eqb_of_ne (cell1_ne_of_dist (.impE (.impE hs₂.wk hj.wk) Prf.hyp0))

/-- Under `smallF` no triangle of the grid is full. -/
theorem fullCount_zero {N p : PTm n} (hs : Γ ⊢[PRAAx] smallF G N p) :
    Γ ⊢[PRAAx] fullCount (lamF G) N (pairT N p) ≐ zero := by
  show Γ ⊢[PRAAx] ap3 (sum2F (RB (lamF G))) N N (pairT N p) ≐ zero
  refine sum2_zero_of_bounded _ (.allI (.impI ?_))
  rw [inst3_RB, shift_pairT]
  refine sum2_zero_of_bounded _ (.allI (.impI ?_))
  rw [inst3_cellB, shift_var0, shift_pairT]
  have hs₁ : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Fm.all _ := hs.allOpen.wk
  have hs₂ := hs₁.allOpen
  have ha := shift_lt' (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) Prf.hyp0
  rw [shift_var0] at ha
  have h5 := Prf.impE (Prf.impE hs₂.wk ha.wk) Prf.hyp0
  have hPQ := near_of_dist (.andE₁ h5)
  have hQR := near_of_dist (.andE₁ (.andE₂ h5))
  have hPR := near_of_dist (.andE₁ (.andE₂ (.andE₂ h5)))
  have hPS := near_of_dist (.andE₁ (.andE₂ (.andE₂ (.andE₂ h5))))
  have hSR := near_of_dist (.andE₂ (.andE₂ (.andE₂ (.andE₂ h5))))
  ipra_lc natEq (full_zero G (N := Syn.shift (Syn.shift N)) hPQ hPR hQR) +
    natEq (full_zero G (N := Syn.shift (Syn.shift N)) hPS hPR hSR)

/-! ## The obstruction -/

/-- No table on the grid `{0, …, N}²` with values on the line has both pairs of opposite faces
separated by `2` and all Kuhn triangles of diameter at most `1`. -/
theorem no_table {N p : PTm n} (h0 : Γ ⊢[PRAAx] sep0F G N p) (h1 : Γ ⊢[PRAAx] sep1F G N p)
    (hs : Γ ⊢[PRAAx] smallF G N p) : Γ ⊢[PRAAx] Fm.bot := by
  have odd := sperner_open (lamF G) (adm_left G N p) (adm_right G h0) (adm_bottom G N p)
    (adm_top G h1)
  have z := fullCount_zero G hs
  exact zero_ne_one _ (par_zero.eqSymm.eqTrans ((congrAp1 parF z).eqSymm.eqTrans odd))

/-- Variables: `0 = N`, `1 = p`. -/
abbrev obstructionFormula : Fm PTm 2 :=
  sep0F G (var 0) (var 1) ⟶ sep1F G (var 0) (var 1) ⟶ smallF G (var 0) (var 1) ⟶ Fm.bot

/-- The finite dimension obstruction for `d = 2`, `m = 1` (`thm:finite`): for all `N` and `p`,
the separation conditions `sep0F`, `sep1F` and the small-simplex condition `smallF` on the
table `G(·, ·, p)` are contradictory. -/
theorem no_table_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (obstructionFormula G) :=
  closeUniv 2 (.impI (.impI (.impI (no_table G hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Topology.DimensionTwo
