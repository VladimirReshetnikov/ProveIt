import IPRADerivations.Geometry.CevaMenelaus
import IPRADerivations.Geometry.Projective
import IPRADerivations.DiophantineNumberTheory.FermatQuartic
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Pairing

/-!
# Internal Desargues: incidence, the common-kernel algorithm and both implications

Packet: `desargues_pascal_ipra`, `sections/03_geometry.tex` and `sections/04_desargues.tex`.
Points and lines are integer triples `Vec 3 n`; a triple is nonzero (`nzV`) when some component
is nonzero (`nz`, i.e. `|pos − neg| ≥ 1`).

* `inc_det` (`lem:inc-det`): a nonzero `o` with `o·u = o·v = o·w = 0` forces `[u v w] = 0`, from
  the adjugate identity `[u v w] o = (o·u)(v×w) + (o·v)(w×u) + (o·w)(u×v)` and cancellation of a
  nonzero coordinate;
* `axis` (`eq:axis`): the total function `u × v`, else `u × w`, else `(−u₁, u₀, 0)`, else
  `(u₂, 0, 0)`, written with the `0/1` selectors `sg(|·|)` so that it is a single term;
* `axis_spec` (`lem:axis`): for `u ≠ 0` with `[u v w] = 0`, `h = axis(u, v, w)` is nonzero and
  `h·u = h·v = h·w = 0`;
* `desargues_forward`, `desargues_reverse` (`thm:des-summary`): a nonzero centre `o` of the joins
  `j₁ = a×A`, `j₂ = b×B`, `j₃ = c×C` gives the nonzero axis `axis(X, Y, Z)` through the side
  intersections; conversely, for `[abc] ≠ 0 ≠ [ABC]`, a nonzero line through `X, Y, Z` gives the
  nonzero centre `axis(j₁, j₂, j₃)`; both via the universal identity
  `[X Y Z] = [abc][ABC][j₁ j₂ j₃]` (`Projective.desargues`, `lem:des-id`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.DesarguesInternal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.CevaMenelaus (nz zt_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrSg)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open Syn Matrix
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Nonzero integers -/

/-- `|x|` as a natural number. -/
abbrev D (x : ZT n) : PTm n := monus x.pos x.neg + monus x.neg x.pos

theorem zt_dich (x : ZT n) : Γ ⊢[PRAAx] nz x ⋎ (D x ≐ zero) := by
  refine .orE (zero_or_succ (D x)) (.orI₂ Prf.hyp0) (.orI₁ ?_)
  exact le_of_eq_add (d := pred (D x)) (Prf.hyp0.eqTrans (by ipra_ring))

theorem eq0_of_D {x : ZT n} (h : Γ ⊢[PRAAx] D x ≐ zero) : Γ ⊢[PRAAx] ZT.eq x (ZT.natLit 0) := by
  have e := le_antisymm (add_eq_zero_left h) (add_eq_zero_right h)
  have e' := natEq e
  apply deriveNat; simp only [ZT.natLit, ZT.ofNat]; ipra_simps
  linear_combination e'

theorem toZ_zero_of {x : ZT n} (h : Γ ⊢[PRAAx] D x ≐ zero) : ZT.toZ Γ x = 0 := by
  have e := ZT.toZ_eq (eq0_of_D h)
  simpa using e

theorem D_of_eq0 {x : ZT n} (h : Γ ⊢[PRAAx] ZT.eq x (ZT.natLit 0)) : Γ ⊢[PRAAx] D x ≐ zero := by
  have e : Γ ⊢[PRAAx] x.pos ≐ x.neg := by
    have h' := natEq h
    apply deriveNat; simp only [ZT.natLit, ZT.ofNat] at h'; ipra_simps
    linear_combination h'
  exact (congrAdd ((congrMonus e (.eqRefl _)).eqTrans (monus_self _))
    ((congrMonus e.eqSymm (.eqRefl _)).eqTrans (monus_self _))).eqTrans (add_zero _)

theorem nz_absurd {x : ZT n} (φ : Fm PTm n) (hx : Γ ⊢[PRAAx] nz x) (h : Γ ⊢[PRAAx] D x ≐ zero) : Γ ⊢[PRAAx] φ :=
  lt_zero_absurd φ (le_congr (.eqRefl _) h hx)

theorem nz_congr {x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq x y) (hx : Γ ⊢[PRAAx] nz x) : Γ ⊢[PRAAx] nz y := by
  refine .orE (zt_dich y) Prf.hyp0 ?_
  have ey := toZ_zero_of (Γ := (D y ≐ zero) :: Γ) Prf.hyp0
  have ex := ZT.toZ_eq (Γ := (D y ≐ zero) :: Γ) h.wk
  exact nz_absurd _ hx.wk (D_of_eq0 (ZT.derive (by rw [ex, ey]; simp)))

theorem nz_neg {x : ZT n} (hx : Γ ⊢[PRAAx] nz x) : Γ ⊢[PRAAx] nz (-x) :=
  le_congr (.eqRefl _) (add_comm _ _) hx

/-! ## Nonzero triples and selectors -/

/-- `u ≠ 0`: some component is nonzero. -/
abbrev nzV (u : Vec 3 n) : Fm PTm n := nz (u 0) ⋎ (nz (u 1) ⋎ nz (u 2))

/-- `[u ≠ 0]` as a `0/1` term. -/
abbrev sel (u : Vec 3 n) : PTm n := sg (D (u 0) + D (u 1) + D (u 2))

theorem sel_one {u : Vec 3 n} (h : Γ ⊢[PRAAx] nzV u) : Γ ⊢[PRAAx] sel u ≐ one := by
  have hl : Γ ⊢[PRAAx] le one (D (u 0) + D (u 1) + D (u 2)) := by
    refine .orE h ?_ (.orE Prf.hyp0 ?_ ?_)
    · exact le_trans Prf.hyp0 (le_of_eq_add (d := D (u 1) + D (u 2)) (by ipra_ring))
    · exact le_trans Prf.hyp0 (le_of_eq_add (d := D (u 0) + D (u 2)) (by ipra_ring))
    · exact le_trans Prf.hyp0 (le_of_eq_add (d := D (u 0) + D (u 1)) (by ipra_ring))
  have e := eq_add_of_le hl
  exact (congrSg (e.eqTrans (by ipra_ring))).eqTrans (sg_succ _)

theorem sel_zero {u : Vec 3 n} (h₀ : Γ ⊢[PRAAx] D (u 0) ≐ zero) (h₁ : Γ ⊢[PRAAx] D (u 1) ≐ zero)
    (h₂ : Γ ⊢[PRAAx] D (u 2) ≐ zero) : Γ ⊢[PRAAx] sel u ≐ zero := by
  have e₀ := natEq h₀; have e₁ := natEq h₁; have e₂ := natEq h₂
  exact (congrSg (by apply deriveNat; ipra_simps; linear_combination e₀ + e₁ + e₂)).eqTrans sg_zero

/-- Either `u ≠ 0` or all of its components vanish. -/
theorem vec_dich (u : Vec 3 n) :
    Γ ⊢[PRAAx] nzV u ⋎ ((D (u 0) ≐ zero) ⋏ ((D (u 1) ≐ zero) ⋏ (D (u 2) ≐ zero))) := by
  refine .orE (zt_dich (u 0)) (.orI₁ (.orI₁ Prf.hyp0)) ?_
  refine .orE (zt_dich (u 1)) (.orI₁ (.orI₂ (.orI₁ Prf.hyp0))) ?_
  refine .orE (zt_dich (u 2)) (.orI₁ (.orI₂ (.orI₂ Prf.hyp0))) ?_
  exact .orI₂ (.andI Prf.hyp1.wk (.andI Prf.hyp1 Prf.hyp0))

theorem toZ_sel_one {s : PTm n} (h : Γ ⊢[PRAAx] s ≐ one) :
    ZT.toZ Γ (ZT.ofNat s) = 1 ∧ ZT.toZ Γ (ZT.ofNat (monus one s)) = 0 := by
  have a := natEq h
  have b := natEq ((congrMonus (.eqRefl one) h).eqTrans (monus_self one))
  simp only [ZT.toZ_ofNat]; ipra_simps
  exact ⟨by linear_combination a, by linear_combination b⟩

theorem toZ_sel_zero {s : PTm n} (h : Γ ⊢[PRAAx] s ≐ zero) :
    ZT.toZ Γ (ZT.ofNat s) = 0 ∧ ZT.toZ Γ (ZT.ofNat (monus one s)) = 1 := by
  have a := natEq h
  have b := natEq ((congrMonus (.eqRefl one) h).eqTrans (monus_zero one))
  simp only [ZT.toZ_ofNat]; ipra_simps
  exact ⟨by linear_combination a, by linear_combination b⟩

/-! ## Incidence gives determinant zero -/

theorem adj3 {R : Type*} [CommRing R] (o u v w : Fin 3 → R) (i : Fin 3) :
    (u ⬝ᵥ (v ⨯₃ w)) * o i = (o ⬝ᵥ u) * (v ⨯₃ w) i + (o ⬝ᵥ v) * (w ⨯₃ u) i + (o ⬝ᵥ w) * (u ⨯₃ v) i := by
  fin_cases i <;> simp [crossProduct, dotProduct, Fin.sum_univ_three] <;> ring

theorem dot_zero {o u : Vec 3 n} (h : Γ ⊢[PRAAx] ZT.eq (Vec.dot o u) (ZT.natLit 0)) :
    Vec.toZ Γ o ⬝ᵥ Vec.toZ Γ u = 0 := by
  have e := ZT.toZ_eq h
  rw [Vec.toZ_dot, ZT.toZ_natLit] at e
  simpa using e

theorem inc_comp {o u v w : Vec 3 n} (i : Fin 3) (h₁ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o u) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o v) (ZT.natLit 0)) (h₃ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o w) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (o i * Vec.triple u v w) (o i * ZT.natLit 0) := by
  have a := adj3 (Vec.toZ Γ o) (Vec.toZ Γ u) (Vec.toZ Γ v) (Vec.toZ Γ w) i
  rw [dot_zero h₁, dot_zero h₂, dot_zero h₃] at a
  refine ZT.derive ?_
  rw [ZT.toZ_mul, ZT.toZ_mul, Vec.toZ_triple, ZT.toZ_natLit]
  simp only [Vec.toZ_apply, zero_mul, add_zero] at a
  linear_combination a

/-- `lem:inc-det`: a nonzero `o` with `o·u = o·v = o·w = 0` gives `[u v w] = 0`. -/
theorem inc_det {o u v w : Vec 3 n} (ho : Γ ⊢[PRAAx] nzV o) (h₁ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o u) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o v) (ZT.natLit 0)) (h₃ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o w) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Vec.triple u v w) (ZT.natLit 0) :=
  .orE ho (zt_cancel Prf.hyp0 (inc_comp 0 h₁.wk h₂.wk h₃.wk))
    (.orE Prf.hyp0 (zt_cancel Prf.hyp0 (inc_comp 1 h₁.wk.wk h₂.wk.wk h₃.wk.wk))
      (zt_cancel Prf.hyp0 (inc_comp 2 h₁.wk.wk h₂.wk.wk h₃.wk.wk)))

/-! ## The common-kernel algorithm -/

/-- `(−u₁, u₀, 0)`. -/
def tV (u : Vec 3 n) : Vec 3 n := ![-(u 1), u 0, ZT.natLit 0]
/-- `(u₂, 0, 0)`. -/
def qV (u : Vec 3 n) : Vec 3 n := ![u 2, ZT.natLit 0, ZT.natLit 0]

/-- `eq:axis`, with the branch tests as `0/1` selectors. -/
def axis (u v w : Vec 3 n) : Vec 3 n := fun i =>
  ZT.ofNat (sel (Vec.cross u v)) * Vec.cross u v i + ZT.ofNat (monus one (sel (Vec.cross u v))) *
    (ZT.ofNat (sel (Vec.cross u w)) * Vec.cross u w i + ZT.ofNat (monus one (sel (Vec.cross u w))) *
      (ZT.ofNat (sel (tV u)) * tV u i + ZT.ofNat (monus one (sel (tV u))) * qV u i))

/-- The conclusion of `lem:axis` for a candidate `h`. -/
abbrev kernel (h u v w : Vec 3 n) : Fm PTm n :=
  nzV h ⋏ (ZT.eq (Vec.dot h u) (ZT.natLit 0) ⋏ (ZT.eq (Vec.dot h v) (ZT.natLit 0) ⋏ ZT.eq (Vec.dot h w) (ZT.natLit 0)))

theorem kernel_congr {h X u v w : Vec 3 n} (hx : Vec.toZ Γ h = Vec.toZ Γ X) (k : Γ ⊢[PRAAx] kernel X u v w) :
    Γ ⊢[PRAAx] kernel h u v w := by
  have d : ∀ y : Vec 3 n, (Γ ⊢[PRAAx] ZT.eq (Vec.dot X y) (ZT.natLit 0)) → (Γ ⊢[PRAAx] ZT.eq (Vec.dot h y) (ZT.natLit 0)) :=
    fun y e => ZT.derive (by rw [Vec.toZ_dot, hx, ← Vec.toZ_dot]; exact ZT.toZ_eq e)
  have c : ∀ i, Γ ⊢[PRAAx] ZT.eq (X i) (h i) := fun i => ZT.derive (congrFun hx i).symm
  refine .andI ?_ (.andI (d u (Prf.andE₁ (Prf.andE₂ k))) (.andI (d v (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ k))))
    (d w (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ k))))))
  exact .orE (Prf.andE₁ k) (.orI₁ (nz_congr (c 0).wk Prf.hyp0))
    (.orE Prf.hyp0 (.orI₂ (.orI₁ (nz_congr (c 1).wk.wk Prf.hyp0))) (.orI₂ (.orI₂ (nz_congr (c 2).wk.wk Prf.hyp0))))

local macro "vexp" : tactic => `(tactic| simp only [Vec.toZ_dot, Vec.toZ_cross, ZT.toZ_natLit, dotProduct,
  crossProduct, Fin.sum_univ_three, Vec.toZ_apply, tV, qV, Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, LinearMap.mk₂_apply, ZT.toZ_neg, Nat.cast_zero,
  Vec.cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at *)

theorem triple_zero {u v w : Vec 3 n} (ht : Γ ⊢[PRAAx] ZT.eq (Vec.triple u v w) (ZT.natLit 0)) :
    Vec.toZ Γ u ⬝ᵥ (Vec.toZ Γ v ⨯₃ Vec.toZ Γ w) = 0 := by
  have e := ZT.toZ_eq ht
  rw [Vec.toZ_triple, ZT.toZ_natLit] at e
  simpa using e

/-- All components of `u` vanish. -/
abbrev allZero (u : Vec 3 n) : Fm PTm n := (D (u 0) ≐ zero) ⋏ ((D (u 1) ≐ zero) ⋏ (D (u 2) ≐ zero))

theorem sel_zero' {u : Vec 3 n} (h : Γ ⊢[PRAAx] allZero u) : Γ ⊢[PRAAx] sel u ≐ zero :=
  sel_zero (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ h))

theorem branch₁ {u v w : Vec 3 n} (h₁ : Γ ⊢[PRAAx] nzV (Vec.cross u v))
    (ht : Γ ⊢[PRAAx] ZT.eq (Vec.triple u v w) (ZT.natLit 0)) : Γ ⊢[PRAAx] kernel (axis u v w) u v w := by
  have s := toZ_sel_one (sel_one h₁)
  have hx : Vec.toZ Γ (axis u v w) = Vec.toZ Γ (Vec.cross u v) := by
    funext i; simp only [Vec.toZ_apply, axis, ZT.toZ_add, ZT.toZ_mul, s.1, s.2]; ring
  refine kernel_congr hx (.andI h₁ (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))))
  · vexp; ring
  · vexp; ring
  · have t := triple_zero ht; vexp; linear_combination t

theorem branch₂ {u v w : Vec 3 n} (h₀ : Γ ⊢[PRAAx] allZero (Vec.cross u v)) (h₂ : Γ ⊢[PRAAx] nzV (Vec.cross u w))
    (ht : Γ ⊢[PRAAx] ZT.eq (Vec.triple u v w) (ZT.natLit 0)) : Γ ⊢[PRAAx] kernel (axis u v w) u v w := by
  have s₁ := toZ_sel_zero (sel_zero' h₀); have s₂ := toZ_sel_one (sel_one h₂)
  have hx : Vec.toZ Γ (axis u v w) = Vec.toZ Γ (Vec.cross u w) := by
    funext i; simp only [Vec.toZ_apply, axis, ZT.toZ_add, ZT.toZ_mul, s₁.1, s₁.2, s₂.1, s₂.2]; ring
  refine kernel_congr hx (.andI h₂ (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))))
  · vexp; ring
  · have t := triple_zero ht; vexp; linear_combination -t
  · vexp; ring

theorem branch₃ {u v w : Vec 3 n} (h₀ : Γ ⊢[PRAAx] allZero (Vec.cross u v)) (h₀' : Γ ⊢[PRAAx] allZero (Vec.cross u w))
    (h₃ : Γ ⊢[PRAAx] nzV (tV u)) : Γ ⊢[PRAAx] kernel (axis u v w) u v w := by
  have s₁ := toZ_sel_zero (sel_zero' h₀); have s₂ := toZ_sel_zero (sel_zero' h₀')
  have s₃ := toZ_sel_one (sel_one h₃)
  have hx : Vec.toZ Γ (axis u v w) = Vec.toZ Γ (tV u) := by
    funext i; simp only [Vec.toZ_apply, axis, ZT.toZ_add, ZT.toZ_mul, s₁.1, s₁.2, s₂.1, s₂.2, s₃.1, s₃.2]; ring
  have c := toZ_zero_of (Prf.andE₂ (Prf.andE₂ h₀)); have c' := toZ_zero_of (Prf.andE₂ (Prf.andE₂ h₀'))
  refine kernel_congr hx (.andI h₃ (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))))
  · vexp; ring
  · vexp; linear_combination c
  · vexp; linear_combination c'

theorem branch₄ {u v w : Vec 3 n} (hu : Γ ⊢[PRAAx] nzV u) (h₀ : Γ ⊢[PRAAx] allZero (Vec.cross u v))
    (h₀' : Γ ⊢[PRAAx] allZero (Vec.cross u w)) (h₄ : Γ ⊢[PRAAx] allZero (tV u)) :
    Γ ⊢[PRAAx] kernel (axis u v w) u v w := by
  have s₁ := toZ_sel_zero (sel_zero' h₀); have s₂ := toZ_sel_zero (sel_zero' h₀')
  have s₃ := toZ_sel_zero (sel_zero' h₄)
  have hx : Vec.toZ Γ (axis u v w) = Vec.toZ Γ (qV u) := by
    funext i; simp only [Vec.toZ_apply, axis, ZT.toZ_add, ZT.toZ_mul, s₁.1, s₁.2, s₂.1, s₂.2, s₃.1, s₃.2]; ring
  have z₀ : Γ ⊢[PRAAx] D (u 0) ≐ zero := Prf.andE₁ (Prf.andE₂ h₄)
  have z₁ : Γ ⊢[PRAAx] D (-(u 1)) ≐ zero := Prf.andE₁ h₄
  have d₀ := toZ_zero_of z₀
  have c := toZ_zero_of (Prf.andE₁ (Prf.andE₂ h₀)); have c' := toZ_zero_of (Prf.andE₁ (Prf.andE₂ h₀'))
  have h2 : Γ ⊢[PRAAx] nz (u 2) :=
    .orE hu (nz_absurd _ Prf.hyp0 z₀.wk) (.orE Prf.hyp0 (nz_absurd _ (nz_neg Prf.hyp0) z₁.wk.wk) Prf.hyp0)
  refine kernel_congr hx (.andI (.orI₁ h2) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))))
  · vexp; linear_combination ZT.toZ Γ (u 2) * d₀
  · vexp; linear_combination c + ZT.toZ Γ (v 2) * d₀
  · vexp; linear_combination c' + ZT.toZ Γ (w 2) * d₀

/-- `lem:axis`: for `u ≠ 0` and `[u v w] = 0`, `axis(u, v, w)` is a nonzero common kernel vector. -/
theorem axis_spec {u v w : Vec 3 n} (hu : Γ ⊢[PRAAx] nzV u) (ht : Γ ⊢[PRAAx] ZT.eq (Vec.triple u v w) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] kernel (axis u v w) u v w := by
  refine .orE (vec_dich (Vec.cross u v)) (branch₁ Prf.hyp0 ht.wk) ?_
  refine .orE (vec_dich (Vec.cross u w)) (branch₂ Prf.hyp1 Prf.hyp0 ht.wk.wk) ?_
  exact .orE (vec_dich (tV u)) (branch₃ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)
    (branch₄ hu.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)

/-! ## Internal Desargues -/

section Desargues

/-- The intersection `(a × b) × (A × B)` of corresponding sides. -/
abbrev meet (a b A B : Vec 3 n) : Vec 3 n := Vec.cross (Vec.cross a b) (Vec.cross A B)

variable (a b c A B C : Vec 3 n)

/-- `lem:des-id` evaluated: `[X Y Z] = [abc][ABC][j₁ j₂ j₃]`. -/
theorem des_toZ : ZT.toZ Γ (Vec.triple (meet a b A B) (meet b c B C) (meet c a C A)) =
    ZT.toZ Γ (Vec.triple a b c) * ZT.toZ Γ (Vec.triple A B C) *
      ZT.toZ Γ (Vec.triple (Vec.cross a A) (Vec.cross b B) (Vec.cross c C)) := by
  simp only [Vec.toZ_triple, Vec.toZ_cross]
  exact Projective.desargues _ _ _ _ _ _

variable {a b c A B C}

/-- `thm:des-summary`, forward: a nonzero centre `o` of the joins gives the nonzero axis
`axis(X, Y, Z)` through the three side intersections (for `X ≠ 0`). -/
theorem desargues_forward {o : Vec 3 n} (ho : Γ ⊢[PRAAx] nzV o)
    (h₁ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o (Vec.cross a A)) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o (Vec.cross b B)) (ZT.natLit 0))
    (h₃ : Γ ⊢[PRAAx] ZT.eq (Vec.dot o (Vec.cross c C)) (ZT.natLit 0))
    (hX : Γ ⊢[PRAAx] nzV (meet a b A B)) :
    Γ ⊢[PRAAx] kernel (axis (meet a b A B) (meet b c B C) (meet c a C A))
      (meet a b A B) (meet b c B C) (meet c a C A) := by
  have tj := ZT.toZ_eq (inc_det ho h₁ h₂ h₃)
  refine axis_spec hX (ZT.derive ?_)
  rw [des_toZ, tj, ZT.toZ_natLit]; simp

/-- `thm:des-summary`, reverse: for nondegenerate triangles, a nonzero line `h` through the side
intersections gives the nonzero centre `axis(j₁, j₂, j₃)` (for `j₁ ≠ 0`). -/
theorem desargues_reverse {h : Vec 3 n} (hh : Γ ⊢[PRAAx] nzV h)
    (h₁ : Γ ⊢[PRAAx] ZT.eq (Vec.dot h (meet a b A B)) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Vec.dot h (meet b c B C)) (ZT.natLit 0))
    (h₃ : Γ ⊢[PRAAx] ZT.eq (Vec.dot h (meet c a C A)) (ZT.natLit 0))
    (habc : Γ ⊢[PRAAx] nz (Vec.triple a b c)) (hABC : Γ ⊢[PRAAx] nz (Vec.triple A B C))
    (hj : Γ ⊢[PRAAx] nzV (Vec.cross a A)) :
    Γ ⊢[PRAAx] kernel (axis (Vec.cross a A) (Vec.cross b B) (Vec.cross c C))
      (Vec.cross a A) (Vec.cross b B) (Vec.cross c C) := by
  have tx := ZT.toZ_eq (inc_det hh h₁ h₂ h₃)
  rw [des_toZ, ZT.toZ_natLit] at tx
  have e₁ : Γ ⊢[PRAAx] ZT.eq (Vec.triple a b c * (Vec.triple A B C * Vec.triple (Vec.cross a A) (Vec.cross b B) (Vec.cross c C)))
      (Vec.triple a b c * (Vec.triple A B C * ZT.natLit 0)) :=
    ZT.derive (by simp only [ZT.toZ_mul, ZT.toZ_natLit]; push_cast at tx ⊢; linear_combination tx)
  exact axis_spec hj (zt_cancel hABC (zt_cancel habc e₁))

end Desargues

end LeanProofs.IPRA.Geometry.DesarguesInternal
