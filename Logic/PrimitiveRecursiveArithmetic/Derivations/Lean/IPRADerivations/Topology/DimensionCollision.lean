import IPRADerivations.Topology.DimensionSchema
import IPRADerivations.Topology.DimensionAlternative

/-!
# Effective approximate face collision (`dimension_invariance_ipra`, `thm:collision`)

Packet: `topology/dimension_invariance_ipra`, `thm:collision`: "If `d > m` and `f` has this
presentation, then for every `a ∈ ℕ` a primitive recursive construction produces `i` and rational
`q, q' ∈ C_d` such that `q_i = 0`, `q'_i = 1`, `‖f(q) − f(q')‖ < 2^{−a}`." The proof samples
`F(v) = A(v/N, p)` at the scales `eq:scales` and runs `thm:alternative`; the large-variation
alternative is excluded by the modulus, and for the returned opposite-face vertices
`‖f(q) − f(q')‖ ≤ dist(F(u), F(v)) + 2^{1−p} < 2^{−a}`.

Here, for every source dimension `D = d' + 1`, every `m < D` and all PR terms `A, μ` coded as in
`Topology/DimensionSchema`, with `eq:U` (`Uhyp`, the rational-sample consequence of the evaluation
and modulus hypotheses): the construction is the family of searches `searchI g` of
`Topology/DimensionAlternative` on the sampled table at the base `⟨2^{μ(k)}, a⟩`, and
`collision` is the closed sentence

  `∀ a. eq:U → ⋁_g (μ_g < bound ∧ u_g = 0 ∧ v_g = N ∧ outI(u, v, p, a) = 0)`

for the decoded points `u, v` of the least witness `μ_g`, where `outI = 0` is
`dist(A(u/N, p), A(v/N, p)) + 2^{1−p} < 2^{−a}`, the arithmetic bound from which the real
statement follows by `eq:eval` (`q = u/N`, `q' = v/N`, `q_i = 0`, `q'_i = 1`). Proof: a successful
search decodes to such a pair (`meaning`, by `DimensionSchema.sep_arith`); if every search returns
its bound, `eq:sep` holds (`DimensionAlternative.sep_of_search`), and `eq:U` gives `eq:small`
(`DimensionSchema.small_from_U`), which `DimensionRational.rat_no_table` refutes. The passage to
real numbers (`eq:eval` itself) is not formalized.
-/

namespace LeanProofs.IPRA.Topology.DimensionCollision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Search (mu)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.DigitCodes
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)
open LeanProofs.IPRA.Topology.DimensionOccupancy
open LeanProofs.IPRA.Topology.DimensionRational
open LeanProofs.IPRA.Topology.DimensionSchema
open LeanProofs.IPRA.Topology.DimensionAlternative
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)

set_option autoImplicit false

variable {n : ℕ}

section Collision

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

/-- The search for coordinate `g` on the sampled table. -/
abbrev sI (g : ℕ) : PTm 2 := searchI d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS g

/-- The decoded low point of a code. -/
abbrev uOf (c b : PTm n) : PTm n := dec (d' + 1) (P1 b) c b

/-- The decoded high point of a code. -/
abbrev vOf (c b : PTm n) : PTm n := dec (d' + 1) (P1 b) (quoK (d' + 1) (P1 b) c) b

/-- The output of the construction for coordinate `g`: the least witness is below the bound, its
points lie on the lower and upper `g`-faces, and their samples satisfy
`dist(A(u/N, p), A(v/N, p)) + 2^{1−p} < 2^{−a}`. -/
def collWit (g : ℕ) (a : PTm n) : Fm PTm n :=
  lt (mu (sI d' m AP AQ AR g) (BI d' (bOf d' μ a)) (bOf d' μ a)) (BI d' (bOf d' μ a)) ⋏
    ((proj (d' - g) (uOf d' (mu (sI d' m AP AQ AR g) (BI d' (bOf d' μ a)) (bOf d' μ a)) (bOf d' μ a)) ≐ zero) ⋏
      ((proj (d' - g) (vOf d' (mu (sI d' m AP AQ AR g) (BI d' (bOf d' μ a)) (bOf d' μ a)) (bOf d' μ a)) ≐
          fstT (bOf d' μ a)) ⋏
        (outI m AP AQ AR (uOf d' (mu (sI d' m AP AQ AR g) (BI d' (bOf d' μ a)) (bOf d' μ a)) (bOf d' μ a))
          (vOf d' (mu (sI d' m AP AQ AR g) (BI d' (bOf d' μ a)) (bOf d' μ a)) (bOf d' μ a))
          (succ (kOf d' a)) a ≐ zero)))

theorem add_zero_right {Γ : List (Fm PTm n)} {x y : PTm n} (h : Γ ⊢[PRAAx] x + y ≐ zero) : Γ ⊢[PRAAx] y ≐ zero :=
  add_eq_zero_left ((add_comm _ _).eqTrans h)

/-- A passed check of `searchI g` means an `h`-close pair on the `g`-faces, and the `h`-closeness is
the collision bound. -/
theorem meaning {Γ : List (Fm PTm n)} {g : ℕ} {a u v : PTm n}
    (hu : Γ ⊢[PRAAx] tl (d' + 1) u ≐ bOf d' μ a) (hv : Γ ⊢[PRAAx] tl (d' + 1) v ≐ bOf d' μ a)
    (h : Γ ⊢[PRAAx] fBodyI d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS g u v (bOf d' μ a) ≐ zero) :
    Γ ⊢[PRAAx] (proj (d' - g) u ≐ zero) ⋏ ((proj (d' - g) v ≐ fstT (bOf d' μ a)) ⋏
      (outI m AP AQ AR u v (succ (kOf d' a)) a ≐ zero)) := by
  have h4 := add_eq_zero_left h
  have hS := add_zero_right h
  have h3 := add_eq_zero_left h4
  have hD := add_zero_right h4
  have hsg := add_zero_right h3
  -- `u_g = 0`
  have hu0 : Γ ⊢[PRAAx] proj (d' - g) u ≐ zero := eq_zero_of_sg hsg
  -- `v_g = N`
  have hvN : Γ ⊢[PRAAx] proj (d' - g) v ≐ fstT (bOf d' μ a) :=
    le_antisymm (add_eq_zero_left hD) (add_zero_right hD)
  -- every entry is `h`-close, hence the collision bound
  refine .andI hu0 (.andI hvN (fsum_eq_zero (fun j => ?_)))
  have hj := fsum_zero_elim m _ hS j
  have hlt : Γ ⊢[PRAAx] lt (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v)
      (thr m (Rt d' m AR) hnS j u v (bOf d' μ a)) := by
    refine .orE (lt_or_le (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v)
      (thr m (Rt d' m AR) hnS j u v (bOf d' μ a))) Prf.hyp0 ?_
    refine .botE _ (succ_ne_zero (a := zero) ?_)
    have e0 : (le (thr m (Rt d' m AR) hnS j u v (bOf d' μ a))
        (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v) :: Γ) ⊢[PRAAx]
        closeBit m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS j u v (bOf d' μ a) ≐ zero :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans Signum.sg_zero
    exact (monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) e0).eqSymm.eqTrans hj.wk)
  have c := lt_congr (congrMul (hd_eq d' μ) (gap_eq d' m AP AQ AR μ j hu hv)) (thr_eq d' m AR μ j hu hv) hlt
  have hp : Γ ⊢[PRAAx] pw two (succ (kOf d' a)) ≐ pw two a * pw two (num (d' + 4)) * two :=
    (pw_succ two _).eqTrans (congrMul (pw_add two a (num (d' + 4))) (.eqRefl _))
  exact sep_arith d' (eq_add_of_le c) (pw_pos one a) (pw16 d') (pw_F d') hp (pw_add two a _) (pw_succ two a)

theorem coll_core (hdm : m < d' + 1) {Γ : List (Fm PTm n)} {a : PTm n}
    (hU : Γ ⊢[PRAAx] Uhyp d' m AP AQ AR μ) :
    Γ ⊢[PRAAx] bigOr (d' + 1) (fun g => collWit d' m AP AQ AR μ g.val a) := by
  refine bigOr_intro _ _ (fun g => mu (sI d' m AP AQ AR g.val) (BI d' (bOf d' μ a)) (bOf d' μ a) ≐ BI d' (bOf d' μ a))
    (fun g => ?_) (fun Δ hext hA => ?_)
  · refine .orE (search_cases (sI d' m AP AQ AR g.val) (BI d' (bOf d' μ a)) (bOf d' μ a)) (.orI₁ ?_) (.orI₂ Prf.hyp0)
    have hc : ((lt (mu (sI d' m AP AQ AR g.val) (BI d' (bOf d' μ a)) (bOf d' μ a)) (BI d' (bOf d' μ a)) ⋏
        (inst2 (sI d' m AP AQ AR g.val) (mu (sI d' m AP AQ AR g.val) (BI d' (bOf d' μ a)) (bOf d' μ a))
          (bOf d' μ a) ≐ zero)) :: Γ) ⊢[PRAAx]
        inst2 (sI d' m AP AQ AR g.val) (mu (sI d' m AP AQ AR g.val) (BI d' (bOf d' μ a)) (bOf d' μ a))
          (bOf d' μ a) ≐ zero := Prf.andE₂ Prf.hyp0
    exact .andI (Prf.andE₁ Prf.hyp0) (meaning d' m AP AQ AR μ (tl_dec _ _ _ _) (tl_dec _ _ _ _) (by rw [← inst_searchI]; exact hc))
  · refine rat_no_table d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS hdm (b := bOf d' μ a)
      (fun g hg => sep_of_search d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS (hA ⟨g, by omega⟩))
      (small_from_U d' m AP AQ AR μ (hext _ hU))

/-- `∀ a. eq:U → ⋁_g collWit g a`. -/
def collisionFormula : Fm PTm 1 :=
  Uhyp d' m AP AQ AR μ ⟶ bigOr (d' + 1) (fun g => collWit d' m AP AQ AR μ g.val (Syn.var 0))

/-- `thm:collision` (arithmetic form) for every source dimension `D = d' + 1`, every `m < D` and all
PR `A, μ`, as a closed sentence of iPRA. -/
theorem collision (hdm : m < d' + 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (collisionFormula d' m AP AQ AR μ) :=
  closeUniv 1 (.impI (coll_core d' m AP AQ AR μ hdm Prf.hyp0))

end Collision

end LeanProofs.IPRA.Topology.DimensionCollision
