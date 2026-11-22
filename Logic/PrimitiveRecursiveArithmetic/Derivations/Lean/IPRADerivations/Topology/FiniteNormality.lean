import IPRADerivations.Topology.FiniteClosureMaps
import IPRADerivations.Core.OrderCertificates

/-!
# Normality, two-valued Urysohn separators and quasi-metrics of finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, in the framework of
`Topology/FiniteInteriorClosure` (subsets are families of iPRA formulas; open = upward closed, closed =
downward closed, by derived implications), with connectedness by walks of the comparability graph
(`Topology/FiniteClosureMaps`):

* F18 (`thm:finite-normal`, sufficiency) and F19 (`thm:finite-urysohn`): if every component has a point below
  all of its points, then for disjoint closed `A`, `B` the union `C_A` of the components meeting `A`
  ("Let `C_A` be the union of comparability components meeting `A`") is clopen (`compUnion_clopen`), contains
  `A` (`sub_compUnion`) and misses `B` (`compUnion_disjoint`, "If a closed set meets a component, downward
  closure forces it to contain that component's least class"). `urysohn` packages the two-valued separator:
  `C_A` and its complement are disjoint open neighbourhoods of `A` and `B`;
* F22 (`thm:finite-quasi`): `d(x, y) = 0` for `x ≼ y` and `1` otherwise satisfies `d(x, x) = 0` and the
  triangle inequality (`qd_refl`, `qd_triangle`), and its forward ball of radius `1` is `↑x`
  (`qd_ball`, `qd_ball_out`);
* F21 (`thm:finite-metric`, the metric half): for the identity relation the same table is the discrete
  metric, symmetric and satisfying the triangle inequality (`discrete_symm`, `discrete_triangle`).
-/

namespace LeanProofs.IPRA.Topology.FiniteNormality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open LeanProofs.IPRA.Topology.FiniteClosureMaps (comp)
open LeanProofs.IPRA.Foundations.ObservationCut.Finality (Walk)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n k : ℕ} {Γ : List (Fm PTm n)} {rel : Fin k → Fin k → Prop} [DecidableRel rel]

/-! ## F18 and F19 -/

open Classical in
/-- `C_A(x) = ⋁_{a ~ x} A a`: the union of the components meeting `A`. -/
noncomputable def compUnion (rel : Fin k → Fin k → Prop) (A : Fin k → Fm PTm n) (x : Fin k) : Fm PTm n :=
  disjFin fun a => if Walk (comp rel) a x then A a else Fm.bot

theorem sub_compUnion (A : Fin k → Fm PTm n) (x : Fin k) : Γ ⊢[PRAAx] A x ⟶ compUnion rel A x :=
  .impI (disjFin_intro x (by beta_reduce; rw [if_pos (Walk.trivial x)]; exact Prf.hyp0))

theorem compUnion_step (A : Fin k → Fm PTm n) {x y : Fin k} (e : comp rel x y) :
    Γ ⊢[PRAAx] compUnion rel A x ⟶ compUnion rel A y :=
  disjFin_imp fun a => by
    beta_reduce
    by_cases h : Walk (comp rel) a x
    · rw [if_pos h]
      exact .impI (disjFin_intro a (by beta_reduce; rw [if_pos (Walk.join h (Walk.edge e))]; exact Prf.hyp0))
    · rw [if_neg h]; exact .impI (.botE _ Prf.hyp0)

/-- `C_A` is open and closed. -/
theorem compUnion_clopen (A : Fin k → Fm PTm n) :
    IsOpen rel Γ (compUnion rel A) ∧ IsClosed rel Γ (compUnion rel A) :=
  ⟨fun _ _ e => compUnion_step A (.inl e), fun _ _ e => compUnion_step A (.inr e)⟩

/-- If every component has a point below all its points, `C_A` misses every closed `B` disjoint from `A`. -/
theorem compUnion_disjoint {A B : Fin k → Fm PTm n} (hA : IsClosed rel Γ A) (hB : IsClosed rel Γ B)
    (hdisj : ∀ x, Γ ⊢[PRAAx] A x ⟶ (B x ⟶ Fm.bot))
    (hleast : ∀ x, ∃ b, ∀ y, Walk (comp rel) x y → rel b y) (x : Fin k) :
    Γ ⊢[PRAAx] compUnion rel A x ⟶ (B x ⟶ Fm.bot) :=
  disjFin_imp fun a => by
    beta_reduce
    by_cases h : Walk (comp rel) a x
    · rw [if_pos h]
      obtain ⟨b, hb⟩ := hleast a
      have hAb : (B x :: A a :: Γ) ⊢[PRAAx] A b := .impE (hA b a (hb a (.trivial a))).wk.wk Prf.hyp1
      have hBb : (B x :: A a :: Γ) ⊢[PRAAx] B b := .impE (hB b x (hb x h)).wk.wk Prf.hyp0
      exact .impI (.impI (.impE (.impE (hdisj b).wk.wk hAb) hBb))
    · rw [if_neg h]; exact .impI (.botE _ Prf.hyp0)

/-- The two-valued Urysohn separator: `C_A` is clopen, `A ⊆ C_A`, `B ⊆ ¬C_A`, and `C_A`, `¬C_A` are disjoint
open neighbourhoods of `A` and `B`. -/
theorem urysohn {A B : Fin k → Fm PTm n} (hA : IsClosed rel Γ A) (hB : IsClosed rel Γ B)
    (hdisj : ∀ x, Γ ⊢[PRAAx] A x ⟶ (B x ⟶ Fm.bot))
    (hleast : ∀ x, ∃ b, ∀ y, Walk (comp rel) x y → rel b y) :
    IsOpen rel Γ (compUnion rel A) ∧ IsClosed rel Γ (compUnion rel A) ∧
    IsOpen rel Γ (fun x => neg (compUnion rel A x)) ∧
    (∀ x, Γ ⊢[PRAAx] A x ⟶ compUnion rel A x) ∧ (∀ x, Γ ⊢[PRAAx] B x ⟶ neg (compUnion rel A x)) := by
  obtain ⟨hO, hC⟩ := compUnion_clopen (Γ := Γ) (rel := rel) A
  refine ⟨hO, hC, fun x y e => ?_, sub_compUnion A, fun x => ?_⟩
  · exact .impI (.impI (.impE Prf.hyp1 (.impE (hC x y e).wk.wk Prf.hyp0)))
  · have d := compUnion_disjoint hA hB hdisj hleast x
    exact .impI (.impI (.impE (.impE d.wk.wk Prf.hyp0) Prf.hyp1))

/-! ## F22 and F21 -/

/-- `d(x, y) = 0` if `x ≼ y`, else `1`. -/
def qd (rel : Fin k → Fin k → Prop) [DecidableRel rel] (x y : Fin k) : PTm n :=
  if rel x y then num 0 else num 1

theorem qd_refl (hrefl : ∀ x, rel x x) (x : Fin k) : Γ ⊢[PRAAx] qd rel x x ≐ num 0 := by
  unfold qd; rw [if_pos (hrefl x)]; exact .eqRefl _

theorem qd_triangle (htrans : ∀ x y z, rel x y → rel y z → rel x z) (x y z : Fin k) :
    Γ ⊢[PRAAx] le (qd rel x z) (qd rel x y + qd rel y z) := by
  unfold qd
  by_cases hxz : rel x z <;> by_cases hxy : rel x y <;> by_cases hyz : rel y z <;>
    simp only [hxz, hxy, hyz, ↓reduceIte]
  all_goals first
    | exact absurd (htrans x y z hxy hyz) hxz
    | ipra_le 0
    | ipra_le 1
    | ipra_le 2

/-- The forward ball of radius `1` about `x` contains `↑x` … -/
theorem qd_ball {x y : Fin k} (h : rel x y) : Γ ⊢[PRAAx] lt (qd rel x y) (num 1) := by
  unfold qd; rw [if_pos h]
  show Γ ⊢[PRAAx] le (succ (num 0)) (num 1)
  ipra_le 0

/-- … and nothing else. -/
theorem qd_ball_out {x y : Fin k} (h : ¬ rel x y) : Γ ⊢[PRAAx] lt (qd rel x y) (num 1) ⟶ Fm.bot := by
  unfold qd; rw [if_neg h]
  exact .impI (LeanProofs.IPRA.lt_irrefl _ _ Prf.hyp0)

/-- The identity relation. -/
def dsc (x y : Fin k) : Prop := x = y

instance : DecidableRel (dsc (k := k)) := fun x y => inferInstanceAs (Decidable (x = y))

/-- The discrete metric is symmetric. -/
theorem discrete_symm (x y : Fin k) : (qd dsc x y : PTm n) = qd dsc y x := by
  unfold qd dsc
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

theorem discrete_triangle (x y z : Fin k) :
    Γ ⊢[PRAAx] le (qd dsc x z) (qd dsc x y + qd dsc y z) :=
  qd_triangle (rel := dsc) (fun _ _ _ (h₁ : dsc _ _) (h₂ : dsc _ _) => (h₁.trans h₂ : dsc _ _)) x y z

end LeanProofs.IPRA.Topology.FiniteNormality
