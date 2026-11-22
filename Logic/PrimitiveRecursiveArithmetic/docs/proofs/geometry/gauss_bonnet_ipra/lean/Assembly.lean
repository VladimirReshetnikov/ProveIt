import Mathlib

/-!
# Gauss--Bonnet: the finite rational assembly identity

Status: source candidate, NOT compiler-checked in the authoring environment.
There are no `sorry` declarations or new axioms. This file is an ambient Lean
proof of finite algebra. It is NOT, by itself, a derivation in iPRA.
`IPRABridge.lean` gives the corresponding deep-embedding polynomial step.

The parameter `p` may be any rational number: the algebra does not assume that
it is pi. At approximation stage q it is the chosen rational pi approximation.
-/

namespace ConstructiveGaussBonnet

structure Counts where
  vi : ℕ
  vb : ℕ
  ei : ℕ
  eb : ℕ
  faces : ℕ
  incidence : 3 * faces = 2 * ei + eb
  boundary : eb = vb

/-- Euler characteristic in the common rational coefficient ring. -/
def Counts.eulerQ (c : Counts) : ℚ :=
  c.vi + c.vb - c.ei - c.eb + c.faces

/-- C: face curvature; B: boundary edges; I: paired interior edges;
    A: all corner angles. This is the sum of face residuals. -/
def faceResidual (c : Counts) (p C B I A : ℚ) : ℚ :=
  C + B + I + c.faces * p - A

/-- Theta: sum of exterior boundary angles. This is the sum of vertex
    residuals, with interior and boundary vertices treated separately. -/
def vertexResidual (c : Counts) (p A Theta : ℚ) : ℚ :=
  A + Theta - (2 * c.vi + c.vb) * p

/-- Exact local-to-global identity. All approximation errors stay visible. -/
theorem assembly_identity (c : Counts) (p C B I A Theta : ℚ) :
    C + B + Theta - 2 * p * c.eulerQ =
      faceResidual c p C B I A - I + vertexResidual c p A Theta := by
  have hf : (3 : ℚ) * c.faces = 2 * c.ei + c.eb := by
    exact_mod_cast c.incidence
  have hb : (c.eb : ℚ) = c.vb := by
    exact_mod_cast c.boundary
  unfold Counts.eulerQ faceResidual vertexResidual
  linear_combination -p * hf + p * hb

/-- Aggregate residual bound; per-cell bounds are added by finite induction. -/
theorem assembly_bound (c : Counts) (p C B I A Theta bf be bv : ℚ)
    (hF : |faceResidual c p C B I A| ≤ bf)
    (hE : |I| ≤ be)
    (hV : |vertexResidual c p A Theta| ≤ bv) :
    |C + B + Theta - 2 * p * c.eulerQ| ≤ bf + be + bv := by
  rw [assembly_identity]
  calc
    |faceResidual c p C B I A - I + vertexResidual c p A Theta| ≤
        |faceResidual c p C B I A - I| + |vertexResidual c p A Theta| :=
      abs_add _ _
    _ ≤ (|faceResidual c p C B I A| + |I|) +
        |vertexResidual c p A Theta| :=
      add_le_add_right (abs_sub _ _) _
    _ ≤ bf + be + bv := by linarith

/-- Polyhedral specialization once each Euclidean face has angle sum p. -/
theorem polyhedral_identity (c : Counts) (p : ℚ) :
    (2 * c.vi + c.vb) * p - c.faces * p = 2 * p * c.eulerQ := by
  have hf : (3 : ℚ) * c.faces = 2 * c.ei + c.eb := by
    exact_mod_cast c.incidence
  have hb : (c.eb : ℚ) = c.vb := by
    exact_mod_cast c.boundary
  unfold Counts.eulerQ
  linear_combination -p * hf + p * hb

def tetrahedronCounts : Counts :=
  ⟨4, 0, 6, 0, 4, by decide, by decide⟩

def twoTriangleDiskCounts : Counts :=
  ⟨0, 4, 1, 4, 2, by decide, by decide⟩

def nineVertexTorusCounts : Counts :=
  ⟨9, 0, 27, 0, 18, by decide, by decide⟩

def sixVertexProjectivePlaneCounts : Counts :=
  ⟨6, 0, 15, 0, 10, by decide, by decide⟩

example : tetrahedronCounts.eulerQ = 2 := by
  norm_num [Counts.eulerQ, tetrahedronCounts]

example : twoTriangleDiskCounts.eulerQ = 1 := by
  norm_num [Counts.eulerQ, twoTriangleDiskCounts]

example : nineVertexTorusCounts.eulerQ = 0 := by
  norm_num [Counts.eulerQ, nineVertexTorusCounts]

example : sixVertexProjectivePlaneCounts.eulerQ = 1 := by
  norm_num [Counts.eulerQ, sixVertexProjectivePlaneCounts]

end ConstructiveGaussBonnet
