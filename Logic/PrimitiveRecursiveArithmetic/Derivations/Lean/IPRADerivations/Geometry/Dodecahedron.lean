import IPRADerivations.Core.PolynomialImplications

/-!
# The exact dodecahedron certificate over `ℤ[φ]` (`pentagonal_tiling_ipra`)

Packet: `geometry/pentagonal_tiling_ipra_2026-11-16`, Section "Spherical pentagonal tilings",
`thm:dodecahedron` ("Exact dodecahedron certificate"): the convex hull of the twenty points
`(±1, ±1, ±1)`, `(0, ±φ⁻¹, ±φ)`, `(±φ⁻¹, ±φ, 0)`, `(±φ, 0, ±φ⁻¹)` with `φ = (1 + √5)/2`,
`φ⁻¹ = φ − 1`, is a regular dodecahedron.

## The encoding of `ℚ(√5)`

All coordinates lie in `ℤ[φ]`, `φ² = φ + 1`. An element `a + bφ` is the pair `⟨a, b⟩`
(`Gold`), with the product `(a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ`. This is an honest
encoding: every statement below is a closed sentence about integer numerals, not an
implication from an unsatisfiable hypothesis such as `φ² = φ + 1` for an integer `φ`. A claim
`g = g′` in `ℤ[φ]` is stated as the polynomial identity `emb g = emb g′`, `emb ⟨a, b⟩ = a + bX`
in one free variable `X`; its universal closure gives `a = a′` (at `X = 0`) and `b = b′` (at
`X = 1`).

**Positivity.** An element `g` with `g φᵏ = c₀ + c₁φ`, `c₀, c₁ ≥ 0` not both `0`, is positive in
the real reading, since `φ > 0` and `φᵏ > 0`. The script found such a multiplier `φᵏ`
(`phiPow k`) for every positivity claim; Lean checks the identity.

## The certificate

The script that generated this module reproduces the vertex set of the packet's
`certificates/dodecahedron_qsqrt5.json` (converted by `√5 = 2φ − 1`) and proposes the data
below; every arithmetic claim is checked by Lean:

* `radius_i`: `|Vᵢ|² = 3` for the twenty vertices;
* `dist_i_j`: the squared distance of each of the 190 pairs; it is one of `8 − 4φ`, `4`, `8`,
  `4 + 4φ`, `12`, and the 30 pairs at `8 − 4φ = 6 − 2√5` are the edges (`edges`);
* `least_1` … `least_4`: each other value exceeds `8 − 4φ` (positivity certificates), so
  `6 − 2√5` is the least nonzero squared distance;
* for each of the twelve faces `faceF` (the simple five-cycles of the edge graph, proposed by the
  script), with the normal `NF = ±(B − A) × (C − A)`: `plane_F_t` (the two remaining vertices
  of the cycle lie in the plane of the first three), `normal_F` (`NF ≠ 0`), and `side_F_t` (each
  of the fifteen other vertices lies strictly on the inner side: `−NF · (P − A) > 0`).

With the distance list, the five edges of each face have the square `8 − 4φ` and its five
diagonals the square `4` (`dist_i_j`), so every face is a regular supporting pentagon of the
hull. The incidence counts of the packet (each vertex of degree `3`, each edge in exactly two
of the twelve faces, `V − E + F = 20 − 30 + 12 = 2`) are facts about the lists `edges` and
`faces`; they were checked by the generating script and are not stated as sentences here
(`V + F = E + 2` is `Geometry/PentagonArithmetic`). The conclusion that the twelve faces are
exactly the boundary of the hull, and the radial projection to the sphere, are not derived.
-/

namespace LeanProofs.IPRA.Geometry.Dodecahedron

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- An element `re + im φ` of `ℤ[φ]`, `φ² = φ + 1`, with integer numeral components. -/
structure Gold where
  /-- The rational part. -/
  re : ZExp 1
  /-- The coefficient of `φ`. -/
  im : ZExp 1

namespace Gold

instance : Add Gold := ⟨fun g h => ⟨g.re + h.re, g.im + h.im⟩⟩
instance : Sub Gold := ⟨fun g h => ⟨g.re - h.re, g.im - h.im⟩⟩
instance : Neg Gold := ⟨fun g => ⟨-g.re, -g.im⟩⟩
/-- `(a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ`. -/
instance : Mul Gold :=
  ⟨fun g h => ⟨g.re * h.re + g.im * h.im, g.re * h.im + g.im * h.re + g.im * h.im⟩⟩

@[simp] theorem add_re (g h : Gold) : (g + h).re = g.re + h.re := rfl
@[simp] theorem add_im (g h : Gold) : (g + h).im = g.im + h.im := rfl
@[simp] theorem sub_re (g h : Gold) : (g - h).re = g.re - h.re := rfl
@[simp] theorem sub_im (g h : Gold) : (g - h).im = g.im - h.im := rfl
@[simp] theorem neg_re (g : Gold) : (-g).re = -g.re := rfl
@[simp] theorem neg_im (g : Gold) : (-g).im = -g.im := rfl
@[simp] theorem mul_re (g h : Gold) : (g * h).re = g.re * h.re + g.im * h.im := rfl
@[simp] theorem mul_im (g h : Gold) : (g * h).im = g.re * h.im + g.im * h.re + g.im * h.im := rfl

end Gold

/-- The image `re + im X` of an element of `ℤ[φ]`, in one free variable `X`. -/
def emb (g : Gold) : ZExp 1 := g.re + g.im * var 0

/-- `φᵏ`. -/
def phiPow : ℕ → Gold
  | 0 => ⟨1, 0⟩
  | k + 1 => phiPow k * ⟨0, 1⟩

/-- A point of `ℤ[φ]³`. -/
structure G3 where
  /-- The first coordinate. -/
  x : Gold
  /-- The second coordinate. -/
  y : Gold
  /-- The third coordinate. -/
  z : Gold

instance : Sub G3 := ⟨fun P Q => ⟨P.x - Q.x, P.y - Q.y, P.z - Q.z⟩⟩
instance : Neg G3 := ⟨fun P => ⟨-P.x, -P.y, -P.z⟩⟩

@[simp] theorem G3.sub_x (P Q : G3) : (P - Q).x = P.x - Q.x := rfl
@[simp] theorem G3.sub_y (P Q : G3) : (P - Q).y = P.y - Q.y := rfl
@[simp] theorem G3.sub_z (P Q : G3) : (P - Q).z = P.z - Q.z := rfl
@[simp] theorem G3.neg_x (P : G3) : (-P).x = -P.x := rfl
@[simp] theorem G3.neg_y (P : G3) : (-P).y = -P.y := rfl
@[simp] theorem G3.neg_z (P : G3) : (-P).z = -P.z := rfl

/-- The dot product in `ℤ[φ]³`. -/
def dot3 (P Q : G3) : Gold := P.x * Q.x + P.y * Q.y + P.z * Q.z

/-- The cross product in `ℤ[φ]³`. -/
def cross3 (P Q : G3) : G3 :=
  ⟨P.y * Q.z - P.z * Q.y, P.z * Q.x - P.x * Q.z, P.x * Q.y - P.y * Q.x⟩

/-! ## The twenty vertices -/

/-- Vertex 0. -/
def V0 : G3 := ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩
/-- Vertex 1. -/
def V1 : G3 := ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨(-1), 0⟩⟩
/-- Vertex 2. -/
def V2 : G3 := ⟨⟨1, 0⟩, ⟨(-1), 0⟩, ⟨1, 0⟩⟩
/-- Vertex 3. -/
def V3 : G3 := ⟨⟨1, 0⟩, ⟨(-1), 0⟩, ⟨(-1), 0⟩⟩
/-- Vertex 4. -/
def V4 : G3 := ⟨⟨(-1), 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩
/-- Vertex 5. -/
def V5 : G3 := ⟨⟨(-1), 0⟩, ⟨1, 0⟩, ⟨(-1), 0⟩⟩
/-- Vertex 6. -/
def V6 : G3 := ⟨⟨(-1), 0⟩, ⟨(-1), 0⟩, ⟨1, 0⟩⟩
/-- Vertex 7. -/
def V7 : G3 := ⟨⟨(-1), 0⟩, ⟨(-1), 0⟩, ⟨(-1), 0⟩⟩
/-- Vertex 8. -/
def V8 : G3 := ⟨⟨0, 0⟩, ⟨(-1), 1⟩, ⟨0, 1⟩⟩
/-- Vertex 9. -/
def V9 : G3 := ⟨⟨0, 0⟩, ⟨(-1), 1⟩, ⟨0, (-1)⟩⟩
/-- Vertex 10. -/
def V10 : G3 := ⟨⟨0, 0⟩, ⟨1, (-1)⟩, ⟨0, 1⟩⟩
/-- Vertex 11. -/
def V11 : G3 := ⟨⟨0, 0⟩, ⟨1, (-1)⟩, ⟨0, (-1)⟩⟩
/-- Vertex 12. -/
def V12 : G3 := ⟨⟨(-1), 1⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩
/-- Vertex 13. -/
def V13 : G3 := ⟨⟨(-1), 1⟩, ⟨0, (-1)⟩, ⟨0, 0⟩⟩
/-- Vertex 14. -/
def V14 : G3 := ⟨⟨1, (-1)⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩
/-- Vertex 15. -/
def V15 : G3 := ⟨⟨1, (-1)⟩, ⟨0, (-1)⟩, ⟨0, 0⟩⟩
/-- Vertex 16. -/
def V16 : G3 := ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨(-1), 1⟩⟩
/-- Vertex 17. -/
def V17 : G3 := ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨1, (-1)⟩⟩
/-- Vertex 18. -/
def V18 : G3 := ⟨⟨0, (-1)⟩, ⟨0, 0⟩, ⟨(-1), 1⟩⟩
/-- Vertex 19. -/
def V19 : G3 := ⟨⟨0, (-1)⟩, ⟨0, 0⟩, ⟨1, (-1)⟩⟩
/-- The face `V0, V8, V4, V14, V12`. -/
def face0 : List (Fin 20) := [0, 8, 4, 14, 12]
/-- The outward normal of face 0: `±(V8 − V0) × (V4 − V0)`. -/
def N0 : G3 := -cross3 (V8 - V0) (V4 - V0)
/-- The face `V0, V8, V10, V2, V16`. -/
def face1 : List (Fin 20) := [0, 8, 10, 2, 16]
/-- The outward normal of face 1: `±(V8 − V0) × (V10 − V0)`. -/
def N1 : G3 := cross3 (V8 - V0) (V10 - V0)
/-- The face `V0, V12, V1, V17, V16`. -/
def face2 : List (Fin 20) := [0, 12, 1, 17, 16]
/-- The outward normal of face 2: `±(V12 − V0) × (V1 − V0)`. -/
def N2 : G3 := -cross3 (V12 - V0) (V1 - V0)
/-- The face `V1, V9, V5, V14, V12`. -/
def face3 : List (Fin 20) := [1, 9, 5, 14, 12]
/-- The outward normal of face 3: `±(V9 − V1) × (V5 − V1)`. -/
def N3 : G3 := cross3 (V9 - V1) (V5 - V1)
/-- The face `V1, V9, V11, V3, V17`. -/
def face4 : List (Fin 20) := [1, 9, 11, 3, 17]
/-- The outward normal of face 4: `±(V9 − V1) × (V11 − V1)`. -/
def N4 : G3 := -cross3 (V9 - V1) (V11 - V1)
/-- The face `V2, V10, V6, V15, V13`. -/
def face5 : List (Fin 20) := [2, 10, 6, 15, 13]
/-- The outward normal of face 5: `±(V10 − V2) × (V6 − V2)`. -/
def N5 : G3 := cross3 (V10 - V2) (V6 - V2)
/-- The face `V2, V13, V3, V17, V16`. -/
def face6 : List (Fin 20) := [2, 13, 3, 17, 16]
/-- The outward normal of face 6: `±(V13 − V2) × (V3 − V2)`. -/
def N6 : G3 := cross3 (V13 - V2) (V3 - V2)
/-- The face `V3, V11, V7, V15, V13`. -/
def face7 : List (Fin 20) := [3, 11, 7, 15, 13]
/-- The outward normal of face 7: `±(V11 − V3) × (V7 − V3)`. -/
def N7 : G3 := -cross3 (V11 - V3) (V7 - V3)
/-- The face `V4, V8, V10, V6, V18`. -/
def face8 : List (Fin 20) := [4, 8, 10, 6, 18]
/-- The outward normal of face 8: `±(V8 − V4) × (V10 − V4)`. -/
def N8 : G3 := -cross3 (V8 - V4) (V10 - V4)
/-- The face `V4, V14, V5, V19, V18`. -/
def face9 : List (Fin 20) := [4, 14, 5, 19, 18]
/-- The outward normal of face 9: `±(V14 − V4) × (V5 − V4)`. -/
def N9 : G3 := cross3 (V14 - V4) (V5 - V4)
/-- The face `V5, V9, V11, V7, V19`. -/
def face10 : List (Fin 20) := [5, 9, 11, 7, 19]
/-- The outward normal of face 10: `±(V9 − V5) × (V11 − V5)`. -/
def N10 : G3 := cross3 (V9 - V5) (V11 - V5)
/-- The face `V6, V15, V7, V19, V18`. -/
def face11 : List (Fin 20) := [6, 15, 7, 19, 18]
/-- The outward normal of face 11: `±(V15 − V6) × (V7 − V6)`. -/
def N11 : G3 := -cross3 (V15 - V6) (V7 - V6)
/-! ## The incidence data -/

/-- The thirty edges: the pairs at the edge square (`dist_i_j` with value `8 − 4φ`). -/
def edges : List (ℕ × ℕ) := [(0, 8), (0, 12), (0, 16), (1, 9), (1, 12), (1, 17), (2, 10), (2, 13),
    (2, 16), (3, 11), (3, 13), (3, 17), (4, 8), (4, 14), (4, 18), (5, 9), (5, 14), (5, 19), (6,
    10), (6, 15), (6, 18), (7, 11), (7, 15), (7, 19), (8, 10), (9, 11), (12, 14), (13, 15), (16,
    17), (18, 19)]

/-- The twelve faces. -/
def faces : List (List ℕ) := [[0, 8, 4, 14, 12], [0, 8, 10, 2, 16], [0, 12, 1, 17, 16], [1, 9, 5,
    14, 12], [1, 9, 11, 3, 17], [2, 10, 6, 15, 13], [2, 13, 3, 17, 16], [3, 11, 7, 15, 13], [4, 8,
    10, 6, 18], [4, 14, 5, 19, 18], [5, 9, 11, 7, 19], [6, 15, 7, 19, 18]]


/-- Start the certificate of a closed identity in `ℤ[φ]`. -/
local macro "gold_poly" : tactic =>
  `(tactic| (
    ipra_poly R ρ h [emb, dot3, cross3, phiPow, Gold.add_re, Gold.add_im, Gold.sub_re,
      Gold.sub_im, Gold.neg_re, Gold.neg_im, Gold.mul_re, Gold.mul_im, G3.sub_x, G3.sub_y,
      G3.sub_z, G3.neg_x, G3.neg_y, G3.neg_z, V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11,
      V12, V13, V14, V15, V16, V17, V18, V19, N0, N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11]
    ring))

/-! ## The circumscribed sphere: every vertex has squared radius `3` -/

/-- `|V0|² = 3`. -/
theorem radius_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V0 V0), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1|² = 3`. -/
theorem radius_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V1 V1), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2|² = 3`. -/
theorem radius_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V2 V2), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3|² = 3`. -/
theorem radius_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V3 V3), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4|² = 3`. -/
theorem radius_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V4 V4), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5|² = 3`. -/
theorem radius_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V5 V5), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6|² = 3`. -/
theorem radius_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V6 V6), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7|² = 3`. -/
theorem radius_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V7 V7), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8|² = 3`. -/
theorem radius_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V8 V8), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9|² = 3`. -/
theorem radius_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V9 V9), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10|² = 3`. -/
theorem radius_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V10 V10), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11|² = 3`. -/
theorem radius_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V11 V11), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12|² = 3`. -/
theorem radius_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V12 V12), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13|² = 3`. -/
theorem radius_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V13 V13), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14|² = 3`. -/
theorem radius_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V14 V14), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V15|² = 3`. -/
theorem radius_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V15 V15), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V16|² = 3`. -/
theorem radius_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V16 V16), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V17|² = 3`. -/
theorem radius_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V17 V17), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V18|² = 3`. -/
theorem radius_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V18 V18), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V19|² = 3`. -/
theorem radius_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 V19 V19), emb ⟨3, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-! ## The squared distances -/

/-- `|V0 − V1|² = 4 + 0φ`. -/
theorem dist_0_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V1) (V0 - V1)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V2|² = 4 + 0φ`. -/
theorem dist_0_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V2) (V0 - V2)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V3|² = 8 + 0φ`. -/
theorem dist_0_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V3) (V0 - V3)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V4|² = 4 + 0φ`. -/
theorem dist_0_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V4) (V0 - V4)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V5|² = 8 + 0φ`. -/
theorem dist_0_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V5) (V0 - V5)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V6|² = 8 + 0φ`. -/
theorem dist_0_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V6) (V0 - V6)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V7|² = 12 + 0φ`. -/
theorem dist_0_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V7) (V0 - V7)), emb ⟨12,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V8|² = 8 + -4φ` (an edge). -/
theorem dist_0_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V8) (V0 - V8)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V9|² = 8 + 0φ`. -/
theorem dist_0_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V9) (V0 - V9)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V10|² = 4 + 0φ`. -/
theorem dist_0_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V10) (V0 - V10)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V11|² = 4 + 4φ`. -/
theorem dist_0_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V11) (V0 - V11)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V12|² = 8 + -4φ` (an edge). -/
theorem dist_0_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V12) (V0 - V12)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V13|² = 8 + 0φ`. -/
theorem dist_0_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V13) (V0 - V13)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V14|² = 4 + 0φ`. -/
theorem dist_0_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V14) (V0 - V14)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V15|² = 4 + 4φ`. -/
theorem dist_0_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V15) (V0 - V15)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V16|² = 8 + -4φ` (an edge). -/
theorem dist_0_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V16) (V0 - V16)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V17|² = 4 + 0φ`. -/
theorem dist_0_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V17) (V0 - V17)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V18|² = 8 + 0φ`. -/
theorem dist_0_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V18) (V0 - V18)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V0 − V19|² = 4 + 4φ`. -/
theorem dist_0_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V0 - V19) (V0 - V19)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V2|² = 8 + 0φ`. -/
theorem dist_1_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V2) (V1 - V2)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V3|² = 4 + 0φ`. -/
theorem dist_1_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V3) (V1 - V3)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V4|² = 8 + 0φ`. -/
theorem dist_1_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V4) (V1 - V4)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V5|² = 4 + 0φ`. -/
theorem dist_1_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V5) (V1 - V5)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V6|² = 12 + 0φ`. -/
theorem dist_1_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V6) (V1 - V6)), emb ⟨12,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V7|² = 8 + 0φ`. -/
theorem dist_1_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V7) (V1 - V7)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V8|² = 8 + 0φ`. -/
theorem dist_1_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V8) (V1 - V8)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V9|² = 8 + -4φ` (an edge). -/
theorem dist_1_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V9) (V1 - V9)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V10|² = 4 + 4φ`. -/
theorem dist_1_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V10) (V1 - V10)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V11|² = 4 + 0φ`. -/
theorem dist_1_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V11) (V1 - V11)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V12|² = 8 + -4φ` (an edge). -/
theorem dist_1_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V12) (V1 - V12)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V13|² = 8 + 0φ`. -/
theorem dist_1_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V13) (V1 - V13)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V14|² = 4 + 0φ`. -/
theorem dist_1_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V14) (V1 - V14)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V15|² = 4 + 4φ`. -/
theorem dist_1_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V15) (V1 - V15)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V16|² = 4 + 0φ`. -/
theorem dist_1_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V16) (V1 - V16)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V17|² = 8 + -4φ` (an edge). -/
theorem dist_1_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V17) (V1 - V17)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V18|² = 4 + 4φ`. -/
theorem dist_1_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V18) (V1 - V18)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V1 − V19|² = 8 + 0φ`. -/
theorem dist_1_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V1 - V19) (V1 - V19)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V3|² = 4 + 0φ`. -/
theorem dist_2_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V3) (V2 - V3)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V4|² = 8 + 0φ`. -/
theorem dist_2_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V4) (V2 - V4)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V5|² = 12 + 0φ`. -/
theorem dist_2_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V5) (V2 - V5)), emb ⟨12,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V6|² = 4 + 0φ`. -/
theorem dist_2_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V6) (V2 - V6)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V7|² = 8 + 0φ`. -/
theorem dist_2_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V7) (V2 - V7)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V8|² = 4 + 0φ`. -/
theorem dist_2_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V8) (V2 - V8)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V9|² = 4 + 4φ`. -/
theorem dist_2_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V9) (V2 - V9)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V10|² = 8 + -4φ` (an edge). -/
theorem dist_2_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V10) (V2 - V10)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V11|² = 8 + 0φ`. -/
theorem dist_2_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V11) (V2 - V11)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V12|² = 8 + 0φ`. -/
theorem dist_2_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V12) (V2 - V12)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V13|² = 8 + -4φ` (an edge). -/
theorem dist_2_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V13) (V2 - V13)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V14|² = 4 + 4φ`. -/
theorem dist_2_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V14) (V2 - V14)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V15|² = 4 + 0φ`. -/
theorem dist_2_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V15) (V2 - V15)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V16|² = 8 + -4φ` (an edge). -/
theorem dist_2_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V16) (V2 - V16)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V17|² = 4 + 0φ`. -/
theorem dist_2_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V17) (V2 - V17)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V18|² = 8 + 0φ`. -/
theorem dist_2_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V18) (V2 - V18)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V2 − V19|² = 4 + 4φ`. -/
theorem dist_2_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V2 - V19) (V2 - V19)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V4|² = 12 + 0φ`. -/
theorem dist_3_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V4) (V3 - V4)), emb ⟨12,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V5|² = 8 + 0φ`. -/
theorem dist_3_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V5) (V3 - V5)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V6|² = 8 + 0φ`. -/
theorem dist_3_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V6) (V3 - V6)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V7|² = 4 + 0φ`. -/
theorem dist_3_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V7) (V3 - V7)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V8|² = 4 + 4φ`. -/
theorem dist_3_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V8) (V3 - V8)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V9|² = 4 + 0φ`. -/
theorem dist_3_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V9) (V3 - V9)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V10|² = 8 + 0φ`. -/
theorem dist_3_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V10) (V3 - V10)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V11|² = 8 + -4φ` (an edge). -/
theorem dist_3_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V11) (V3 - V11)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V12|² = 8 + 0φ`. -/
theorem dist_3_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V12) (V3 - V12)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V13|² = 8 + -4φ` (an edge). -/
theorem dist_3_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V13) (V3 - V13)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V14|² = 4 + 4φ`. -/
theorem dist_3_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V14) (V3 - V14)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V15|² = 4 + 0φ`. -/
theorem dist_3_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V15) (V3 - V15)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V16|² = 4 + 0φ`. -/
theorem dist_3_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V16) (V3 - V16)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V17|² = 8 + -4φ` (an edge). -/
theorem dist_3_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V17) (V3 - V17)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V18|² = 4 + 4φ`. -/
theorem dist_3_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V18) (V3 - V18)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V3 − V19|² = 8 + 0φ`. -/
theorem dist_3_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V3 - V19) (V3 - V19)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V5|² = 4 + 0φ`. -/
theorem dist_4_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V5) (V4 - V5)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V6|² = 4 + 0φ`. -/
theorem dist_4_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V6) (V4 - V6)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V7|² = 8 + 0φ`. -/
theorem dist_4_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V7) (V4 - V7)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V8|² = 8 + -4φ` (an edge). -/
theorem dist_4_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V8) (V4 - V8)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V9|² = 8 + 0φ`. -/
theorem dist_4_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V9) (V4 - V9)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V10|² = 4 + 0φ`. -/
theorem dist_4_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V10) (V4 - V10)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V11|² = 4 + 4φ`. -/
theorem dist_4_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V11) (V4 - V11)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V12|² = 4 + 0φ`. -/
theorem dist_4_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V12) (V4 - V12)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V13|² = 4 + 4φ`. -/
theorem dist_4_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V13) (V4 - V13)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V14|² = 8 + -4φ` (an edge). -/
theorem dist_4_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V14) (V4 - V14)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V15|² = 8 + 0φ`. -/
theorem dist_4_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V15) (V4 - V15)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V16|² = 8 + 0φ`. -/
theorem dist_4_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V16) (V4 - V16)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V17|² = 4 + 4φ`. -/
theorem dist_4_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V17) (V4 - V17)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V18|² = 8 + -4φ` (an edge). -/
theorem dist_4_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V18) (V4 - V18)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V4 − V19|² = 4 + 0φ`. -/
theorem dist_4_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V4 - V19) (V4 - V19)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V6|² = 8 + 0φ`. -/
theorem dist_5_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V6) (V5 - V6)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V7|² = 4 + 0φ`. -/
theorem dist_5_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V7) (V5 - V7)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V8|² = 8 + 0φ`. -/
theorem dist_5_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V8) (V5 - V8)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V9|² = 8 + -4φ` (an edge). -/
theorem dist_5_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V9) (V5 - V9)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V10|² = 4 + 4φ`. -/
theorem dist_5_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V10) (V5 - V10)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V11|² = 4 + 0φ`. -/
theorem dist_5_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V11) (V5 - V11)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V12|² = 4 + 0φ`. -/
theorem dist_5_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V12) (V5 - V12)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V13|² = 4 + 4φ`. -/
theorem dist_5_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V13) (V5 - V13)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V14|² = 8 + -4φ` (an edge). -/
theorem dist_5_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V14) (V5 - V14)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V15|² = 8 + 0φ`. -/
theorem dist_5_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V15) (V5 - V15)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V16|² = 4 + 4φ`. -/
theorem dist_5_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V16) (V5 - V16)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V17|² = 8 + 0φ`. -/
theorem dist_5_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V17) (V5 - V17)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V18|² = 4 + 0φ`. -/
theorem dist_5_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V18) (V5 - V18)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V5 − V19|² = 8 + -4φ` (an edge). -/
theorem dist_5_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V5 - V19) (V5 - V19)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V7|² = 4 + 0φ`. -/
theorem dist_6_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V7) (V6 - V7)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V8|² = 4 + 0φ`. -/
theorem dist_6_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V8) (V6 - V8)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V9|² = 4 + 4φ`. -/
theorem dist_6_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V9) (V6 - V9)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V10|² = 8 + -4φ` (an edge). -/
theorem dist_6_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V10) (V6 - V10)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V11|² = 8 + 0φ`. -/
theorem dist_6_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V11) (V6 - V11)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V12|² = 4 + 4φ`. -/
theorem dist_6_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V12) (V6 - V12)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V13|² = 4 + 0φ`. -/
theorem dist_6_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V13) (V6 - V13)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V14|² = 8 + 0φ`. -/
theorem dist_6_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V14) (V6 - V14)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V15|² = 8 + -4φ` (an edge). -/
theorem dist_6_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V15) (V6 - V15)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V16|² = 8 + 0φ`. -/
theorem dist_6_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V16) (V6 - V16)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V17|² = 4 + 4φ`. -/
theorem dist_6_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V17) (V6 - V17)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V18|² = 8 + -4φ` (an edge). -/
theorem dist_6_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V18) (V6 - V18)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V6 − V19|² = 4 + 0φ`. -/
theorem dist_6_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V6 - V19) (V6 - V19)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V8|² = 4 + 4φ`. -/
theorem dist_7_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V8) (V7 - V8)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V9|² = 4 + 0φ`. -/
theorem dist_7_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V9) (V7 - V9)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V10|² = 8 + 0φ`. -/
theorem dist_7_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V10) (V7 - V10)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V11|² = 8 + -4φ` (an edge). -/
theorem dist_7_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V11) (V7 - V11)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V12|² = 4 + 4φ`. -/
theorem dist_7_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V12) (V7 - V12)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V13|² = 4 + 0φ`. -/
theorem dist_7_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V13) (V7 - V13)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V14|² = 8 + 0φ`. -/
theorem dist_7_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V14) (V7 - V14)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V15|² = 8 + -4φ` (an edge). -/
theorem dist_7_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V15) (V7 - V15)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V16|² = 4 + 4φ`. -/
theorem dist_7_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V16) (V7 - V16)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V17|² = 8 + 0φ`. -/
theorem dist_7_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V17) (V7 - V17)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V18|² = 4 + 0φ`. -/
theorem dist_7_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V18) (V7 - V18)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V7 − V19|² = 8 + -4φ` (an edge). -/
theorem dist_7_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V7 - V19) (V7 - V19)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V9|² = 4 + 4φ`. -/
theorem dist_8_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V9) (V8 - V9)), emb ⟨4,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V10|² = 8 + -4φ` (an edge). -/
theorem dist_8_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V10) (V8 - V10)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V11|² = 12 + 0φ`. -/
theorem dist_8_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V11) (V8 - V11)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V12|² = 4 + 0φ`. -/
theorem dist_8_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V12) (V8 - V12)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V13|² = 8 + 0φ`. -/
theorem dist_8_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V13) (V8 - V13)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V14|² = 4 + 0φ`. -/
theorem dist_8_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V14) (V8 - V14)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V15|² = 8 + 0φ`. -/
theorem dist_8_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V15) (V8 - V15)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V16|² = 4 + 0φ`. -/
theorem dist_8_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V16) (V8 - V16)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V17|² = 8 + 0φ`. -/
theorem dist_8_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V17) (V8 - V17)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V18|² = 4 + 0φ`. -/
theorem dist_8_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V18) (V8 - V18)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V8 − V19|² = 8 + 0φ`. -/
theorem dist_8_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V8 - V19) (V8 - V19)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V10|² = 12 + 0φ`. -/
theorem dist_9_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V10) (V9 - V10)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V11|² = 8 + -4φ` (an edge). -/
theorem dist_9_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V11) (V9 - V11)), emb ⟨8,
        (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V12|² = 4 + 0φ`. -/
theorem dist_9_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V12) (V9 - V12)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V13|² = 8 + 0φ`. -/
theorem dist_9_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V13) (V9 - V13)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V14|² = 4 + 0φ`. -/
theorem dist_9_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V14) (V9 - V14)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V15|² = 8 + 0φ`. -/
theorem dist_9_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V15) (V9 - V15)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V16|² = 8 + 0φ`. -/
theorem dist_9_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V16) (V9 - V16)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V17|² = 4 + 0φ`. -/
theorem dist_9_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V17) (V9 - V17)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V18|² = 8 + 0φ`. -/
theorem dist_9_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V18) (V9 - V18)), emb ⟨8,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V9 − V19|² = 4 + 0φ`. -/
theorem dist_9_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V9 - V19) (V9 - V19)), emb ⟨4,
        0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V11|² = 4 + 4φ`. -/
theorem dist_10_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V11) (V10 - V11)), emb
        ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V12|² = 8 + 0φ`. -/
theorem dist_10_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V12) (V10 - V12)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V13|² = 4 + 0φ`. -/
theorem dist_10_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V13) (V10 - V13)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V14|² = 8 + 0φ`. -/
theorem dist_10_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V14) (V10 - V14)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V15|² = 4 + 0φ`. -/
theorem dist_10_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V15) (V10 - V15)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V16|² = 4 + 0φ`. -/
theorem dist_10_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V16) (V10 - V16)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V17|² = 8 + 0φ`. -/
theorem dist_10_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V17) (V10 - V17)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V18|² = 4 + 0φ`. -/
theorem dist_10_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V18) (V10 - V18)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V10 − V19|² = 8 + 0φ`. -/
theorem dist_10_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V10 - V19) (V10 - V19)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V12|² = 8 + 0φ`. -/
theorem dist_11_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V12) (V11 - V12)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V13|² = 4 + 0φ`. -/
theorem dist_11_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V13) (V11 - V13)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V14|² = 8 + 0φ`. -/
theorem dist_11_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V14) (V11 - V14)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V15|² = 4 + 0φ`. -/
theorem dist_11_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V15) (V11 - V15)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V16|² = 8 + 0φ`. -/
theorem dist_11_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V16) (V11 - V16)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V17|² = 4 + 0φ`. -/
theorem dist_11_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V17) (V11 - V17)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V18|² = 8 + 0φ`. -/
theorem dist_11_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V18) (V11 - V18)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V11 − V19|² = 4 + 0φ`. -/
theorem dist_11_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V11 - V19) (V11 - V19)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V13|² = 4 + 4φ`. -/
theorem dist_12_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V13) (V12 - V13)), emb
        ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V14|² = 8 + -4φ` (an edge). -/
theorem dist_12_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V14) (V12 - V14)), emb
        ⟨8, (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V15|² = 12 + 0φ`. -/
theorem dist_12_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V15) (V12 - V15)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V16|² = 4 + 0φ`. -/
theorem dist_12_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V16) (V12 - V16)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V17|² = 4 + 0φ`. -/
theorem dist_12_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V17) (V12 - V17)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V18|² = 8 + 0φ`. -/
theorem dist_12_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V18) (V12 - V18)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V12 − V19|² = 8 + 0φ`. -/
theorem dist_12_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V12 - V19) (V12 - V19)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V14|² = 12 + 0φ`. -/
theorem dist_13_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V14) (V13 - V14)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V15|² = 8 + -4φ` (an edge). -/
theorem dist_13_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V15) (V13 - V15)), emb
        ⟨8, (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V16|² = 4 + 0φ`. -/
theorem dist_13_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V16) (V13 - V16)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V17|² = 4 + 0φ`. -/
theorem dist_13_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V17) (V13 - V17)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V18|² = 8 + 0φ`. -/
theorem dist_13_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V18) (V13 - V18)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V13 − V19|² = 8 + 0φ`. -/
theorem dist_13_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V13 - V19) (V13 - V19)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14 − V15|² = 4 + 4φ`. -/
theorem dist_14_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V14 - V15) (V14 - V15)), emb
        ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14 − V16|² = 8 + 0φ`. -/
theorem dist_14_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V14 - V16) (V14 - V16)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14 − V17|² = 8 + 0φ`. -/
theorem dist_14_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V14 - V17) (V14 - V17)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14 − V18|² = 4 + 0φ`. -/
theorem dist_14_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V14 - V18) (V14 - V18)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V14 − V19|² = 4 + 0φ`. -/
theorem dist_14_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V14 - V19) (V14 - V19)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V15 − V16|² = 8 + 0φ`. -/
theorem dist_15_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V15 - V16) (V15 - V16)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V15 − V17|² = 8 + 0φ`. -/
theorem dist_15_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V15 - V17) (V15 - V17)), emb
        ⟨8, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V15 − V18|² = 4 + 0φ`. -/
theorem dist_15_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V15 - V18) (V15 - V18)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V15 − V19|² = 4 + 0φ`. -/
theorem dist_15_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V15 - V19) (V15 - V19)), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V16 − V17|² = 8 + -4φ` (an edge). -/
theorem dist_16_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V16 - V17) (V16 - V17)), emb
        ⟨8, (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V16 − V18|² = 4 + 4φ`. -/
theorem dist_16_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V16 - V18) (V16 - V18)), emb
        ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V16 − V19|² = 12 + 0φ`. -/
theorem dist_16_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V16 - V19) (V16 - V19)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V17 − V18|² = 12 + 0φ`. -/
theorem dist_17_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V17 - V18) (V17 - V18)), emb
        ⟨12, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V17 − V19|² = 4 + 4φ`. -/
theorem dist_17_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V17 - V19) (V17 - V19)), emb
        ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `|V18 − V19|² = 8 + -4φ` (an edge). -/
theorem dist_18_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 (V18 - V19) (V18 - V19)), emb
        ⟨8, (-4)⟩)) :=
  derive_imp _ _ (by gold_poly)

/-! ## The edge square is the least nonzero squared distance -/

/-- `(4 + 0φ) − (8 − 4φ)` times `φ^1` is `4 + 0φ`, with nonnegative coefficients: since `φ > 0`,
the squared distance `4 + 0φ` exceeds the edge square. -/
theorem least_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (((⟨4, 0⟩ : Gold) - (⟨8, (-4)⟩ :
        Gold)) * phiPow 1), emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `(8 + 0φ) − (8 − 4φ)` times `φ^0` is `0 + 4φ`, with nonnegative coefficients: since `φ > 0`,
the squared distance `8 + 0φ` exceeds the edge square. -/
theorem least_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (((⟨8, 0⟩ : Gold) - (⟨8, (-4)⟩ :
        Gold)) * phiPow 0), emb ⟨0, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `(4 + 4φ) − (8 − 4φ)` times `φ^1` is `8 + 4φ`, with nonnegative coefficients: since `φ > 0`,
the squared distance `4 + 4φ` exceeds the edge square. -/
theorem least_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (((⟨4, 4⟩ : Gold) - (⟨8, (-4)⟩ :
        Gold)) * phiPow 1), emb ⟨8, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `(12 + 0φ) − (8 − 4φ)` times `φ^0` is `4 + 4φ`, with nonnegative coefficients: since `φ > 0`,
the squared distance `12 + 0φ` exceeds the edge square. -/
theorem least_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (((⟨12, 0⟩ : Gold) - (⟨8, (-4)⟩ :
        Gold)) * phiPow 0), emb ⟨4, 4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-! ## The twelve faces -/

/-- `V14` lies in the plane of face 0. -/
theorem plane_0_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N0 (V14 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies in the plane of face 0. -/
theorem plane_0_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N0 (V12 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 0 is nonzero: `|N0|² φ^4 = 8 + 4φ`. -/
theorem normal_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N0 N0 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 0: `−N0 · (V1 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_0_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V1 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 0: `−N0 · (V2 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_0_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V2 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 0: `−N0 · (V3 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_0_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V3 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 0: `−N0 · (V5 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_0_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V5 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 0: `−N0 · (V6 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_0_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V6 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 0: `−N0 · (V7 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_0_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V7 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 0: `−N0 · (V9 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_0_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V9 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 0: `−N0 · (V10 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_0_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V10 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 0: `−N0 · (V11 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_0_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V11 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 0: `−N0 · (V13 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_0_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V13 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 0: `−N0 · (V15 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_0_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V15 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 0: `−N0 · (V16 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_0_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V16 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 0: `−N0 · (V17 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_0_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V17 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 0: `−N0 · (V18 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_0_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V18 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 0: `−N0 · (V19 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_0_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N0 (V19 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies in the plane of face 1. -/
theorem plane_1_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N1 (V2 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies in the plane of face 1. -/
theorem plane_1_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N1 (V16 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 1 is nonzero: `|N1|² φ^4 = 8 + 4φ`. -/
theorem normal_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N1 N1 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 1: `−N1 · (V1 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_1_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V1 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 1: `−N1 · (V3 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_1_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V3 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 1: `−N1 · (V4 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_1_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V4 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 1: `−N1 · (V5 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_1_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V5 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 1: `−N1 · (V6 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_1_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V6 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 1: `−N1 · (V7 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_1_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V7 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 1: `−N1 · (V9 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_1_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V9 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 1: `−N1 · (V11 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_1_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V11 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 1: `−N1 · (V12 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_1_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V12 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 1: `−N1 · (V13 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_1_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V13 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 1: `−N1 · (V14 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_1_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V14 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 1: `−N1 · (V15 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_1_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V15 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 1: `−N1 · (V17 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_1_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V17 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 1: `−N1 · (V18 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_1_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V18 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 1: `−N1 · (V19 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_1_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N1 (V19 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies in the plane of face 2. -/
theorem plane_2_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N2 (V17 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies in the plane of face 2. -/
theorem plane_2_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N2 (V16 - V0)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 2 is nonzero: `|N2|² φ^4 = 8 + 4φ`. -/
theorem normal_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N2 N2 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 2: `−N2 · (V2 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_2_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V2 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 2: `−N2 · (V3 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_2_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V3 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 2: `−N2 · (V4 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_2_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V4 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 2: `−N2 · (V5 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_2_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V5 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 2: `−N2 · (V6 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_2_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V6 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 2: `−N2 · (V7 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_2_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V7 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 2: `−N2 · (V8 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_2_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V8 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 2: `−N2 · (V9 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_2_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V9 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 2: `−N2 · (V10 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_2_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V10 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 2: `−N2 · (V11 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_2_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V11 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 2: `−N2 · (V13 − V0)` times `φ^1` is `4 + 0φ`. -/
theorem side_2_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V13 - V0) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 2: `−N2 · (V14 − V0)` times `φ^2` is `4 + 0φ`. -/
theorem side_2_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V14 - V0) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 2: `−N2 · (V15 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_2_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V15 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 2: `−N2 · (V18 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_2_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V18 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 2: `−N2 · (V19 − V0)` times `φ^0` is `4 + 0φ`. -/
theorem side_2_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N2 (V19 - V0) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies in the plane of face 3. -/
theorem plane_3_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N3 (V14 - V1)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies in the plane of face 3. -/
theorem plane_3_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N3 (V12 - V1)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 3 is nonzero: `|N3|² φ^4 = 8 + 4φ`. -/
theorem normal_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N3 N3 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 3: `−N3 · (V0 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_3_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V0 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 3: `−N3 · (V2 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_3_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V2 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 3: `−N3 · (V3 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_3_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V3 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 3: `−N3 · (V4 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_3_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V4 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 3: `−N3 · (V6 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_3_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V6 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 3: `−N3 · (V7 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_3_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V7 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 3: `−N3 · (V8 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_3_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V8 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 3: `−N3 · (V10 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_3_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V10 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 3: `−N3 · (V11 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_3_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V11 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 3: `−N3 · (V13 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_3_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V13 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 3: `−N3 · (V15 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_3_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V15 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 3: `−N3 · (V16 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_3_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V16 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 3: `−N3 · (V17 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_3_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V17 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 3: `−N3 · (V18 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_3_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V18 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 3: `−N3 · (V19 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_3_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N3 (V19 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies in the plane of face 4. -/
theorem plane_4_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N4 (V3 - V1)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies in the plane of face 4. -/
theorem plane_4_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N4 (V17 - V1)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 4 is nonzero: `|N4|² φ^4 = 8 + 4φ`. -/
theorem normal_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N4 N4 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 4: `−N4 · (V0 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_4_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V0 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 4: `−N4 · (V2 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_4_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V2 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 4: `−N4 · (V4 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_4_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V4 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 4: `−N4 · (V5 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_4_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V5 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 4: `−N4 · (V6 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_4_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V6 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 4: `−N4 · (V7 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_4_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V7 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 4: `−N4 · (V8 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_4_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V8 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 4: `−N4 · (V10 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_4_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V10 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 4: `−N4 · (V12 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_4_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V12 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 4: `−N4 · (V13 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_4_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V13 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 4: `−N4 · (V14 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_4_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V14 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 4: `−N4 · (V15 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_4_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V15 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 4: `−N4 · (V16 − V1)` times `φ^2` is `4 + 0φ`. -/
theorem side_4_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V16 - V1) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 4: `−N4 · (V18 − V1)` times `φ^0` is `4 + 0φ`. -/
theorem side_4_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V18 - V1) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 4: `−N4 · (V19 − V1)` times `φ^1` is `4 + 0φ`. -/
theorem side_4_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N4 (V19 - V1) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies in the plane of face 5. -/
theorem plane_5_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N5 (V15 - V2)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies in the plane of face 5. -/
theorem plane_5_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N5 (V13 - V2)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 5 is nonzero: `|N5|² φ^4 = 8 + 4φ`. -/
theorem normal_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N5 N5 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 5: `−N5 · (V0 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_5_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V0 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 5: `−N5 · (V1 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_5_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V1 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 5: `−N5 · (V3 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_5_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V3 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 5: `−N5 · (V4 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_5_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V4 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 5: `−N5 · (V5 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_5_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V5 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 5: `−N5 · (V7 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_5_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V7 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 5: `−N5 · (V8 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_5_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V8 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 5: `−N5 · (V9 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_5_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V9 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 5: `−N5 · (V11 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_5_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V11 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 5: `−N5 · (V12 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_5_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V12 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 5: `−N5 · (V14 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_5_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V14 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 5: `−N5 · (V16 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_5_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V16 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 5: `−N5 · (V17 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_5_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V17 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 5: `−N5 · (V18 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_5_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V18 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 5: `−N5 · (V19 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_5_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N5 (V19 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies in the plane of face 6. -/
theorem plane_6_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N6 (V17 - V2)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies in the plane of face 6. -/
theorem plane_6_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N6 (V16 - V2)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 6 is nonzero: `|N6|² φ^4 = 8 + 4φ`. -/
theorem normal_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N6 N6 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 6: `−N6 · (V0 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_6_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V0 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 6: `−N6 · (V1 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_6_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V1 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 6: `−N6 · (V4 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_6_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V4 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 6: `−N6 · (V5 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_6_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V5 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 6: `−N6 · (V6 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_6_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V6 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 6: `−N6 · (V7 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_6_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V7 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 6: `−N6 · (V8 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_6_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V8 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 6: `−N6 · (V9 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_6_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V9 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 6: `−N6 · (V10 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_6_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V10 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 6: `−N6 · (V11 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_6_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V11 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 6: `−N6 · (V12 − V2)` times `φ^1` is `4 + 0φ`. -/
theorem side_6_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V12 - V2) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 6: `−N6 · (V14 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_6_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V14 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 6: `−N6 · (V15 − V2)` times `φ^2` is `4 + 0φ`. -/
theorem side_6_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V15 - V2) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 6: `−N6 · (V18 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_6_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V18 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 6: `−N6 · (V19 − V2)` times `φ^0` is `4 + 0φ`. -/
theorem side_6_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N6 (V19 - V2) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies in the plane of face 7. -/
theorem plane_7_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N7 (V15 - V3)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies in the plane of face 7. -/
theorem plane_7_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N7 (V13 - V3)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 7 is nonzero: `|N7|² φ^4 = 8 + 4φ`. -/
theorem normal_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N7 N7 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 7: `−N7 · (V0 − V3)` times `φ^0` is `4 + 0φ`. -/
theorem side_7_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V0 - V3) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 7: `−N7 · (V1 − V3)` times `φ^1` is `4 + 0φ`. -/
theorem side_7_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V1 - V3) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 7: `−N7 · (V2 − V3)` times `φ^2` is `4 + 0φ`. -/
theorem side_7_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V2 - V3) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 7: `−N7 · (V4 − V3)` times `φ^0` is `4 + 0φ`. -/
theorem side_7_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V4 - V3) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 7: `−N7 · (V5 − V3)` times `φ^1` is `4 + 0φ`. -/
theorem side_7_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V5 - V3) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 7: `−N7 · (V6 − V3)` times `φ^2` is `4 + 0φ`. -/
theorem side_7_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V6 - V3) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 7: `−N7 · (V8 − V3)` times `φ^0` is `4 + 0φ`. -/
theorem side_7_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V8 - V3) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 7: `−N7 · (V9 − V3)` times `φ^2` is `4 + 0φ`. -/
theorem side_7_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V9 - V3) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 7: `−N7 · (V10 − V3)` times `φ^1` is `4 + 0φ`. -/
theorem side_7_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V10 - V3) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 7: `−N7 · (V12 − V3)` times `φ^0` is `4 + 0φ`. -/
theorem side_7_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V12 - V3) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 7: `−N7 · (V14 − V3)` times `φ^0` is `4 + 0φ`. -/
theorem side_7_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V14 - V3) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 7: `−N7 · (V16 − V3)` times `φ^1` is `4 + 0φ`. -/
theorem side_7_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V16 - V3) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 7: `−N7 · (V17 − V3)` times `φ^2` is `4 + 0φ`. -/
theorem side_7_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V17 - V3) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 7: `−N7 · (V18 − V3)` times `φ^1` is `4 + 0φ`. -/
theorem side_7_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V18 - V3) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 7: `−N7 · (V19 − V3)` times `φ^2` is `4 + 0φ`. -/
theorem side_7_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N7 (V19 - V3) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies in the plane of face 8. -/
theorem plane_8_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N8 (V6 - V4)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies in the plane of face 8. -/
theorem plane_8_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N8 (V18 - V4)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 8 is nonzero: `|N8|² φ^4 = 8 + 4φ`. -/
theorem normal_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N8 N8 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 8: `−N8 · (V0 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_8_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V0 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 8: `−N8 · (V1 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_8_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V1 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 8: `−N8 · (V2 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_8_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V2 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 8: `−N8 · (V3 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_8_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V3 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 8: `−N8 · (V5 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_8_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V5 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 8: `−N8 · (V7 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_8_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V7 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 8: `−N8 · (V9 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_8_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V9 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 8: `−N8 · (V11 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_8_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V11 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 8: `−N8 · (V12 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_8_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V12 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 8: `−N8 · (V13 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_8_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V13 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 8: `−N8 · (V14 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_8_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V14 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 8: `−N8 · (V15 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_8_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V15 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 8: `−N8 · (V16 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_8_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V16 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 8: `−N8 · (V17 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_8_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V17 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies strictly below the plane of face 8: `−N8 · (V19 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_8_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N8 (V19 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies in the plane of face 9. -/
theorem plane_9_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N9 (V19 - V4)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies in the plane of face 9. -/
theorem plane_9_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N9 (V18 - V4)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 9 is nonzero: `|N9|² φ^4 = 8 + 4φ`. -/
theorem normal_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N9 N9 * phiPow 4), emb ⟨8, 4⟩))
        :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 9: `−N9 · (V0 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_9_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V0 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 9: `−N9 · (V1 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_9_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V1 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 9: `−N9 · (V2 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_9_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V2 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 9: `−N9 · (V3 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_9_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V3 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 9: `−N9 · (V6 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_9_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V6 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies strictly below the plane of face 9: `−N9 · (V7 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_9_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V7 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 9: `−N9 · (V8 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_9_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V8 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 9: `−N9 · (V9 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_9_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V9 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 9: `−N9 · (V10 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_9_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V10 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 9: `−N9 · (V11 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_9_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V11 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 9: `−N9 · (V12 − V4)` times `φ^2` is `4 + 0φ`. -/
theorem side_9_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V12 - V4) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 9: `−N9 · (V13 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_9_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V13 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 9: `−N9 · (V15 − V4)` times `φ^1` is `4 + 0φ`. -/
theorem side_9_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V15 - V4) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 9: `−N9 · (V16 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_9_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V16 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 9: `−N9 · (V17 − V4)` times `φ^0` is `4 + 0φ`. -/
theorem side_9_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N9 (V17 - V4) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V7` lies in the plane of face 10. -/
theorem plane_10_7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N10 (V7 - V5)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies in the plane of face 10. -/
theorem plane_10_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N10 (V19 - V5)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 10 is nonzero: `|N10|² φ^4 = 8 + 4φ`. -/
theorem normal_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N10 N10 * phiPow 4), emb ⟨8,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 10: `−N10 · (V0 − V5)` times `φ^0` is `4 + 0φ`. -/
theorem side_10_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V0 - V5) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 10: `−N10 · (V1 − V5)` times `φ^2` is `4 + 0φ`. -/
theorem side_10_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V1 - V5) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 10: `−N10 · (V2 − V5)` times `φ^0` is `4 + 0φ`. -/
theorem side_10_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V2 - V5) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 10: `−N10 · (V3 − V5)` times `φ^2` is `4 + 0φ`. -/
theorem side_10_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V3 - V5) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 10: `−N10 · (V4 − V5)` times `φ^1` is `4 + 0φ`. -/
theorem side_10_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V4 - V5) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V6` lies strictly below the plane of face 10: `−N10 · (V6 − V5)` times `φ^1` is `4 + 0φ`. -/
theorem side_10_6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V6 - V5) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 10: `−N10 · (V8 − V5)` times `φ^0` is `4 + 0φ`. -/
theorem side_10_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V8 - V5) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 10: `−N10 · (V10 − V5)` times `φ^0` is `4 + 0φ`. -/
theorem side_10_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V10 - V5) * phiPow 0),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 10: `−N10 · (V12 − V5)` times `φ^1` is `4 + 0φ`. -/
theorem side_10_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V12 - V5) * phiPow 1),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 10: `−N10 · (V13 − V5)` times `φ^1` is `4 + 0φ`. -/
theorem side_10_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V13 - V5) * phiPow 1),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 10: `−N10 · (V14 − V5)` times `φ^2` is `4 + 0φ`. -/
theorem side_10_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V14 - V5) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V15` lies strictly below the plane of face 10: `−N10 · (V15 − V5)` times `φ^2` is `4 + 0φ`. -/
theorem side_10_15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V15 - V5) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 10: `−N10 · (V16 − V5)` times `φ^0` is `4 + 0φ`. -/
theorem side_10_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V16 - V5) * phiPow 0),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 10: `−N10 · (V17 − V5)` times `φ^1` is `4 + 0φ`. -/
theorem side_10_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V17 - V5) * phiPow 1),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies strictly below the plane of face 10: `−N10 · (V18 − V5)` times `φ^2` is `4 + 0φ`. -/
theorem side_10_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N10 (V18 - V5) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V19` lies in the plane of face 11. -/
theorem plane_11_19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N11 (V19 - V6)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V18` lies in the plane of face 11. -/
theorem plane_11_18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N11 (V18 - V6)), emb ⟨0, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- The normal of face 11 is nonzero: `|N11|² φ^4 = 8 + 4φ`. -/
theorem normal_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (dot3 N11 N11 * phiPow 4), emb ⟨8,
        4⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V0` lies strictly below the plane of face 11: `−N11 · (V0 − V6)` times `φ^0` is `4 + 0φ`. -/
theorem side_11_0 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V0 - V6) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V1` lies strictly below the plane of face 11: `−N11 · (V1 − V6)` times `φ^0` is `4 + 0φ`. -/
theorem side_11_1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V1 - V6) * phiPow 0), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V2` lies strictly below the plane of face 11: `−N11 · (V2 − V6)` times `φ^1` is `4 + 0φ`. -/
theorem side_11_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V2 - V6) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V3` lies strictly below the plane of face 11: `−N11 · (V3 − V6)` times `φ^1` is `4 + 0φ`. -/
theorem side_11_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V3 - V6) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V4` lies strictly below the plane of face 11: `−N11 · (V4 − V6)` times `φ^2` is `4 + 0φ`. -/
theorem side_11_4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V4 - V6) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V5` lies strictly below the plane of face 11: `−N11 · (V5 − V6)` times `φ^2` is `4 + 0φ`. -/
theorem side_11_5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V5 - V6) * phiPow 2), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V8` lies strictly below the plane of face 11: `−N11 · (V8 − V6)` times `φ^1` is `4 + 0φ`. -/
theorem side_11_8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V8 - V6) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V9` lies strictly below the plane of face 11: `−N11 · (V9 − V6)` times `φ^1` is `4 + 0φ`. -/
theorem side_11_9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V9 - V6) * phiPow 1), emb
        ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V10` lies strictly below the plane of face 11: `−N11 · (V10 − V6)` times `φ^2` is `4 + 0φ`. -/
theorem side_11_10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V10 - V6) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V11` lies strictly below the plane of face 11: `−N11 · (V11 − V6)` times `φ^2` is `4 + 0φ`. -/
theorem side_11_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V11 - V6) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V12` lies strictly below the plane of face 11: `−N11 · (V12 − V6)` times `φ^0` is `4 + 0φ`. -/
theorem side_11_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V12 - V6) * phiPow 0),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V13` lies strictly below the plane of face 11: `−N11 · (V13 − V6)` times `φ^2` is `4 + 0φ`. -/
theorem side_11_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V13 - V6) * phiPow 2),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V14` lies strictly below the plane of face 11: `−N11 · (V14 − V6)` times `φ^1` is `4 + 0φ`. -/
theorem side_11_14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V14 - V6) * phiPow 1),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V16` lies strictly below the plane of face 11: `−N11 · (V16 − V6)` times `φ^0` is `4 + 0φ`. -/
theorem side_11_16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V16 - V6) * phiPow 0),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

/-- `V17` lies strictly below the plane of face 11: `−N11 · (V17 − V6)` times `φ^0` is `4 + 0φ`. -/
theorem side_11_17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1) (imp [] (emb (-dot3 N11 (V17 - V6) * phiPow 0),
        emb ⟨4, 0⟩)) :=
  derive_imp _ _ (by gold_poly)

end LeanProofs.IPRA.Geometry.Dodecahedron
