import IPRADerivations.Geometry.SphericalCore

/-!
# Polar duality and the tetrahedron laws (`spherical_trigonometry_ipra_2026-11-15`)

Vector identities over the integers behind Sections 5 and 11 of the packet:

* `polar_cross` (`thm:polar-correspondence`, involution): `(v × w) × (w × u) = [u v w] w`, so the
  polar of the polar triangle is the original one up to the positive factor `τ`;
* `polar_side` ((5.2), `a* = π − A`): `(w × u)·(u × v) = (w·u)(u·v) − (u·u)(v·w)`, which for unit
  vectors is `yz − x = −s_b s_c cos A`;
* `polar_triple`: `[v × w, w × u, u × v] = [u v w]²`, the triple product of the polar triangle;
* `face_closure` (`lem:face-closure`): `(b − a) × (c − a) = b × c + c × a + a × b`, i.e. the four
  outward face-area vectors of a tetrahedron sum to zero;
* `tetra_cosine` (`thm:tetra-cosine`): `|N|² = |N₂|² + |N₃|² + |N₄|² + 2(N₂·N₃ + N₂·N₄ + N₃·N₄)` for
  `N = (b − a) × (c − a)` and `N₂ = b × c`, `N₃ = c × a`, `N₄ = a × b`; with
  `N_j·N_k = −Δ_j Δ_k cos θ` for outward normals this is the tetrahedral cosine law.
-/

namespace LeanProofs.IPRA.Geometry.SphericalPolar

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R]

theorem cross_cross_ring (u v w : Fin 3 → R) :
    (v ⨯₃ w) ⨯₃ (w ⨯₃ u) = (u ⬝ᵥ (v ⨯₃ w)) • w := by
  ext i; fin_cases i <;> simp [crossProduct, dotProduct, Fin.sum_univ_three] <;> ring

theorem polar_side_ring (u v w : Fin 3 → R) :
    (w ⨯₃ u) ⬝ᵥ (u ⨯₃ v) = (w ⬝ᵥ u) * (u ⬝ᵥ v) - (u ⬝ᵥ u) * (v ⬝ᵥ w) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem polar_triple_ring (u v w : Fin 3 → R) :
    (v ⨯₃ w) ⬝ᵥ ((w ⨯₃ u) ⨯₃ (u ⨯₃ v)) = (u ⬝ᵥ (v ⨯₃ w)) ^ 2 := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem face_closure_ring (a b c : Fin 3 → R) :
    (b - a) ⨯₃ (c - a) = b ⨯₃ c + c ⨯₃ a + a ⨯₃ b := by
  ext i; fin_cases i <;> simp [crossProduct] <;> ring

theorem tetra_cosine_ring (a b c : Fin 3 → R) :
    ((b - a) ⨯₃ (c - a)) ⬝ᵥ ((b - a) ⨯₃ (c - a)) =
      (b ⨯₃ c) ⬝ᵥ (b ⨯₃ c) + (c ⨯₃ a) ⬝ᵥ (c ⨯₃ a) + (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) +
        2 * ((b ⨯₃ c) ⬝ᵥ (c ⨯₃ a) + (b ⨯₃ c) ⬝ᵥ (a ⨯₃ b) + (c ⨯₃ a) ⬝ᵥ (a ⨯₃ b)) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem tetra_linear0_ring (a b c : Fin 3 → R) :
    ((b - a) ⨯₃ (c - a)) ⬝ᵥ ((b - a) ⨯₃ (c - a)) =
      ((b - a) ⨯₃ (c - a)) ⬝ᵥ (b ⨯₃ c) + ((b - a) ⨯₃ (c - a)) ⬝ᵥ (c ⨯₃ a) + ((b - a) ⨯₃ (c - a)) ⬝ᵥ (a ⨯₃ b) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem tetra_linear1_ring (a b c : Fin 3 → R) :
    (b ⨯₃ c) ⬝ᵥ (b ⨯₃ c) + (b ⨯₃ c) ⬝ᵥ (c ⨯₃ a) + (b ⨯₃ c) ⬝ᵥ (a ⨯₃ b) = (b ⨯₃ c) ⬝ᵥ ((b - a) ⨯₃ (c - a)) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem cross_flip (o x y : Fin 3 → R) :
    ((o - y) ⨯₃ (x - y)) ⬝ᵥ ((o - y) ⨯₃ (x - y)) = ((o - x) ⨯₃ (y - x)) ⬝ᵥ ((o - x) ⨯₃ (y - x)) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem norm_flip (x y : Fin 3 → R) : (x - y) ⬝ᵥ (x - y) = (y - x) ⬝ᵥ (y - x) := by
  simp [dotProduct, Fin.sum_univ_three]; ring

/-- The squared tetrahedral sine law, cleared: with `σ(X; Y, Z) = |(X − Y) × (Z − Y)|²` and edge norms,
`σ_A(O,B) σ_B(O,C) σ_C(O,A) · |OA|²|AC|²|OC|²|CB|²|OB|²|BA|² =
 σ_A(O,C) σ_C(O,B) σ_B(O,A) · |OA|²|AB|²|OB|²|BC|²|OC|²|CA|²`. -/
theorem tetra_sine_ring (o a b c : Fin 3 → R) :
    (((o - a) ⨯₃ (b - a)) ⬝ᵥ ((o - a) ⨯₃ (b - a)) * (((o - b) ⨯₃ (c - b)) ⬝ᵥ ((o - b) ⨯₃ (c - b))) *
        (((o - c) ⨯₃ (a - c)) ⬝ᵥ ((o - c) ⨯₃ (a - c)))) *
      (((o - a) ⬝ᵥ (o - a)) * ((c - a) ⬝ᵥ (c - a)) * (((o - c) ⬝ᵥ (o - c)) * ((b - c) ⬝ᵥ (b - c))) *
        (((o - b) ⬝ᵥ (o - b)) * ((a - b) ⬝ᵥ (a - b)))) =
    (((o - a) ⨯₃ (c - a)) ⬝ᵥ ((o - a) ⨯₃ (c - a)) * (((o - c) ⨯₃ (b - c)) ⬝ᵥ ((o - c) ⨯₃ (b - c))) *
        (((o - b) ⨯₃ (a - b)) ⬝ᵥ ((o - b) ⨯₃ (a - b)))) *
      (((o - a) ⬝ᵥ (o - a)) * ((b - a) ⬝ᵥ (b - a)) * (((o - b) ⬝ᵥ (o - b)) * ((c - b) ⬝ᵥ (c - b))) *
        (((o - c) ⬝ᵥ (o - c)) * ((a - c) ⬝ᵥ (a - c)))) := by
  rw [cross_flip o a c, cross_flip o c b, cross_flip o b a, norm_flip c a, norm_flip b c, norm_flip a b]
  ring

end Ring

abbrev u : Vec 3 18 := Vec.vars 3 0 (by norm_num)
abbrev v : Vec 3 18 := Vec.vars 3 6 (by norm_num)
abbrev w : Vec 3 18 := Vec.vars 3 12 (by norm_num)

/-- `(v × w) × (w × u) = [u v w] w`. -/
def polarCrossFormula : Fm PTm 18 :=
  Vec.eqFm (Vec.cross (Vec.cross v w) (Vec.cross w u)) (Vec.smul (Vec.triple u v w) w)

theorem polar_cross : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 polarCrossFormula :=
  closeUniv 18 (Vec.derive (by
    simp only [Vec.toZ_cross, Vec.toZ_smul, Vec.toZ_triple]
    exact cross_cross_ring _ _ _))

/-- `(w × u)·(u × v) = (w·u)(u·v) − (u·u)(v·w)`. -/
def polarSideFormula : Fm PTm 18 :=
  ZT.eq (Vec.dot (Vec.cross w u) (Vec.cross u v)) (Vec.dot w u * Vec.dot u v - Vec.dot u u * Vec.dot v w)

theorem polar_side : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 polarSideFormula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, ZT.toZ_sub, ZT.toZ_mul]
    exact polar_side_ring _ _ _))

/-- `[v × w, w × u, u × v] = [u v w]²`. -/
def polarTripleFormula : Fm PTm 18 :=
  ZT.eq (Vec.triple (Vec.cross v w) (Vec.cross w u) (Vec.cross u v)) (ZT.sq (Vec.triple u v w))

theorem polar_triple : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 polarTripleFormula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_triple, Vec.toZ_cross, ZT.toZ_sq]
    exact polar_triple_ring _ _ _))

/-- `(v − u) × (w − u) = v × w + w × u + u × v`. -/
def faceClosureFormula : Fm PTm 18 :=
  Vec.eqFm (Vec.cross (Vec.sub v u) (Vec.sub w u))
    (Vec.add (Vec.add (Vec.cross v w) (Vec.cross w u)) (Vec.cross u v))

theorem face_closure : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 faceClosureFormula :=
  closeUniv 18 (Vec.derive (by
    simp only [Vec.toZ_cross, Vec.toZ_sub, Vec.toZ_add]
    exact face_closure_ring _ _ _))

/-- The tetrahedral cosine law in face-normal form. -/
def tetraCosineFormula : Fm PTm 18 :=
  ZT.eq (Vec.dot (Vec.cross (Vec.sub v u) (Vec.sub w u)) (Vec.cross (Vec.sub v u) (Vec.sub w u)))
    (Vec.dot (Vec.cross v w) (Vec.cross v w) + Vec.dot (Vec.cross w u) (Vec.cross w u) +
      Vec.dot (Vec.cross u v) (Vec.cross u v) +
      ZT.natLit 2 * (Vec.dot (Vec.cross v w) (Vec.cross w u) + Vec.dot (Vec.cross v w) (Vec.cross u v) +
        Vec.dot (Vec.cross w u) (Vec.cross u v)))

theorem tetra_cosine : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 tetraCosineFormula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_sub, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
    exact tetra_cosine_ring _ _ _))

/-- `cor:tetra-linear`, cleared: dotting the closure with the face normal `N₀ = (v − u) × (w − u)` gives
`N₀·N₀ = N₀·N₁ + N₀·N₂ + N₀·N₃` with `N₁ = v × w`, `N₂ = w × u`, `N₃ = u × v`, i.e.
`Δ₀ = Δ₁ cos θ + Δ₂ cos θ' + Δ₃ cos θ''` after dividing by `Δ₀`. -/
def tetraLinear0Formula : Fm PTm 18 :=
  ZT.eq (Vec.dot (Vec.cross (Vec.sub v u) (Vec.sub w u)) (Vec.cross (Vec.sub v u) (Vec.sub w u)))
    (Vec.dot (Vec.cross (Vec.sub v u) (Vec.sub w u)) (Vec.cross v w) +
      Vec.dot (Vec.cross (Vec.sub v u) (Vec.sub w u)) (Vec.cross w u) +
      Vec.dot (Vec.cross (Vec.sub v u) (Vec.sub w u)) (Vec.cross u v))

theorem tetra_linear0 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 tetraLinear0Formula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_sub, ZT.toZ_add]
    exact tetra_linear0_ring _ _ _))

/-- `cor:tetra-linear` at a face through the apex: `N₁·N₁ + N₁·N₂ + N₁·N₃ = N₁·N₀`. -/
def tetraLinear1Formula : Fm PTm 18 :=
  ZT.eq (Vec.dot (Vec.cross v w) (Vec.cross v w) + Vec.dot (Vec.cross v w) (Vec.cross w u) +
      Vec.dot (Vec.cross v w) (Vec.cross u v))
    (Vec.dot (Vec.cross v w) (Vec.cross (Vec.sub v u) (Vec.sub w u)))

theorem tetra_linear1 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 tetraLinear1Formula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_sub, ZT.toZ_add]
    exact tetra_linear1_ring _ _ _))

section TetraSine

abbrev O : Vec 3 24 := Vec.vars 3 0 (by norm_num)
abbrev A : Vec 3 24 := Vec.vars 3 6 (by norm_num)
abbrev B : Vec 3 24 := Vec.vars 3 12 (by norm_num)
abbrev C : Vec 3 24 := Vec.vars 3 18 (by norm_num)

/-- `σ(X; Y, Z) = |(X − Y) × (Z − Y)|²`, the squared doubled area seen from `Y`. -/
abbrev sg2 (X Y Z : Vec 3 24) : ZT 24 := Vec.dot (Vec.cross (Vec.sub X Y) (Vec.sub Z Y)) (Vec.cross (Vec.sub X Y) (Vec.sub Z Y))
abbrev nm2 (X Y : Vec 3 24) : ZT 24 := Vec.dot (Vec.sub X Y) (Vec.sub X Y)

/-- `thm:tetra-sine`, squared and cleared: with `sin² ∠XYZ = σ(X; Y, Z) / (|X − Y|² |Z − Y|²)`,
`sin²∠OAB sin²∠OBC sin²∠OCA = sin²∠OAC sin²∠OCB sin²∠OBA`. -/
def tetraSineFormula : Fm PTm 24 :=
  ZT.eq ((sg2 O A B * sg2 O B C * sg2 O C A) * (nm2 O A * nm2 C A * (nm2 O C * nm2 B C) * (nm2 O B * nm2 A B)))
    ((sg2 O A C * sg2 O C B * sg2 O B A) * (nm2 O A * nm2 B A * (nm2 O B * nm2 C B) * (nm2 O C * nm2 A C)))

theorem tetra_sine : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 24 tetraSineFormula :=
  closeUniv 24 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_sub, ZT.toZ_mul]
    exact tetra_sine_ring _ _ _ _))

end TetraSine

end LeanProofs.IPRA.Geometry.SphericalPolar
