import IPRADerivations.Core.LinearCombination

/-!
# The two-orbit placement of the Conway criterion

Packet: `geometry/conway_criterion_ipra_2026-11-16`, Sections 2 and 3: `eq:fourcompositions`,
`lem:orbitpairs` ("Pairing with the second orbit") and `prop:edgepaired` ("Every open boundary
segment is paired": "The table proves the assertion for direct tiles. Reversing each row proves
it for the corresponding turned tile. ... Applying any map twice returns the original index. All
equalities are consequences of `lem:orbitpairs` and integer addition.").

A half-turn with doubled centre `c` is `x ↦ c − x`, a translation is `x ↦ x + w`. The doubled
centres of the four centrosymmetric paths `b, c, e, f` are `p`, `q = p + t`, `r`, `s = r − t`
(`eq:centers`, `eq:centerrelations`), and `u = r − p`. The placements are
`T⁰_{m,k}(x) = x + m t + k u` and `T¹_{m,k}(x) = (r − x) + m t + k u`. Every statement is an
affine identity of one coordinate, for arbitrary integer terms (`ZT`); it is applied to each of
the two coordinates of a point.

* `comp_p`, `comp_q`, `comp_r`, `comp_s` (`eq:fourcompositions`): `h_r h_p = τ_u`,
  `h_r h_q = τ_{u−t}`, `h_r h_r = id`, `h_r h_s = τ_t`;
* `turned_pair` (`lem:orbitpairs`, last assertion): `h_r(x + t) = h_r(x) − t`;
* `row_a`, `row_d`, `row_b`, `row_c`, `row_e`, `row_f` (the adjacency table): a point `x` of a
  boundary path of `T⁰_{m,k}` is the placed partner point (`x + t`, `p − x`, `q − x`, `r − x`,
  `s − x`) of the matching path of the neighbouring tile `T⁰_{m−1,k}`, `T⁰_{m+1,k}`,
  `T¹_{m,k−1}`, `T¹_{m+1,k−1}`, `T¹_{m,k}`, `T¹_{m−1,k}`;
* `turned_a`, `turned_d`, `turned_b`, `turned_c`, `turned_e`, `turned_f`: the same for the turned
  tile `T¹_{m,k}`, with the neighbours `T¹_{m+1,k}`, `T¹_{m−1,k}`, `T⁰_{m,k+1}`,
  `T⁰_{m−1,k+1}`, `T⁰_{m,k}`, `T⁰_{m+1,k}`;
* `index_back`, `index_forth`: the neighbour maps are involutive on the indices.

The paths as lists of points and their reversal are not formalized; the identities are the
statements about each of their points.
-/

namespace LeanProofs.IPRA.Geometry.ConwayOrbit

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Orbit

variable (p r t : ZT n)

/-- The doubled centre `q = p + t`. -/
abbrev qc : ZT n := p + t
/-- The doubled centre `s = r − t`. -/
abbrev sc : ZT n := r - t
/-- The second period `u = r − p`. -/
abbrev up : ZT n := r - p

/-- The direct placement `T⁰_{m,k}(x) = x + m t + k u`. -/
abbrev P0 (m k x : ZT n) : ZT n := x + m * t + k * up p r
/-- The turned placement `T¹_{m,k}(x) = (r − x) + m t + k u`. -/
abbrev P1 (m k x : ZT n) : ZT n := (r - x) + m * t + k * up p r

/-! ## The four compositions -/

/-- `h_r h_p = τ_u`. -/
theorem comp_p (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (r - (p - x)) (x + up p r) := by
  ipra_ring

/-- `h_r h_q = τ_{u−t}`. -/
theorem comp_q (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (r - (qc p t - x)) (x + (up p r - t)) := by
  ipra_ring

/-- `h_r h_r = id`. -/
theorem comp_r (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (r - (r - x)) x := by
  ipra_ring

/-- `h_r h_s = τ_t`. -/
theorem comp_s (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (r - (sc r t - x)) (x + t) := by
  ipra_ring

/-- `lem:orbitpairs`, last assertion: the translated pair stays a translated pair in the turned
tile, `h_r(τ_t(x)) = τ_{−t}(h_r(x))`. -/
theorem turned_pair (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (r - (x + t)) ((r - x) - t) := by
  ipra_ring

/-! ## The adjacency table of a direct tile -/

variable (m k : ZT n)

/-- Path `a` of `T⁰_{m,k}` is path `d` of `T⁰_{m−1,k}`. -/
theorem row_a (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P0 p r t m k x) (P0 p r t (m - ZT.natLit 1) k (x + t)) := by
  ipra_ring

/-- Path `d` of `T⁰_{m,k}` is path `a` of `T⁰_{m+1,k}`. -/
theorem row_d (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P0 p r t m k (x + t)) (P0 p r t (m + ZT.natLit 1) k x) := by
  ipra_ring

/-- Path `b` of `T⁰_{m,k}` is path `b` of `T¹_{m,k−1}`. -/
theorem row_b (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P0 p r t m k x) (P1 p r t m (k - ZT.natLit 1) (p - x)) := by
  ipra_ring

/-- Path `c` of `T⁰_{m,k}` is path `c` of `T¹_{m+1,k−1}`. -/
theorem row_c (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P0 p r t m k x)
      (P1 p r t (m + ZT.natLit 1) (k - ZT.natLit 1) (qc p t - x)) := by
  ipra_ring

/-- Path `e` of `T⁰_{m,k}` is path `e` of `T¹_{m,k}`. -/
theorem row_e (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (P0 p r t m k x) (P1 p r t m k (r - x)) := by
  ipra_ring

/-- Path `f` of `T⁰_{m,k}` is path `f` of `T¹_{m−1,k}`. -/
theorem row_f (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P0 p r t m k x) (P1 p r t (m - ZT.natLit 1) k (sc r t - x)) := by
  ipra_ring

/-! ## The adjacency table of a turned tile -/

/-- Path `a` of `T¹_{m,k}` is path `d` of `T¹_{m+1,k}`. -/
theorem turned_a (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P1 p r t m k x) (P1 p r t (m + ZT.natLit 1) k (x + t)) := by
  ipra_ring

/-- Path `d` of `T¹_{m,k}` is path `a` of `T¹_{m−1,k}`. -/
theorem turned_d (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P1 p r t m k (x + t)) (P1 p r t (m - ZT.natLit 1) k x) := by
  ipra_ring

/-- Path `b` of `T¹_{m,k}` is path `b` of `T⁰_{m,k+1}`. -/
theorem turned_b (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P1 p r t m k x) (P0 p r t m (k + ZT.natLit 1) (p - x)) := by
  ipra_ring

/-- Path `c` of `T¹_{m,k}` is path `c` of `T⁰_{m−1,k+1}`. -/
theorem turned_c (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P1 p r t m k x)
      (P0 p r t (m - ZT.natLit 1) (k + ZT.natLit 1) (qc p t - x)) := by
  ipra_ring

/-- Path `e` of `T¹_{m,k}` is path `e` of `T⁰_{m,k}`. -/
theorem turned_e (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (P1 p r t m k x) (P0 p r t m k (r - x)) :=
  ZT.derive rfl

/-- Path `f` of `T¹_{m,k}` is path `f` of `T⁰_{m+1,k}`. -/
theorem turned_f (x : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (P1 p r t m k x) (P0 p r t (m + ZT.natLit 1) k (sc r t - x)) := by
  ipra_ring

end Orbit

/-! ## The neighbour maps are involutive -/

/-- "Applying any map twice returns the original index": `(m − 1) + 1 = m`. -/
theorem index_back (m : ZT n) : Γ ⊢[PRAAx] ZT.eq ((m - ZT.natLit 1) + ZT.natLit 1) m := by
  ipra_lc

/-- `(m + 1) − 1 = m`. -/
theorem index_forth (m : ZT n) : Γ ⊢[PRAAx] ZT.eq ((m + ZT.natLit 1) - ZT.natLit 1) m := by
  ipra_ring

end LeanProofs.IPRA.Geometry.ConwayOrbit
