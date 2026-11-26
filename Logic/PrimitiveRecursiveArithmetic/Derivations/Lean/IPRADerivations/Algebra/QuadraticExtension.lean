import IPRADerivations.Core.Tactic

/-!
# The pair ring of a quadratic extension

Packet: `geometry/isoperimetric_ipra` (`lem:orderedextension`, the ring part). The packet adjoins
a square root of `d` to a ring by pairs `(a, b)`, read as `a + b √d`, with the product

  `(a, b)(c, e) = (a c + b e d, a e + b c)`.

Over the integers, both coordinates of each law are polynomial identities:

* `mul_comm`, `mul_assoc`, `distrib`, `one_mul`: the pair product is commutative, associative,
  distributes over addition, and `(1, 0)` is a unit;
* `root_sq`: `(0, 1)(0, 1) = (d, 0)`, so `(0, 1)` is a square root of `d`;
* `conj_mul`: `(a, b)(a, −b) = (a² − d b², 0)`;
* `norm_mul`: the norm `N(a, b) = a² − d b²` is multiplicative.

The sign rule, the order on the extension and its use for the vertices of regular polygons are
not formalized.
-/

namespace LeanProofs.IPRA.Algebra.QuadraticExtension

open_ipra

abbrev a : ZT 14 := .var2 0 1
abbrev b : ZT 14 := .var2 2 3
abbrev c : ZT 14 := .var2 4 5
abbrev e : ZT 14 := .var2 6 7
abbrev f : ZT 14 := .var2 8 9
abbrev g : ZT 14 := .var2 10 11
abbrev d : ZT 14 := .var2 12 13

/-- The first coordinate of `(u₁, u₂)(v₁, v₂)`. -/
abbrev m₁ (u₁ u₂ v₁ v₂ : ZT 14) : ZT 14 := u₁ * v₁ + u₂ * v₂ * d
/-- The second coordinate of `(u₁, u₂)(v₁, v₂)`. -/
abbrev m₂ (u₁ u₂ v₁ v₂ : ZT 14) : ZT 14 := u₁ * v₂ + u₂ * v₁
/-- The norm `u₁² − d u₂²`. -/
abbrev nm (u₁ u₂ : ZT 14) : ZT 14 := u₁ * u₁ - d * (u₂ * u₂)

def commFormula : Fm PTm 14 := ZT.eq (m₁ a b c e) (m₁ c e a b) ⋏ ZT.eq (m₂ a b c e) (m₂ c e a b)

def assocFormula : Fm PTm 14 :=
  ZT.eq (m₁ (m₁ a b c e) (m₂ a b c e) f g) (m₁ a b (m₁ c e f g) (m₂ c e f g)) ⋏
    ZT.eq (m₂ (m₁ a b c e) (m₂ a b c e) f g) (m₂ a b (m₁ c e f g) (m₂ c e f g))

def distribFormula : Fm PTm 14 :=
  ZT.eq (m₁ a b (c + f) (e + g)) (m₁ a b c e + m₁ a b f g) ⋏
    ZT.eq (m₂ a b (c + f) (e + g)) (m₂ a b c e + m₂ a b f g)

def oneFormula : Fm PTm 14 :=
  ZT.eq (m₁ (ZT.natLit 1) (ZT.natLit 0) a b) a ⋏ ZT.eq (m₂ (ZT.natLit 1) (ZT.natLit 0) a b) b

def rootFormula : Fm PTm 14 :=
  ZT.eq (m₁ (ZT.natLit 0) (ZT.natLit 1) (ZT.natLit 0) (ZT.natLit 1)) d ⋏
    ZT.eq (m₂ (ZT.natLit 0) (ZT.natLit 1) (ZT.natLit 0) (ZT.natLit 1)) (ZT.natLit 0)

def conjFormula : Fm PTm 14 := ZT.eq (m₁ a b a (-b)) (nm a b) ⋏ ZT.eq (m₂ a b a (-b)) (ZT.natLit 0)

def normFormula : Fm PTm 14 := ZT.eq (nm (m₁ a b c e) (m₂ a b c e)) (nm a b * nm c e)

theorem comm_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] commFormula := by
  unfold commFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem assoc_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] assocFormula := by
  unfold assocFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem distrib_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] distribFormula := by
  unfold distribFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem one_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] oneFormula := by
  unfold oneFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem root_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] rootFormula := by
  unfold rootFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem conj_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] conjFormula := by
  unfold conjFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem norm_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] normFormula := by
  unfold normFormula; ipra_ring

/-- The pair product is commutative. -/
theorem mul_comm : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 commFormula := closeAll 14 comm_open
/-- The pair product is associative. -/
theorem mul_assoc : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 assocFormula := closeAll 14 assoc_open
/-- The pair product distributes over addition. -/
theorem distrib : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 distribFormula := closeAll 14 distrib_open
/-- `(1, 0)` is a unit. -/
theorem one_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 oneFormula := closeAll 14 one_open
/-- `(0, 1)² = (d, 0)`. -/
theorem root_sq : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 rootFormula := closeAll 14 root_open
/-- `(a, b)(a, −b) = (a² − d b², 0)`. -/
theorem conj_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 conjFormula := closeAll 14 conj_open
/-- The norm is multiplicative. -/
theorem norm_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 normFormula := closeAll 14 norm_open

end LeanProofs.IPRA.Algebra.QuadraticExtension
