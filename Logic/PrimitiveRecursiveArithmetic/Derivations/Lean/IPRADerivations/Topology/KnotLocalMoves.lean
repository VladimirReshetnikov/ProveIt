import IPRADerivations.Core.IntCertificates

/-!
# The local identities behind the Reidemeister moves: the bracket and Fox colourings

Packet: `topology/knot_theory_ipra`, `bracket.tex`, Theorem "Regular isotopy and the Jones skein relation", and
`color.tex`, Theorem "Coloring invariance and tricolorability" with the braid action that follows it. The
invariance proofs reduce each move to an identity between coefficients; those identities are derived here in iPRA
for integer terms.

The bracket. The Laurent variable is a pair of terms `A`, `B` with `A B = 1` (`B` is `A⁻¹`), and `δ` is a term with
`A² + B² + δ = 0` ("`δ = −A² − A⁻²`"). With the Temperley–Lieb relations `e² = δ e`, `e f e = e`, `f e f = f`
of the cap-cup pairings:

* `move_II`: "`R_i R_i⁻ = I + (A² + A⁻² + δ) e_i = I`": the coefficient `A² + B² + A B δ` of `e` vanishes (and the
  coefficient of `I` is `A B = 1`);
* `move_III`: "`U W U − W U W = (A + A⁻¹ δ + A⁻³)(e − f) = 0`": the coefficient `A² B + A B² δ + B³` vanishes;
* `curl_pos`, `curl_neg`: "In a positive curl the `A`-pairing detaches a circle, giving factor
  `A δ + A⁻¹ = −A³`. The opposite curl gives `A⁻¹ δ + A = −A⁻³`";
* `skein`: "Multiplying the first by `A⁴` and subtracting `A⁻⁴` times the second cancels `H` and leaves
  `(A⁻² − A²)(−A³)^{−u} U`", for the brackets `U`, `H` of the two smoothings.

Fox colourings. With the reflection `S_y(x) = 2y − x` (`refl`):

* `kink`, `type_II`, `type_III`: "`S_x(x) = x`, `S_y(S_y(x)) = x`, `S_z(S_y(x)) = S_{S_z(y)}(S_z(x))`", the last
  with "value `2z − 2y + x` on both sides" (`type_III_value`);
* `braid_relation`: for the generator `P(x, y) = (2x − y, x)`, "both `P₁ P₂ P₁` and `P₂ P₁ P₂` give
  `(2x − 2y + z, 2x − y, x)`": the first coordinates `S_{S_x(y)}(S_x(z))` and `S_x(S_y(z))` agree (the other
  two coordinates are syntactically equal);
* `pw`, `two_strand_power`: Proposition "All two-strand powers": "Put `d = x − y`. Then `P(x, y) = (x + d, y + d)`
  preserves `d`. Induction ... gives `(x + m d, y + m d)`", for every numeral `m` (the row closes exactly when
  `m d = 0`);
* `crossing_alternating`: Lemma "Endpoint equality": "A crossing preserves the alternating sum since
  `(2x − y) − x = x − y`";
* `stabilization_pos`, `stabilization_neg`: "The positive final crossing gives `(2u − v, u)`, the negative one
  gives `(v, 2v − u)`. In each case the closure equations force `u = v`".

These are identities over the integers, hence modulo every `n`. Not derived: the state sum over a coded diagram,
the tracing of pairings behind the Temperley–Lieb relations, and the bijections of colourings induced by the
moves.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.KnotLocalMoves

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The reflection `S_y(x) = 2y − x`. -/
def refl (y x : ZT n) : ZT n := ZT.natLit 2 * y - x

local macro "ksimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [refl, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

/-! ## The bracket -/

/-- Move II: the coefficient of `e` in `(A I + B e)(B I + A e)` vanishes. -/
theorem move_II {A B δ : ZT n} (hAB : Γ ⊢[PRAAx] ZT.eq (A * B) (ZT.natLit 1))
    (hδ : Γ ⊢[PRAAx] ZT.eq (A * A + B * B + δ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (A * A + B * B + A * B * δ) (ZT.natLit 0) := by
  have e1 := ZT.toZ_eq hAB
  have e2 := ZT.toZ_eq hδ
  apply ZT.derive
  ksimp at e1 e2 ⊢
  linear_combination e2 + ZT.toZ Γ δ * e1

/-- Move III: the coefficient of `e − f` in `U W U − W U W` vanishes. -/
theorem move_III {A B δ : ZT n} (hAB : Γ ⊢[PRAAx] ZT.eq (A * B) (ZT.natLit 1))
    (hδ : Γ ⊢[PRAAx] ZT.eq (A * A + B * B + δ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (A * A * B + A * B * B * δ + B * B * B) (ZT.natLit 0) := by
  have e1 := ZT.toZ_eq hAB
  have e2 := ZT.toZ_eq hδ
  apply ZT.derive
  ksimp at e1 e2 ⊢
  linear_combination ZT.toZ Γ B * e2 + ZT.toZ Γ B * ZT.toZ Γ δ * e1

/-- The positive curl: `A δ + B = −A³`. -/
theorem curl_pos {A B δ : ZT n} (hAB : Γ ⊢[PRAAx] ZT.eq (A * B) (ZT.natLit 1))
    (hδ : Γ ⊢[PRAAx] ZT.eq (A * A + B * B + δ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (A * δ + B) (-(A * A * A)) := by
  have e1 := ZT.toZ_eq hAB
  have e2 := ZT.toZ_eq hδ
  apply ZT.derive
  ksimp at e1 e2 ⊢
  linear_combination ZT.toZ Γ A * e2 - ZT.toZ Γ B * e1

/-- The negative curl: `B δ + A = −B³`. -/
theorem curl_neg {A B δ : ZT n} (hAB : Γ ⊢[PRAAx] ZT.eq (A * B) (ZT.natLit 1))
    (hδ : Γ ⊢[PRAAx] ZT.eq (A * A + B * B + δ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (B * δ + A) (-(B * B * B)) := by
  have e1 := ZT.toZ_eq hAB
  have e2 := ZT.toZ_eq hδ
  apply ZT.derive
  ksimp at e1 e2 ⊢
  linear_combination ZT.toZ Γ B * e2 - ZT.toZ Γ A * e1

/-- The skein relation: `A⁴ (−B³)(A U + B H) − B⁴ (−A³)(B U + A H) = (B² − A²) U`. -/
theorem skein {A B U H : ZT n} (hAB : Γ ⊢[PRAAx] ZT.eq (A * B) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      (A * A * A * A * (-(B * B * B)) * (A * U + B * H) -
        B * B * B * B * (-(A * A * A)) * (B * U + A * H))
      ((B * B - A * A) * U) := by
  have e1 := ZT.toZ_eq hAB
  apply ZT.derive
  ksimp at e1 ⊢
  linear_combination
    ((ZT.toZ Γ B * ZT.toZ Γ B - ZT.toZ Γ A * ZT.toZ Γ A) * ZT.toZ Γ U *
      (ZT.toZ Γ A * ZT.toZ Γ B * (ZT.toZ Γ A * ZT.toZ Γ B) + ZT.toZ Γ A * ZT.toZ Γ B + 1)) * e1

/-! ## Fox colourings -/

/-- Move I: `S_x(x) = x`. -/
theorem kink (x : ZT n) : Γ ⊢[PRAAx] ZT.eq (refl x x) x := by
  apply ZT.derive
  ksimp
  ring

/-- Move II: `S_y(S_y(x)) = x`. -/
theorem type_II (x y : ZT n) : Γ ⊢[PRAAx] ZT.eq (refl y (refl y x)) x := by
  apply ZT.derive
  ksimp
  ring

/-- Move III: `S_z(S_y(x)) = S_{S_z(y)}(S_z(x))`. -/
theorem type_III (x y z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl z (refl y x)) (refl (refl z y) (refl z x)) := by
  apply ZT.derive
  ksimp
  ring

/-- The common value in move III: `2z − 2y + x`. -/
theorem type_III_value (x y z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl z (refl y x)) (ZT.natLit 2 * z - ZT.natLit 2 * y + x) := by
  apply ZT.derive
  ksimp
  ring

/-- The braid relation for `P(x, y) = (S_x(y), x)`: the first coordinates of `P₁ P₂ P₁` and `P₂ P₁ P₂`. -/
theorem braid_relation (x y z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (refl (refl x y) (refl x z)) (refl x (refl y z)) := by
  apply ZT.derive
  ksimp
  ring

/-- Positive stabilization: the closure equation `2u − v = u` forces `u = v`. -/
theorem stabilization_pos {u v : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (refl u v) u) : Γ ⊢[PRAAx] ZT.eq u v := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ksimp at e
  linear_combination e

/-- Negative stabilization: the closure equation `2v − u = v` forces `u = v`. -/
theorem stabilization_neg {u v : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (refl v u) v) : Γ ⊢[PRAAx] ZT.eq u v := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ksimp at e
  linear_combination (-1 : Groth (Q Γ)) * e

/-- The row `P^m (x, y)` of the two-strand braid `σ₁^m`, for `P(x, y) = (S_x(y), x)`. -/
def pw (x y : ZT n) : ℕ → ZT n × ZT n
  | 0 => (x, y)
  | m + 1 => (refl (pw x y m).1 (pw x y m).2, (pw x y m).1)

/-- `P^m (x, y) = (x + m d, y + m d)` with `d = x − y`. -/
theorem two_strand_power (x y : ZT n) (m : ℕ) :
    (Γ ⊢[PRAAx] ZT.eq (pw x y m).1 (x + ZT.natLit m * (x - y))) ∧
      (Γ ⊢[PRAAx] ZT.eq (pw x y m).2 (y + ZT.natLit m * (x - y))) := by
  induction m with
  | zero =>
    constructor
    · apply ZT.derive
      show ZT.toZ Γ x = ZT.toZ Γ (x + ZT.natLit 0 * (x - y))
      ksimp
      ring
    · apply ZT.derive
      show ZT.toZ Γ y = ZT.toZ Γ (y + ZT.natLit 0 * (x - y))
      ksimp
      ring
  | succ m ih =>
    have e1 := ZT.toZ_eq ih.1
    have e2 := ZT.toZ_eq ih.2
    ksimp at e1 e2
    constructor
    · apply ZT.derive
      show ZT.toZ Γ (refl (pw x y m).1 (pw x y m).2) = ZT.toZ Γ (x + ZT.natLit (m + 1) * (x - y))
      ksimp
      push_cast
      linear_combination (2 : Groth (Q Γ)) * e1 - e2
    · apply ZT.derive
      show ZT.toZ Γ (pw x y m).1 = ZT.toZ Γ (y + ZT.natLit (m + 1) * (x - y))
      ksimp
      push_cast
      linear_combination e1

/-- A crossing preserves the alternating sum of a slice: `(2x − y) − x = x − y`. -/
theorem crossing_alternating (x y : ZT n) : Γ ⊢[PRAAx] ZT.eq (refl x y - x) (x - y) := by
  apply ZT.derive
  ksimp
  ring

end LeanProofs.IPRA.Topology.KnotLocalMoves
