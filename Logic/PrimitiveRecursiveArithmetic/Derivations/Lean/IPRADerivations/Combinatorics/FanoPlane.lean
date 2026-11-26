import IPRADerivations.Core.CertificateTactics

/-!
# The Fano plane as a symmetric `2-(7, 3, 1)` design

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, result 47: "At `q = 2` it gives the seven-point,
seven-line Fano plane ... let `a, b, c, d` denote respectively `00, 01, 10, 11`; let `v, h, s` denote vertical,
horizontal and slope-one infinity. The seven lines are `abv, cdv, ach, bdh, ads, bcs, vhs`."

The incidence table `inc` (points `a, b, c, d, v, h, s` as rows `0, …, 6`, the lines in the order of the packet
as columns) is a table of numerals. As iPRA derivations, for all points and lines:

* `fano_bit`: the entries are bits;
* `fano_point`, `fano_line`: every point is on three lines and every line has three points;
* `fano_pair`: two distinct points are on exactly one common line ("uniqueness of the joining line");
* `fano_meet`: two distinct lines have exactly one common point.

So the table is a `2-(7, 3, 1)` design with as many blocks as points, the equality case of Fisher's inequality
(`Combinatorics/FisherInequality`), and its parameters satisfy the counts of `Combinatorics/DesignCounts`.

Not derived: the construction from a field table for every `q`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FanoPlane

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The incidence of the Fano plane: rows are the points `a, b, c, d, v, h, s`, columns the lines
`abv, cdv, ach, bdh, ads, bcs, vhs`. -/
def inc (i B : Fin 7) : ℕ :=
  (![![1, 0, 1, 0, 1, 0, 0], ![1, 0, 0, 1, 0, 1, 0], ![0, 1, 1, 0, 0, 1, 0], ![0, 1, 0, 1, 1, 0, 0],
    ![1, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 1], ![0, 0, 0, 0, 1, 1, 1]] : Fin 7 → Fin 7 → ℕ) i B

theorem inc_bit : ∀ i B : Fin 7, inc i B * inc i B = inc i B := by decide

theorem inc_point : ∀ i : Fin 7, ∑ B, inc i B = 3 := by decide

theorem inc_line : ∀ B : Fin 7, ∑ i, inc i B = 3 := by decide

theorem inc_pair : ∀ i j : Fin 7, i ≠ j → ∑ B, inc i B * inc j B = 1 := by decide

theorem inc_meet : ∀ B C : Fin 7, B ≠ C → ∑ i, inc i B * inc i C = 1 := by decide

/-- The entries of the incidence table are bits. -/
theorem fano_bit (i B : Fin 7) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit (inc i B) * ZT.natLit (inc i B)) (ZT.natLit (inc i B) : ZT n) := by
  ipra_cast inc_bit i B

/-- Every point is on three lines. -/
theorem fano_point (i : Fin 7) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => (ZT.natLit (inc i B) : ZT n)) (ZT.natLit 3) := by
  ipra_cast inc_point i

/-- Every line has three points. -/
theorem fano_line (B : Fin 7) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => (ZT.natLit (inc i B) : ZT n)) (ZT.natLit 3) := by
  ipra_cast inc_line B

/-- Two distinct points are on exactly one common line. -/
theorem fano_pair (i j : Fin 7) (hij : i ≠ j) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => (ZT.natLit (inc i B) : ZT n) * ZT.natLit (inc j B)) (ZT.natLit 1) := by
  ipra_cast inc_pair i j hij

/-- Two distinct lines have exactly one common point. -/
theorem fano_meet (B C : Fin 7) (hBC : B ≠ C) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => (ZT.natLit (inc i B) : ZT n) * ZT.natLit (inc i C)) (ZT.natLit 1) := by
  ipra_cast inc_meet B C hBC

end LeanProofs.IPRA.Combinatorics.FanoPlane
