import IPRADerivations.Core.IntCertificates

/-!
# The Temperley–Lieb table on three strands and the brackets of small links

Packet: `topology/knot_theory_ipra`, `bracket.tex`, the proof of the Theorem "Regular isotopy and the Jones skein
relation": "For `k` vertical strands write `I` for the identity pairing and `e_i` for a cap and cup at positions
`i, i + 1` ... Tracing the affected endpoints gives `e_i² = δ e_i`, `e_i e_{i+1} e_i = e_i`,
`e_{i+1} e_i e_{i+1} = e_{i+1}`", with the crossing expansions "`R_i = A I + A⁻¹ e_i` and
`R_i⁻ = A⁻¹ I + A e_i`". For integer terms `A`, `B` (`B` in the role of `A⁻¹`) and `δ = −A² − B²` (`dl`):

* on two strands an element `α I + β e` is a pair, with product `m2₀`, `m2₁` and closure `tr2` (`δ` for `I`,
  `1` for `e`); `hopf_bracket`: the closure of `σ₁²` has bracket `−A⁴ − B⁴`; `trefoil_bracket`: the closure of
  `σ₁³` has bracket `−A⁵ − B³ + B⁷`; `trefoil_jones`: multiplied by `(−A³)⁻³ = −B⁹` it is `t + t³ − t⁴` for
  `t = B⁴`, the Jones polynomial of the trefoil;
* on three strands an element is a combination of `I, e₁, e₂, e₁ e₂, e₂ e₁`, with the product `m3₀, …, m3₄`
  read off from the three relations and the closure `tr3` (`δ², δ, δ, 1, 1`); `tl3_assoc₀, …, tl3_assoc₄`: the
  product is associative, for every `δ`;
* `move_II_I`, `move_II_e`: "`R_i R_i⁻ = I + (A² + A⁻² + δ) e_i = I`"; `move_III₁, …, move_III₄`:
  "`U W U − W U W = (A + A⁻¹ δ + A⁻³)(e − f) = 0`", coefficient by coefficient; `curl_pos`, `curl_neg`: "In a
  positive curl ... factor `A δ + A⁻¹ = −A³`. The opposite curl gives `A⁻¹ δ + A = −A⁻³`";
* `figure_eight_bracket`: the closure of `(σ₁ σ₂⁻¹)²` has bracket `A⁸ − A⁴ + 1 − B⁴ + B⁸`;
* `borromean_bracket`: the closure of `(σ₁ σ₂⁻¹)³` has bracket
  `−A¹² + 3A⁸ − 2A⁴ + 4 − 2B⁴ + 3B⁸ − B¹²`.

The relation `A B = 1` is not assumed as a hypothesis about integer terms (it would force `A = B = ±1`): each
move
and each bracket is the unconditional identity "traced product = value +
        `q` · (`A B − 1`)" with an explicit integer
polynomial `q` in `A`, `B`, that is, an identity of Laurent polynomials. Powers are written `pwr A k`.

Not derived: coded diagrams and the state sum over an arbitrary diagram, and the invariance of the bracket as
a statement about diagrams.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.TemperleyLieb

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The power `A^k` of an integer term. -/
def pwr (A : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 1
  | k + 1 => pwr A k * A

theorem toZ_pwr (A : ZT n) (k : ℕ) : ZT.toZ Γ (pwr A k) = ZT.toZ Γ A ^ k := by
  induction k with
  | zero => simp only [pwr, ZT.toZ_natLit, Nat.cast_one, pow_zero]
  | succ k ih => simp only [pwr, ZT.toZ_mul, ih, pow_succ]

/-- `δ = −A² − B²`. -/
def dl (A B : ZT n) : ZT n := -(A * A) - B * B

/-! ## Two strands -/

/-- Coefficient of `I` in `(a₀ I + a₁ e)(c₀ I + c₁ e)`. -/
def m2₀ (a₀ c₀ : ZT n) : ZT n := a₀ * c₀

/-- Coefficient of `e` in `(a₀ I + a₁ e)(c₀ I + c₁ e)`, by `e² = δ e`. -/
def m2₁ (d a₀ a₁ c₀ c₁ : ZT n) : ZT n := a₀ * c₁ + a₁ * c₀ + d * (a₁ * c₁)

/-- The closure of `a₀ I + a₁ e`: one extra circle for `I`, none for `e`. -/
def tr2 (d a₀ a₁ : ZT n) : ZT n := a₀ * d + a₁

/-! ## Three strands -/

/-- Coefficient of `I` in a product. -/
def m3₀ (a₀ c₀ : ZT n) : ZT n := a₀ * c₀

/-- Coefficient of `e₁` in a product. -/
def m3₁ (d a₀ a₁ a₃ c₀ c₁ c₄ : ZT n) : ZT n :=
  a₀ * c₁ + a₁ * c₀ + d * (a₁ * c₁) + a₁ * c₄ + a₃ * c₁ + d * (a₃ * c₄)

/-- Coefficient of `e₂` in a product. -/
def m3₂ (d a₀ a₂ a₄ c₀ c₂ c₃ : ZT n) : ZT n :=
  a₀ * c₂ + a₂ * c₀ + d * (a₂ * c₂) + a₂ * c₃ + a₄ * c₂ + d * (a₄ * c₃)

/-- Coefficient of `e₁ e₂` in a product. -/
def m3₃ (d a₀ a₁ a₃ c₀ c₂ c₃ : ZT n) : ZT n :=
  a₀ * c₃ + a₃ * c₀ + a₁ * c₂ + d * (a₁ * c₃) + d * (a₃ * c₂) + a₃ * c₃

/-- Coefficient of `e₂ e₁` in a product. -/
def m3₄ (d a₀ a₂ a₄ c₀ c₁ c₄ : ZT n) : ZT n :=
  a₀ * c₄ + a₄ * c₀ + a₂ * c₁ + d * (a₂ * c₄) + d * (a₄ * c₁) + a₄ * c₄

/-- The closure on three strands: `δ², δ, δ, 1, 1` on `I, e₁, e₂, e₁ e₂, e₂ e₁`. -/
def tr3 (d a₀ a₁ a₂ a₃ a₄ : ZT n) : ZT n := a₀ * (d * d) + a₁ * d + a₂ * d + a₃ + a₄

/-! ## One block `σ₁ σ₂⁻¹` on three strands -/

/-- Coefficient of `I` in one block `(A I + B e₁)(B I + A e₂)`. -/
def blk₀ (A B : ZT n) : ZT n := m3₀ A B

/-- Coefficient of `e₁` in one block `(A I + B e₁)(B I + A e₂)`. -/
def blk₁ (A B : ZT n) : ZT n := m3₁ (dl A B) A B (ZT.natLit 0) B (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `e₂` in one block `(A I + B e₁)(B I + A e₂)`. -/
def blk₂ (A B : ZT n) : ZT n := m3₂ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) B A (ZT.natLit 0)

/-- Coefficient of `e₁ e₂` in one block `(A I + B e₁)(B I + A e₂)`. -/
def blk₃ (A B : ZT n) : ZT n := m3₃ (dl A B) A B (ZT.natLit 0) B A (ZT.natLit 0)

/-- Coefficient of `e₂ e₁` in one block `(A I + B e₁)(B I + A e₂)`. -/
def blk₄ (A B : ZT n) : ZT n := m3₄ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) B (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `I` in the square of a block. -/
def blkSq₀ (A B : ZT n) : ZT n :=
  m3₀ (blk₀ A B) (blk₀ A B)

/-- Coefficient of `e₁` in the square of a block. -/
def blkSq₁ (A B : ZT n) : ZT n :=
  m3₁ (dl A B) (blk₀ A B) (blk₁ A B) (blk₃ A B) (blk₀ A B) (blk₁ A B) (blk₄ A B)

/-- Coefficient of `e₂` in the square of a block. -/
def blkSq₂ (A B : ZT n) : ZT n :=
  m3₂ (dl A B) (blk₀ A B) (blk₂ A B) (blk₄ A B) (blk₀ A B) (blk₂ A B) (blk₃ A B)

/-- Coefficient of `e₁ e₂` in the square of a block. -/
def blkSq₃ (A B : ZT n) : ZT n :=
  m3₃ (dl A B) (blk₀ A B) (blk₁ A B) (blk₃ A B) (blk₀ A B) (blk₂ A B) (blk₃ A B)

/-- Coefficient of `e₂ e₁` in the square of a block. -/
def blkSq₄ (A B : ZT n) : ZT n :=
  m3₄ (dl A B) (blk₀ A B) (blk₂ A B) (blk₄ A B) (blk₀ A B) (blk₁ A B) (blk₄ A B)

/-- Coefficient of `I` in `U W`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def uw₀ (A _B : ZT n) : ZT n := m3₀ A A

/-- Coefficient of `e₁` in `U W`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def uw₁ (A B : ZT n) : ZT n := m3₁ (dl A B) A B (ZT.natLit 0) A (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `e₂` in `U W`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def uw₂ (A B : ZT n) : ZT n := m3₂ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) A B (ZT.natLit 0)

/-- Coefficient of `e₁ e₂` in `U W`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def uw₃ (A B : ZT n) : ZT n := m3₃ (dl A B) A B (ZT.natLit 0) A B (ZT.natLit 0)

/-- Coefficient of `e₂ e₁` in `U W`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def uw₄ (A B : ZT n) : ZT n := m3₄ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) A (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `I` in `W U`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def wu₀ (A _B : ZT n) : ZT n := m3₀ A A

/-- Coefficient of `e₁` in `W U`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def wu₁ (A B : ZT n) : ZT n := m3₁ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) A B (ZT.natLit 0)

/-- Coefficient of `e₂` in `W U`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def wu₂ (A B : ZT n) : ZT n := m3₂ (dl A B) A B (ZT.natLit 0) A (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `e₁ e₂` in `W U`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def wu₃ (A B : ZT n) : ZT n := m3₃ (dl A B) A (ZT.natLit 0) (ZT.natLit 0) A (ZT.natLit 0) (ZT.natLit 0)

/-- Coefficient of `e₂ e₁` in `W U`, for `U = A I + B e₁`, `W = A I + B e₂`. -/
def wu₄ (A B : ZT n) : ZT n := m3₄ (dl A B) A B (ZT.natLit 0) A B (ZT.natLit 0)

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [blk₀, blk₁, blk₂, blk₃, blk₄, blkSq₀, blkSq₁, blkSq₂, blkSq₃, blkSq₄, toZ_pwr,
    uw₀, uw₁, uw₂, uw₃, uw₄, wu₀, wu₁, wu₂, wu₃, wu₄,
    dl, m2₀, m2₁, tr2, m3₀, m3₁, m3₂, m3₃, m3₄, tr3, zsl_def, ZT.toZ_add, ZT.toZ_sub,
    ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Associativity of the three-strand table -/

/-- Associativity, coefficient of `I`. -/
theorem tl3_assoc₀ (a₀ b₀ c₀ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₀ (m3₀ a₀ b₀) c₀)
      (m3₀ a₀ (m3₀ b₀ c₀)) := by
  geo

/-- Associativity, coefficient of `e₁`. -/
theorem tl3_assoc₁ (d a₀ a₁ a₃ b₀ b₁ b₂ b₃ b₄ c₀ c₁ c₄ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₁ d (m3₀ a₀ b₀) (m3₁ d a₀ a₁ a₃ b₀ b₁ b₄) (m3₃ d a₀ a₁ a₃ b₀ b₂ b₃) c₀ c₁ c₄)
      (m3₁ d a₀ a₁ a₃ (m3₀ b₀ c₀) (m3₁ d b₀ b₁ b₃ c₀ c₁ c₄) (m3₄ d b₀ b₂ b₄ c₀ c₁ c₄)) := by
  geo

/-- Associativity, coefficient of `e₂`. -/
theorem tl3_assoc₂ (d a₀ a₂ a₄ b₀ b₁ b₂ b₃ b₄ c₀ c₂ c₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₂ d (m3₀ a₀ b₀) (m3₂ d a₀ a₂ a₄ b₀ b₂ b₃) (m3₄ d a₀ a₂ a₄ b₀ b₁ b₄) c₀ c₂ c₃)
      (m3₂ d a₀ a₂ a₄ (m3₀ b₀ c₀) (m3₂ d b₀ b₂ b₄ c₀ c₂ c₃) (m3₃ d b₀ b₁ b₃ c₀ c₂ c₃)) := by
  geo

/-- Associativity, coefficient of `e₁ e₂`. -/
theorem tl3_assoc₃ (d a₀ a₁ a₃ b₀ b₁ b₂ b₃ b₄ c₀ c₂ c₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₃ d (m3₀ a₀ b₀) (m3₁ d a₀ a₁ a₃ b₀ b₁ b₄) (m3₃ d a₀ a₁ a₃ b₀ b₂ b₃) c₀ c₂ c₃)
      (m3₃ d a₀ a₁ a₃ (m3₀ b₀ c₀) (m3₂ d b₀ b₂ b₄ c₀ c₂ c₃) (m3₃ d b₀ b₁ b₃ c₀ c₂ c₃)) := by
  geo

/-- Associativity, coefficient of `e₂ e₁`. -/
theorem tl3_assoc₄ (d a₀ a₂ a₄ b₀ b₁ b₂ b₃ b₄ c₀ c₁ c₄ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₄ d (m3₀ a₀ b₀) (m3₂ d a₀ a₂ a₄ b₀ b₂ b₃) (m3₄ d a₀ a₂ a₄ b₀ b₁ b₄) c₀ c₁ c₄)
      (m3₄ d a₀ a₂ a₄ (m3₀ b₀ c₀) (m3₁ d b₀ b₁ b₃ c₀ c₁ c₄) (m3₄ d b₀ b₂ b₄ c₀ c₁ c₄)) := by
  geo

/-! ## Moves II and III and the curls, modulo `A B − 1` -/

/-- Move II, coefficient of `I` in `(A I + B e)(B I + A e)`: `1` modulo `A B − 1`. -/
theorem move_II_I (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m2₀ A B)
      (ZT.natLit 1 +
        (ZT.natLit 1) * (A * B - ZT.natLit 1)) := by
  geo

/-- Move II, coefficient of `e` in `(A I + B e)(B I + A e)`: `0` modulo `A B − 1`. -/
theorem move_II_e (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m2₁ (dl A B) A B B A)
      (ZT.natLit 0 +
        (-(pwr A 2) - pwr B 2) * (A * B - ZT.natLit 1)) := by
  geo

/-- A positive curl: the closure of `A I + B e` is `−A³` modulo `A B − 1`. -/
theorem curl_pos (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr2 (dl A B) A B)
      (-(pwr A 3) +
        (-(B)) * (A * B - ZT.natLit 1)) := by
  geo

/-- A negative curl: the closure of `B I + A e` is `−B³` modulo `A B − 1`. -/
theorem curl_neg (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr2 (dl A B) B A)
      (-(pwr B 3) +
        (-(A)) * (A * B - ZT.natLit 1)) := by
  geo

/-- Move III, coefficient of `e₁`: `U W U = W U W` modulo `A B − 1`, for `U = A I + B e₁`,
`W = A I + B e₂`. -/
theorem move_III₁ (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₁ (dl A B) (uw₀ A B) (uw₁ A B) (uw₃ A B) A B (ZT.natLit 0))
      (m3₁ (dl A B) (wu₀ A B) (wu₁ A B) (wu₃ A B) A (ZT.natLit 0) (ZT.natLit 0) +
        (-(pwr A 2 * B) - pwr B 3) * (A * B - ZT.natLit 1)) := by
  geo

/-- Move III, coefficient of `e₂`: `U W U = W U W` modulo `A B − 1`, for `U = A I + B e₁`,
`W = A I + B e₂`. -/
theorem move_III₂ (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₂ (dl A B) (uw₀ A B) (uw₂ A B) (uw₄ A B) A (ZT.natLit 0) (ZT.natLit 0))
      (m3₂ (dl A B) (wu₀ A B) (wu₂ A B) (wu₄ A B) A B (ZT.natLit 0) +
        (pwr A 2 * B + pwr B 3) * (A * B - ZT.natLit 1)) := by
  geo

/-- Move III, coefficient of `e₁ e₂`: `U W U = W U W` modulo `A B − 1`, for `U = A I + B e₁`,
`W = A I + B e₂`. -/
theorem move_III₃ (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₃ (dl A B) (uw₀ A B) (uw₁ A B) (uw₃ A B) A (ZT.natLit 0) (ZT.natLit 0))
      (m3₃ (dl A B) (wu₀ A B) (wu₁ A B) (wu₃ A B) A B (ZT.natLit 0) +
        (ZT.natLit 0) * (A * B - ZT.natLit 1)) := by
  geo

/-- Move III, coefficient of `e₂ e₁`: `U W U = W U W` modulo `A B − 1`, for `U = A I + B e₁`,
`W = A I + B e₂`. -/
theorem move_III₄ (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (m3₄ (dl A B) (uw₀ A B) (uw₂ A B) (uw₄ A B) A B (ZT.natLit 0))
      (m3₄ (dl A B) (wu₀ A B) (wu₂ A B) (wu₄ A B) A (ZT.natLit 0) (ZT.natLit 0) +
        (ZT.natLit 0) * (A * B - ZT.natLit 1)) := by
  geo

/-! ## Brackets on two strands -/

/-- The Hopf link, the closure of `σ₁²`: `−A⁴ − B⁴` modulo `A B − 1`. -/
theorem hopf_bracket (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr2 (dl A B) (m2₀ A A) (m2₁ (dl A B) A B A B))
      (-(pwr A 4) - pwr B 4 +
        (-(ZT.natLit 2 * A * B)) * (A * B - ZT.natLit 1)) := by
  geo

/-- The trefoil, the closure of `σ₁³`: `−A⁵ − B³ + B⁷` modulo `A B − 1`. -/
theorem trefoil_bracket (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr2 (dl A B) (m2₀ (m2₀ A A) A) (m2₁ (dl A B) (m2₀ A A) (m2₁ (dl A B) A B A B) A B))
      (-(pwr A 5) + pwr B 7 - pwr B 3 +
        (pwr A 3 * pwr B 2 - ZT.natLit 3 * pwr A 2 * B + ZT.natLit 2 * A * pwr B 4 - pwr B 3) * (A * B -
        ZT.natLit 1)) := by
  geo

/-- The writhe-normalized bracket of the trefoil: `t + t³ − t⁴` for `t = B⁴`, modulo `A B − 1`. -/
theorem trefoil_jones (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (-(pwr B 9) *
        tr2 (dl A B) (m2₀ (m2₀ A A) A) (m2₁ (dl A B) (m2₀ A A) (m2₁ (dl A B) A B A B) A B))
      (-(pwr B 16) + pwr B 12 + pwr B 4 +
        (pwr A 4 * pwr B 8 - pwr A 3 * pwr B 11 + pwr A 3 * pwr B 7 + ZT.natLit 3 * pwr A 2 * pwr B 10 +
        pwr A 2 * pwr B 6 - ZT.natLit 2 * A * pwr B 13 + A * pwr B 5 + pwr B 12 + pwr B 4) * (A * B -
        ZT.natLit 1)) := by
  geo

/-! ## Brackets on three strands -/

/-- The figure-eight knot, the closure of `(σ₁ σ₂⁻¹)²`: `A⁸ − A⁴ + 1 − B⁴ + B⁸` modulo `A B − 1`. -/
theorem figure_eight_bracket (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr3 (dl A B) (blkSq₀ A B) (blkSq₁ A B) (blkSq₂ A B) (blkSq₃ A B) (blkSq₄ A B))
      (pwr A 8 - pwr A 4 + pwr B 8 - pwr B 4 + ZT.natLit 1 +
        (ZT.natLit 3 * pwr A 5 * B - pwr A 4 + ZT.natLit 4 * pwr A 3 * pwr B 3 - ZT.natLit 4 * pwr A 2 * pwr B 2 +
        ZT.natLit 3 * A * pwr B 5 + A * B - pwr B 4 + ZT.natLit 1) * (A * B - ZT.natLit 1)) := by
  geo

/-- The Borromean rings, the closure of `(σ₁ σ₂⁻¹)³`, modulo `A B − 1`. -/
theorem borromean_bracket (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (tr3 (dl A B)
        (m3₀ (blkSq₀ A B) (blk₀ A B))
        (m3₁ (dl A B) (blkSq₀ A B) (blkSq₁ A B) (blkSq₃ A B) (blk₀ A B) (blk₁ A B) (blk₄ A B))
        (m3₂ (dl A B) (blkSq₀ A B) (blkSq₂ A B) (blkSq₄ A B) (blk₀ A B) (blk₂ A B) (blk₃ A B))
        (m3₃ (dl A B) (blkSq₀ A B) (blkSq₁ A B) (blkSq₃ A B) (blk₀ A B) (blk₂ A B) (blk₃ A B))
        (m3₄ (dl A B) (blkSq₀ A B) (blkSq₂ A B) (blkSq₄ A B) (blk₀ A B) (blk₁ A B) (blk₄ A B)))
      (-(pwr A 12) + ZT.natLit 3 * pwr A 8 - ZT.natLit 2 * pwr A 4 - pwr B 12 + ZT.natLit 3 * pwr B 8 -
        ZT.natLit 2 * pwr B 4 + ZT.natLit 4 +
        (-(ZT.natLit 3 * pwr A 9 * B) + ZT.natLit 3 * pwr A 8 - ZT.natLit 3 * pwr A 7 * pwr B 3 +
        ZT.natLit 13 * pwr A 6 * pwr B 2 - ZT.natLit 2 * pwr A 5 * pwr B 5 - ZT.natLit 2 * pwr A 5 * B +
        ZT.natLit 18 * pwr A 4 * pwr B 4 - ZT.natLit 2 * pwr A 4 - ZT.natLit 3 * pwr A 3 * pwr B 7 -
        ZT.natLit 12 * pwr A 3 * pwr B 3 + ZT.natLit 13 * pwr A 2 * pwr B 6 + ZT.natLit 4 * pwr A 2 * pwr B 2 -
        ZT.natLit 3 * A * pwr B 9 - ZT.natLit 2 * A * pwr B 5 + ZT.natLit 4 * A * B + ZT.natLit 3 * pwr B 8 -
        ZT.natLit 2 * pwr B 4 + ZT.natLit 4) * (A * B - ZT.natLit 1)) := by
  geo

end LeanProofs.IPRA.Topology.TemperleyLieb
