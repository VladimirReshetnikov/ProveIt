import Mathlib

/-!
# Finite rational observations

Each geometric tag uses radius and mass density one. The two elliptic
tags use the Legendre parameter 3/4 (modulus sqrt(3)/2). The quadrature
parameter is t = tan(θ/2) in [0,1]. All sampled quantities are rational.
These are executable Lean specifications in the metatheory. The roadmap
explains how to represent each fixed evaluator by a ConciseIPRA term.
-/
namespace Oloid.Observations

inductive Tag where
  | area | volume | axial | transverse | ellipticK | ellipticE | pi
  deriving Repr, DecidableEq

def weight (t : ℚ) : ℚ := 2 / (1 + t ^ 2)

def radicand (t : ℚ) : ℚ :=
  1 - (3/4 : ℚ) * (2*t / (1+t^2)) ^ 2

/-- Lower dyadic mesh root for a nonnegative rational. -/
def meshRoot (q : ℚ) (precision : ℕ) : ℚ :=
  let scale : ℕ := 2 ^ precision
  let numerator := Nat.sqrt (q.num.natAbs * scale ^ 2 / q.den)
  (numerator : ℚ) / (scale : ℚ)

/-- Exact result of the height and ruling-parameter integrations.
Use only with the three solid-moment tags. -/
def column (tag : Tag) (q : ℚ) : ℚ :=
  match tag with
  | .volume => 2/q - 1/(2*q^2)
  | .axial =>
    -32*q^2/15 + 12*q/5 - 1/5 - 1/(3*q) + 3/(5*q^2)
      - 1/(4*q^3) + 7/(240*q^4)
  | .transverse =>
    32*q^2/15 - 16*q/15 + 2/15 - 1/(10*q) - 5/(24*q^2)
      + 7/(24*q^3) - 7/(120*q^4)
  | _ => 0

def sample (tag : Tag) (precision : ℕ) (t : ℚ) : ℚ :=
  let q := radicand t
  let w := meshRoot q precision
  let transformed := match tag with
    | .area => 4 * (1 + 1/(2*q))
    | .ellipticK => 1/w
    | .ellipticE => w
    | .pi => 2
    | .volume | .axial | .transverse => column tag q / w
  weight t * transformed

def prefixSum (sampleAt : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | i+1 => prefixSum sampleAt i + sampleAt i

def grid (tag : Tag) (meshDepth rootDepth : ℕ) : ℚ :=
  let cells : ℕ := 2 ^ meshDepth
  prefixSum (fun i => sample tag rootDepth ((i : ℚ)/(cells : ℚ))) cells /
    (cells : ℚ)

/-- Direct guarantee from the estimates in the roadmap: the error is at
most 2^(-n-2). Smaller meshes are practical for low precision. -/
def observe (tag : Tag) (n : ℕ) : ℚ := grid tag (n+23) (n+17)

example : radicand 0 = 1 := by norm_num [radicand]
example : radicand 1 = 1/4 := by norm_num [radicand]
example : sample .area 0 0 = 12 := by norm_num [sample, weight, radicand]
example : sample .pi 0 1 = 2 := by norm_num [sample, weight]

end Oloid.Observations
