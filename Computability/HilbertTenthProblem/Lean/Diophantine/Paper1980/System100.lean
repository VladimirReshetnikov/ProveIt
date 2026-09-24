import Diophantine.Paper1980.Kernel3

/-!
# The 100-operation counter-machine system (alternative universal architecture)

`Papers/1980/EXPLORATION_STATE_TOP_DOUBLED_GRID.md` (building on
`EXPLORATION_DOUBLED_GRID_COMPLEMENTS.md`, `EXPLORATION_INTERLEAVED_GRID_COMPLEMENTS.md`
and the raw-counter compiler chain), receipt
`Papers/verification/explore_state_top_doubled_grid.json`: 100 operations
(55 multiplications, 45 additions), 22 equations in 34 positive unknowns with the
supplied input `x`.

The fixed data of the compiled three-counter controller are the **ROM constants**
`Zon` (the fixed Boolean ternary grid numeral), `B₀ = 3^ℓ` (the grid spacing), `K`
(the transition table), `g` (the marker `3^d`), `I` (the cyclic initial/terminal
code), `hs, hz` (the sign and zero-request ports), `S` (the fixed state word).
They are parameters of the transcription `Sys100`; the receipt instantiates them
with the numerals of the maintained example (`B₀ = 9`).

With `J = Jrep`, `t = Tgap`, `D = Dzero`, `z = zgrid`, `α = alphaI`, the twelve
outer equations are

    q = J + 1,  q = W v,  W = R³,  H(R − 1) = 2J,  Kplus + Kminus = H,
    (B₀ − 1)(Zon + z) = R − 1,  6t = (R − 3)D,
    W(A₀ + A₁ + Kplus − Kminus) = A₀ + A₁ − 4x,  4x + α = R,
    2r + 1 = q¹² + P,  r + β = q¹²,
    (RK − g)C = 2gIJ + R(V + hs·Kplus + hz·D),

where the packed register is computed as

    X = Kminus + q²[D + q²(A₀ + q²(A₁ + q²(V + q²C)))],
    P = J·X + (1 + q²)(H + q⁴t) + q⁸H(z + q²S),

and the ten base-three kernel equations (`Kernel3`) are taken at the scale
`D₀ = q¹²`.  Every equation is transcribed from the receipt's instruction
schedule (so subtractions are avoided by moving terms across the equality); the
agreement with the receipt's residual polynomials is checked by
`Papers/verification/lean_sys100_transcription_check.py`.
-/

namespace Jones1980

/-- The fixed ROM constants of a compiled controller. -/
structure ROM100 where
  /-- The fixed Boolean ternary grid numeral. -/
  Zon : ℕ
  /-- The grid spacing `B₀ = 3^ℓ`. -/
  B0 : ℕ
  /-- The transition table. -/
  K : ℕ
  /-- The marker `g = 3^d`. -/
  g : ℕ
  /-- The cyclic initial and terminal code. -/
  I : ℕ
  /-- The sign port `hs = 3^(d + b_s)`. -/
  hs : ℕ
  /-- The zero-request port `hz = 3^(d + b_z)`. -/
  hz : ℕ
  /-- The fixed state word. -/
  S : ℕ

/-- The 22 equations of the 100-operation system. -/
structure Sys100 (C : ROM100) (x : ℕ)
    (q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ) :
    Prop where
  /-- `q = J + 1`. -/
  E0 : q = J + 1
  /-- `q = W v`. -/
  E1 : q = W * v
  /-- `H(R − 1) = 2J`. -/
  E2 : H * R = H + 2 * J
  /-- `Kplus + Kminus = H`. -/
  E3 : Kp + Km = H
  /-- The grid width `(B₀ − 1)(Zon + z) = R − 1`. -/
  E4 : (C.B0 - 1) * (C.Zon + z) + 1 = R
  /-- `6t = (R − 3)D`. -/
  E5 : 6 * t + 3 * D = D * R
  /-- The time equation `W(A₀ + A₁ + Kplus − Kminus) = A₀ + A₁ − 4x`. -/
  E6 : W * (A0 + A1 + Kp) + 4 * x = A0 + A1 + W * Km
  /-- The input bound `4x + α = R`. -/
  E7 : 4 * x + α = R
  /-- The packed index `2r + 1 = q¹² + P`. -/
  E8 : 2 * r + 1 = q ^ 12 + (J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
    + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * C.S)))
  /-- The ten kernel equations at the scale `D₀ = q¹²`. -/
  kernel : Kernel3 (q ^ 12) r a c d f h i j k o s w τ η ζ γ y
  /-- `W = R³`. -/
  E19 : W = R ^ 3
  /-- The index bound `r + β = q¹²`. -/
  E20 : r + β = q ^ 12
  /-- The cyclic route `(RK − g)C = 2gIJ + R(V + hs·Kplus + hz·D)`. -/
  E21 : R * C.K * PC = C.g * PC + C.g * C.I * (2 * J) + R * (PV + C.hs * Kp + C.hz * D)

/-- Positivity of the 34 unknowns and of the input. -/
structure Pos100 (x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ) :
    Prop where
  x : 0 < x
  q : 0 < q
  J : 0 < J
  W : 0 < W
  H : 0 < H
  v : 0 < v
  t : 0 < t
  A0 : 0 < A0
  A1 : 0 < A1
  Kp : 0 < Kp
  Km : 0 < Km
  D : 0 < D
  α : 0 < α
  R : 0 < R
  PC : 0 < PC
  PV : 0 < PV
  β : 0 < β
  z : 0 < z
  r : 0 < r
  kernel : KernelPos3 a c d f h i j k o s w τ η ζ γ y

/-- Solvability of the 100-operation system in positive integers at the input `x`. -/
def Solvable100 (C : ROM100) (x : ℕ) : Prop :=
  ∃ q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ,
    Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y ∧
    Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y

end Jones1980
