import Diophantine.Paper1980.Kernel3

/-!
# The 91-operation tag-system certificate (alternative universal architecture)

`Papers/1980/EXPLORATION_PRODUCT_COORDINATE_TAG.md` (the last of the chain
`EXPLORATION_TAG_QUEUE_HISTORY.md` → … → `EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`),
receipt `Papers/verification/explore_product_coordinate_tag.json`: 91 operations
(50 multiplications, 41 additions), 18 equations in 29 positive unknowns with the
encoded-instance parameters `Ninit, Linit`.

The fixed data of the binary tag system (productions `0 → 0`, `1 → u`, deletion
number `β`, halting when the queue is shorter than `K = 3^β`) are the **tag
constants** `k = K/3`, `Ut = (U − ε)/3` (with `U` the value of the appendant `u` and
`ε = U mod 3 ∈ {0, 1}` its leading branch), `B = 3^(a−1)` (with `a` the appendant
length), the fixed power of three `C`, `j = (C − C/K)/2` and `cc = (k − 1)/2`.  They
are parameters of the transcription `Sys91`; the receipt instantiates them with
`k = 9`, `Ut = 1`, `B = 27`, `C = 3¹⁰`, `j = 28431`, `cc = 4`.

With `M₁ = 2Q + S₁` and `N = 3T + S₁` (`ε = 0`) or `N = 3T − 2Q` (`ε = 1`), the eight
outer equations are

    kD = R,  D(T − E + Ut·M₁) = N − Ninit,  D[L + (B − 1)M₁] = L − Linit + 3q,
    RH = H + q − 1,  RH = CZ,  Rv = q,  2r + 1 = q⁹ + 2P,  r + β = q⁹,

with the packed word

    P = H + (q − 1)S₁ + q²[Q + q(Q + Z)]
        + q⁴[L + (q − 1)M₁ + q²(cc·H + (q − 1)E + q²(N + jZ))],

and the ten base-three kernel equations (`Kernel3`) are taken at the scale
`D₀ = q⁹`.  Subtractions are interpreted over the integers.  The agreement with
the receipt's residual polynomials (both leading branches) is checked by
`Papers/verification/lean_sys91_transcription_check.py`.
-/

namespace Jones1980

/-- The fixed constants of a normalized binary tag system. -/
structure Tag91 where
  /-- `k = K/3`, a third of the halting threshold `K = 3^β`. -/
  Khalf : ℕ
  /-- `Ut = (U − ε)/3`, the appendant value without its leading trit. -/
  Uthird : ℕ
  /-- The leading branch `ε = U mod 3`. -/
  ε : ℕ
  /-- `B = 3^(a − 1)`. -/
  B : ℕ
  /-- The fixed power of three `C`. -/
  C : ℕ
  /-- `j = (C − C/K)/2`. -/
  jg : ℕ
  /-- `cc = (k − 1)/2`. -/
  cc : ℕ

/-- The fixed-constant contract of the tag certificate (`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`,
§1): `K = 3^β` with `β ≥ 2`, `k = K/3`, `B = 3^(a−1)` with `a ≥ 2`, `C` a power of three
above `K³`, `3K·3^a` and `2KU + 3` (with `U = 3·Ut + ε` the appendant value), `ε ∈ {0, 1}`,
`cc = (k − 1)/2` and `j = (C − C/K)/2`. -/
structure Tag91.Ok (T : Tag91) : Prop where
  Khalf_pow : ∃ β, 2 ≤ β ∧ T.Khalf = 3 ^ (β - 1)
  B_pow : ∃ a, 2 ≤ a ∧ T.B = 3 ^ (a - 1)
  C_pow : ∃ γ, T.C = 3 ^ γ
  ε_lt : T.ε < 2
  cc_eq : 2 * T.cc + 1 = T.Khalf
  jg_eq : 2 * T.jg + T.C / (3 * T.Khalf) = T.C
  K_dvd_C : 3 * T.Khalf ∣ T.C
  C_gt_K3 : (3 * T.Khalf) ^ 3 < T.C
  C_gt_KB : 3 * (3 * T.Khalf) * (3 * T.B) < T.C
  C_gt_KU : 2 * (3 * T.Khalf) * (3 * T.Uthird + T.ε) + 3 < T.C

/-- The content register `N = 3T + S₁` (`ε = 0`) or `3T − 2Q` (`ε = 1`). -/
def Tag91.N (T : Tag91) (Q S1 Tc : ℕ) : ℤ :=
  if T.ε = 0 then 3 * Tc + S1 else 3 * Tc - 2 * Q

/-- The 18 equations of the 91-operation certificate. -/
structure Sys91 (T : Tag91) (Ninit Linit : ℕ)
    (Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ) : Prop where
  /-- `kD = R`. -/
  E0 : T.Khalf * D = R
  /-- The content transport `D(T − E + Ut·M₁) = N − Ninit`. -/
  E1 : (D : ℤ) * ((Tc : ℤ) - E + T.Uthird * (2 * Q + S1)) = T.N Q S1 Tc - Ninit
  /-- The length transport `D[L + (B − 1)M₁] = L − Linit + 3q`. -/
  E2 : (D : ℤ) * ((L : ℤ) + ((T.B : ℤ) - 1) * (2 * Q + S1)) = (L : ℤ) - Linit + 3 * q
  /-- The head geometry `RH = H + q − 1`. -/
  E3 : R * H + 1 = H + q
  /-- The width product `RH = CZ`. -/
  E4 : R * H = T.C * Z
  /-- `Rv = q`. -/
  E5 : R * v = q
  /-- The packed index `2r + 1 = q⁹ + 2P`. -/
  E6 : (2 * r + 1 : ℤ) = (q : ℤ) ^ 9 + 2 * ((H : ℤ) + ((q : ℤ) - 1) * S1 + (q : ℤ) ^ 2 * (Q + q * (Q + Z))
    + (q : ℤ) ^ 4 * ((L : ℤ) + ((q : ℤ) - 1) * (2 * Q + S1)
      + (q : ℤ) ^ 2 * (T.cc * H + ((q : ℤ) - 1) * E + (q : ℤ) ^ 2 * (T.N Q S1 Tc + T.jg * Z))))
  /-- The index bound `r + β = q⁹`. -/
  E7 : r + β = q ^ 9
  /-- The ten kernel equations at the scale `D₀ = q⁹`. -/
  kernel : Kernel3 (q ^ 9) r a c d f h i j k o s w τ η ζ γ y

/-- Positivity of the 29 unknowns. -/
structure Pos91 (Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ) : Prop where
  Q : 0 < Q
  S1 : 0 < S1
  Tc : 0 < Tc
  E : 0 < E
  H : 0 < H
  R : 0 < R
  L : 0 < L
  q : 0 < q
  v : 0 < v
  r : 0 < r
  β : 0 < β
  D : 0 < D
  Z : 0 < Z
  kernel : KernelPos3 a c d f h i j k o s w τ η ζ γ y

/-- Solvability of the 91-operation certificate in positive integers at the encoded
instance `(Ninit, Linit)`. -/
def Solvable91 (T : Tag91) (Ninit Linit : ℕ) : Prop :=
  ∃ Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ,
    Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z ∧
    Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z

end Jones1980
