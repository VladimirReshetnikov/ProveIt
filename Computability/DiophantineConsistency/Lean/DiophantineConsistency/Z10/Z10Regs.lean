import DiophantineConsistency.Nine121.N105Layout
import DiophantineConsistency.Nine121.N9Norm

/-! # The ten-integer equations of package 106, register by register

Package 106 (`con-zfc-diophantine-forms/106-compact-certificates-round13/norm`), forms
`integer10_polar.json` (467 operations), `integer10_linear.json` (470),
`integer10_cubic.json` (473) and `integer10_sixterm.json` (507). Their ten unrestricted integer
unknowns, in order, are `t g0 c0 k0 l w x y z m` (`x 0 … x 9`); their fixed integers are the two
scales `radix = 2^2134940`, `threshold = 2^34159017` and ten coefficient leaves, which are
polynomials in the four ports `p = (β, K0, MC, MF)` of the 121x8801 machine.

**The prefix** (DAG nodes 19–399, identical in the four forms) is the H1868 layout of package 105
at the base `Bc b = 2^2134940 b²`: weights, targets and kernel positions are
`Nine121.N105Layout.weights/targets/pos0/pos1/pos2`, the kernel coefficients are
`Nine121.N101Layout.c0/c1/c2`. It differs from `Nine121.N105Prefix` in the scale (one more factor
two), in `Tc` (two less), in the multiplier `NN = Bc^1986` (no factor `2b`) and in the threshold,
which here is the single non-square `Y = 2^34159017 · b · Bc^2109`.

**The back end** (`regs`, DAG nodes 400–491 of the polar form) is the signed Pell certificate:
all registers that do not read the last unknown `m`. The polar value is the two-root norm
`out R m = norm2 (Sigma · m − Theta) Sigma a0 a1`.

**The three variants are translates of polar.** Their DAGs compute the same registers and the
same norm with the leaf `m` replaced by `m + shear`, where `shear` reads only `regs` and `y`
(`shearLin`, `shearCub`, `shearSix`). Since `regs` does not read `m` (`regs_congr`), a variant
has an integer zero exactly when polar has one (`exists_shift`).

The register equations `*_def` hold by `rfl`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Z10Regs
open Nine121 Nine121.N105Layout

/-- The radix scale of the code base. -/
def radix : ℤ := 2 ^ 2134940
/-- The scale of the binomial threshold. -/
def threshold : ℤ := 2 ^ 34159017
attribute [irreducible] radix threshold

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-! ## The prefix -/

/-- The code base `2^2134940 · b²`. -/
def Bc (b : 𝔸) : 𝔸 := (radix : 𝔸) * (b * b)
/-- The weight word `Σᵢ Bc^{wᵢ}`. -/
def ell (b : 𝔸) : 𝔸 := ∑ i, Bc b ^ weights i
/-- The target word `Σₖ Bc^{qₖ}`. -/
def AT (b : 𝔸) : 𝔸 := ∑ k, Bc b ^ targets k
def ker0 (p : Fin 4 → 𝔸) (b : 𝔸) : 𝔸 := ∑ q, N101Layout.c0 p q * Bc b ^ pos0 q
def ker1 (p : Fin 4 → 𝔸) (b : 𝔸) : 𝔸 := ∑ q, N101Layout.c1 p q * Bc b ^ pos1 q
def ker2 (p : Fin 4 → 𝔸) (b : 𝔸) : 𝔸 := ∑ q, N101Layout.c2 p q * Bc b ^ pos2 q
/-- The shifted code word `ℓ + g`. -/
def word (b g : 𝔸) : 𝔸 := ell b + g
/-- The source polynomial `K₀ + U(K₁ + U K₂)` at the code word. -/
def coded (p : Fin 4 → 𝔸) (b g : 𝔸) : 𝔸 :=
  ker0 p b + word b g * (ker1 p b + word b g * ker2 p b)
def N0 (b : 𝔸) : 𝔸 := Bc b ^ 117
def NN (b : 𝔸) : 𝔸 := Bc b ^ 1986
def mask (b : 𝔸) : 𝔸 := N0 b - 1 - ell b * (b - 1)
def Tc (b : 𝔸) : 𝔸 := mask b + N0 b * (AT b * (Bc b - 2)) - 2
def Sc (p : Fin 4 → 𝔸) (b g : 𝔸) : 𝔸 := g + N0 b * (AT b + 2 * coded p b g)
/-- The central-binomial argument `X = N (S_c + T_c + 1) − S_c − 1`. -/
def Xc (p : Fin 4 → 𝔸) (b g : 𝔸) : 𝔸 := NN b * (Sc p b g + Tc b + 1) - Sc p b g - 1
/-- The threshold `Y = 2^34159017 · b · Bc^2109`. -/
def Yc (b : 𝔸) : 𝔸 := b * ((threshold : 𝔸) * Bc b ^ 2109)
/-- The digit cap `b · Bc^116`. -/
def cap (b : 𝔸) : 𝔸 := b * Bc b ^ 116

/-! ## The back end -/

/-- The registers that do not read the last unknown `m`. -/
structure Regs (𝔸 : Type*) where
  b : 𝔸
  g : 𝔸
  k2 : 𝔸
  X : 𝔸
  Y : 𝔸
  cap : 𝔸
  L : 𝔸
  halfU : 𝔸
  U : 𝔸
  V : 𝔸
  W : 𝔸
  uv : 𝔸
  halfA : 𝔸
  A : 𝔸
  B1 : 𝔸
  C : 𝔸
  Phalf : 𝔸
  K : 𝔸
  S : 𝔸
  T : 𝔸
  Q : 𝔸
  Delta : 𝔸
  xi : 𝔸
  D : 𝔸
  E0 : 𝔸
  E : 𝔸
  E2 : 𝔸
  F : 𝔸
  G : 𝔸
  Omega : 𝔸
  H : 𝔸
  I : 𝔸
  rho : 𝔸
  Sigma : 𝔸
  Theta : 𝔸
  r : 𝔸
  a0 : 𝔸
  a1 : 𝔸

/-- The registers at the nine unknowns `t g0 c0 k0 l w x y z`. -/
def regs9 (p : Fin 4 → 𝔸) (t g0 c0 k0 l w xx y z : 𝔸) : Regs 𝔸 :=
  let b := 6 * t + 4
  let g := b * g0
  let k2 := b * (6 * k0 + 4)
  let X := Xc p b g
  let Y := Yc b
  let cap := cap b
  let L := l * Y
  let halfU := L * X
  let U := 2 * halfU
  let V := 4 * g * w * Y
  let W := b * w
  let uv := halfU * V
  let halfA := halfU + uv
  let A := 2 * halfA
  let B1 := 2 * X + 1
  let C := 6 * c0 - 1
  let Phalf := U * uv
  let K := X + 1 + k2 * (Phalf - 1)
  let S := 2 * A - 5
  let T := 3 * W * C - 2 * (W * W - 1)
  let Q := (Phalf * Phalf - 1) * (K * K) + 1
  let Delta := g * (cap - g) * (K * K) - cap * cap * ((C - K * L) * (C - K * L))
  let xi := z * xx
  let D := (A * A - 4) * (C * C) + 4
  let E0 := C * C * xi
  let E := D * E0
  let E2 := E0 * E
  let F := 4 * (A * A - 4) * E2 + 1
  let G := (halfA - 1) * (F - 1) - 1
  let Omega := 16 * E
  let H := C + F * (B1 - C + Omega * y)
  let I := (G * G - 1) * (H * H) + 1
  let rho := T + S * y
  let Sigma := xi * S ^ 5
  let Theta := (rho ^ 3 - rho * S ^ 2 - S ^ 3) * (rho ^ 2 + 23 * S ^ 2)
  let r := b * Q
  let a0 := r + (9 * Delta - 3) * (r * z) ^ 2
  let a1 := D * F * I
  { b := b, g := g, k2 := k2, X := X, Y := Y, cap := cap, L := L, halfU := halfU, U := U, V := V,
    W := W, uv := uv, halfA := halfA, A := A, B1 := B1, C := C, Phalf := Phalf, K := K, S := S,
    T := T, Q := Q, Delta := Delta, xi := xi, D := D, E0 := E0, E := E, E2 := E2, F := F, G := G,
    Omega := Omega, H := H, I := I, rho := rho, Sigma := Sigma, Theta := Theta, r := r, a0 := a0,
    a1 := a1 }

/-- The registers of an assignment; the last unknown `x 9` is not read. -/
def regs (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : Regs 𝔸 :=
  regs9 p (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

/-- The two-root norm at the linear slot `μ`. -/
def out (R : Regs 𝔸) (μ : 𝔸) : 𝔸 := N9Norm.norm2 (R.Sigma * μ - R.Theta) R.Sigma R.a0 R.a1

/-- The value of the 467-operation polar circuit. -/
def value (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : 𝔸 := out (regs p x) (x 9)

/-- The shear of the linear form, `2 A E · G H`. -/
def shearLin (R : Regs 𝔸) (_y : 𝔸) : 𝔸 := R.G * R.H * (2 * R.A * R.E)

/-- The shear of the cubic form, `2 A E0 (D − 2C²) · G H`. -/
def shearCub (R : Regs 𝔸) (_y : 𝔸) : 𝔸 :=
  R.G * R.H * ((R.D - 2 * (R.C * R.C)) * (2 * R.A * R.E0))

/-- The first quadratic of the six-term shear, `6 + C² (2h² − 11)`. -/
def sixA (R : Regs 𝔸) : 𝔸 := 6 + R.C * R.C * (2 * (R.halfA * R.halfA) - 11)

/-- The second quadratic of the six-term shear. -/
def sixB (R : Regs 𝔸) : 𝔸 :=
  48 + ((8 * R.halfA ^ 4 - 52 * (R.halfA * R.halfA) + 143) * (R.C * R.C) ^ 2 +
    R.C * R.C * (32 * (R.halfA * R.halfA) - 176))

/-- The six-term bracket. -/
def sixT (R : Regs 𝔸) (y : 𝔸) : 𝔸 :=
  3 * y + (sixA R * (R.xi * (R.B1 - R.C)) + sixB R * (y * (R.xi * (R.E0 * R.Omega))))

/-- The shear of the six-term form. -/
def shearSix (R : Regs 𝔸) (y : 𝔸) : 𝔸 :=
  ((R.halfA - 1) * sixT R y - 2 * y) * (R.halfA ^ 9 * (R.E0 ^ 4 * (32768 * (R.C * R.C) ^ 3)))

/-- The value of a variant circuit with shear `σ`. -/
def valueS (σ : Regs 𝔸 → 𝔸 → 𝔸) (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : 𝔸 :=
  out (regs p x) (x 9 + σ (regs p x) (x 7))

/-- The value of the 470-operation linear circuit. -/
abbrev valueLin (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : 𝔸 := valueS shearLin p x
/-- The value of the 473-operation cubic circuit. -/
abbrev valueCub (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : 𝔸 := valueS shearCub p x
/-- The value of the 507-operation six-term circuit. -/
abbrev valueSix (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) : 𝔸 := valueS shearSix p x

/-! ## The variants are translates of polar -/

/-- The registers do not read the last unknown. -/
theorem regs_congr (p : Fin 4 → 𝔸) {x x' : Fin 10 → 𝔸} (h : ∀ i, i ≠ 9 → x i = x' i) :
    regs p x = regs p x' := by
  unfold regs
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]

theorem regs_update (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸) (μ : 𝔸) :
    regs p (Function.update x 9 μ) = regs p x :=
  regs_congr p fun _ hi => Function.update_of_ne hi μ x

/-- **A variant has a zero exactly when polar has one**: the substitution `m ↦ m + σ` is a
bijection of assignments, because `σ` does not read `m`. -/
theorem exists_shift (σ : Regs 𝔸 → 𝔸 → 𝔸) (p : Fin 4 → 𝔸) :
    (∃ x, valueS σ p x = 0) ↔ ∃ x, value p x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x 9 (x 9 + σ (regs p x) (x 7)), ?_⟩
    rw [value, regs_update, Function.update_self]
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x 9 (x 9 - σ (regs p x) (x 7)), ?_⟩
    rw [valueS, regs_update, Function.update_self,
      Function.update_of_ne (by decide : (7 : Fin 10) ≠ 9), sub_add_cancel]
    exact hx

/-! ## Register equations (by `rfl`) -/

section Defs
variable (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸)
local notation "𝓡" => regs p x

theorem b_def : (𝓡).b = 6 * x 0 + 4 := rfl
theorem g_def : (𝓡).g = (𝓡).b * x 1 := rfl
theorem k2_def : (𝓡).k2 = (𝓡).b * (6 * x 3 + 4) := rfl
theorem X_def : (𝓡).X = Xc p (𝓡).b (𝓡).g := rfl
theorem Y_def : (𝓡).Y = Yc (𝓡).b := rfl
theorem cap_def : (𝓡).cap = cap (𝓡).b := rfl
theorem L_def : (𝓡).L = x 4 * (𝓡).Y := rfl
theorem halfU_def : (𝓡).halfU = (𝓡).L * (𝓡).X := rfl
theorem U_def : (𝓡).U = 2 * (𝓡).halfU := rfl
theorem V_def : (𝓡).V = 4 * (𝓡).g * x 5 * (𝓡).Y := rfl
theorem W_def : (𝓡).W = (𝓡).b * x 5 := rfl
theorem uv_def : (𝓡).uv = (𝓡).halfU * (𝓡).V := rfl
theorem halfA_def : (𝓡).halfA = (𝓡).halfU + (𝓡).uv := rfl
theorem A_def : (𝓡).A = 2 * (𝓡).halfA := rfl
theorem B1_def : (𝓡).B1 = 2 * (𝓡).X + 1 := rfl
theorem C_def : (𝓡).C = 6 * x 2 - 1 := rfl
theorem Phalf_def : (𝓡).Phalf = (𝓡).U * (𝓡).uv := rfl
theorem K_def : (𝓡).K = (𝓡).X + 1 + (𝓡).k2 * ((𝓡).Phalf - 1) := rfl
theorem S_def : (𝓡).S = 2 * (𝓡).A - 5 := rfl
theorem T_def : (𝓡).T = 3 * (𝓡).W * (𝓡).C - 2 * ((𝓡).W * (𝓡).W - 1) := rfl
theorem Q_def : (𝓡).Q = ((𝓡).Phalf * (𝓡).Phalf - 1) * ((𝓡).K * (𝓡).K) + 1 := rfl
theorem Delta_def : (𝓡).Delta = (𝓡).g * ((𝓡).cap - (𝓡).g) * ((𝓡).K * (𝓡).K) -
    (𝓡).cap * (𝓡).cap * (((𝓡).C - (𝓡).K * (𝓡).L) * ((𝓡).C - (𝓡).K * (𝓡).L)) := rfl
theorem xi_def : (𝓡).xi = x 8 * x 6 := rfl
theorem D_def : (𝓡).D = ((𝓡).A * (𝓡).A - 4) * ((𝓡).C * (𝓡).C) + 4 := rfl
theorem E0_def : (𝓡).E0 = (𝓡).C * (𝓡).C * (𝓡).xi := rfl
theorem E_def : (𝓡).E = (𝓡).D * (𝓡).E0 := rfl
theorem E2_def : (𝓡).E2 = (𝓡).E0 * (𝓡).E := rfl
theorem F_def : (𝓡).F = 4 * ((𝓡).A * (𝓡).A - 4) * (𝓡).E2 + 1 := rfl
theorem G_def : (𝓡).G = ((𝓡).halfA - 1) * ((𝓡).F - 1) - 1 := rfl
theorem Omega_def : (𝓡).Omega = 16 * (𝓡).E := rfl
theorem H_def : (𝓡).H = (𝓡).C + (𝓡).F * ((𝓡).B1 - (𝓡).C + (𝓡).Omega * x 7) := rfl
theorem I_def : (𝓡).I = ((𝓡).G * (𝓡).G - 1) * ((𝓡).H * (𝓡).H) + 1 := rfl
theorem rho_def : (𝓡).rho = (𝓡).T + (𝓡).S * x 7 := rfl
theorem Sigma_def : (𝓡).Sigma = (𝓡).xi * (𝓡).S ^ 5 := rfl
theorem Theta_def : (𝓡).Theta =
    ((𝓡).rho ^ 3 - (𝓡).rho * (𝓡).S ^ 2 - (𝓡).S ^ 3) * ((𝓡).rho ^ 2 + 23 * (𝓡).S ^ 2) := rfl
theorem r_def : (𝓡).r = (𝓡).b * (𝓡).Q := rfl
theorem a0_def : (𝓡).a0 = (𝓡).r + (9 * (𝓡).Delta - 3) * ((𝓡).r * x 8) ^ 2 := rfl
theorem a1_def : (𝓡).a1 = (𝓡).D * (𝓡).F * (𝓡).I := rfl
theorem value_def :
    value p x = N9Norm.norm2 ((𝓡).Sigma * x 9 - (𝓡).Theta) (𝓡).Sigma (𝓡).a0 (𝓡).a1 := rfl

end Defs

end Generic

end DiophantineConsistency.Z10Regs

#print axioms DiophantineConsistency.Z10Regs.exists_shift
