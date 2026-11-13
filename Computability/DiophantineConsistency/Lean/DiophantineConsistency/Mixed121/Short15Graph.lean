import DiophantineConsistency.Mixed121.P55Graph

/-! # The fifteen-positive forms on 121x8801: shared registers and residuals

Packages 59 (`p69_d91`, `p67_d125`, `p68_d101`), 56 (`Q54`, `Q46`) and 47
(`gap_minima75`) use one coordinate order, package 55's with `h` inserted:

`0 J, 1 F, 2 α, 3 z, 4 f, 5 h, 6 i, 7 T, 8 s, 9 w, 10 τ|r, 11 η, 12 ζ, 13 y|e, 14 γ`.

With `q = βJ + 1`, `X = wq`, `Y = sq³`, `E = XY`, `k = η + ζ`, `c = kY + η`,
`a = E + Y`, `H = 4a + 3`, `Δ = a² + H`, `ℓ = E·kY`,
`R = ((q−1)(q−F) + α)(q²−1) + (MC + q·MF)J` and `D = X + ac + γH`, the
residuals are:

* `N0 = τ² − ℓ(ℓ + k)`, the first norm;
* `N1 = D² − Δc²`, the main norm (its root is `D` itself);
* `Nk = k − hE − R`, the explicit index multiplier;
* `Nt = (K0 + w)C + (q − F) − z(q − 1)` with `C = q − F − α`, the transport;
* `S = (ic²)² − Aaux` with `Aaux = Δ(f² − 1)`, the ordinary strong norm;
* `Na = Aaux(V² − y²) + y²`, the auxiliary norm, for the squared-modulus
  ordinate `Vn = f²(cT − R) − c` or the old ordinate `Vo = c(Tf − 1) − Rf²`.

The per-equation graph modules prove that their literal gates evaluate to these
functions. Everything here is over an arbitrary commutative ring. -/
set_option autoImplicit false
noncomputable section
namespace Short15Graph
open DiophantineConsistency AdaptiveEquationSyntax2011

/-- The six residuals and the output of a fifteen-positive literal graph. -/
structure Graph where
  N0 : Expr (Fin 15)
  N1 : Expr (Fin 15)
  Na : Expr (Fin 15)
  Nk : Expr (Fin 15)
  Nt : Expr (Fin 15)
  Ns : Expr (Fin 15)
  output : Expr (Fin 15)

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values. -/
structure Vals (R : Type*) where
  qm : R
  q : R
  X : R
  Y : R
  E : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  ell : R
  qF : R
  C : R
  RR : R
  D : R
  Aaux : R
  Vn : R
  Vo : R

def vals (p : Fin 4 → ℤ) (w : Fin 15 → R) : Vals R :=
  let qm := (p 0 : R) * w 0
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let X := w 9 * q
  let Y := w 8 * q3
  let E := X * Y
  let k := w 11 + w 12
  let kY := k * Y
  let ell := E * kY
  let c := kY + w 11
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let qF := q - w 1
  let C := qF - w 2
  let RR := (qm * qF + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0
  let D := X + a * c + w 14 * H
  let Aaux := Delta * (w 4 * w 4 - 1)
  let Vn := (w 4 * w 4) * (c * w 7 - RR) - c
  let Vo := c * (w 7 * w 4 - 1) - RR * (w 4 * w 4)
  ⟨qm, q, X, Y, E, k, c, a, H, Delta, ell, qF, C, RR, D, Aaux, Vn, Vo⟩

/-- The first norm, at a root `τ`. -/
def rN0 (p : Fin 4 → ℤ) (w : Fin 15 → R) (τ : R) : R :=
  τ * τ - (vals p w).ell * ((vals p w).ell + (vals p w).k)

/-- The main norm. -/
def rN1 (p : Fin 4 → ℤ) (w : Fin 15 → R) : R :=
  (vals p w).D * (vals p w).D - (vals p w).Delta * ((vals p w).c * (vals p w).c)

/-- The index residual. -/
def rNk (p : Fin 4 → ℤ) (w : Fin 15 → R) : R :=
  ((vals p w).k - w 5 * (vals p w).E) - (vals p w).RR

/-- The transport residual. -/
def rNt (p : Fin 4 → ℤ) (w : Fin 15 → R) : R :=
  (((p 1 : R) + w 9) * (vals p w).C + (vals p w).qF) - w 3 * (vals p w).qm

/-- The ordinary strong residual, at an index `i`. -/
def rS (p : Fin 4 → ℤ) (w : Fin 15 → R) (i : R) : R :=
  (i * ((vals p w).c * (vals p w).c)) * (i * ((vals p w).c * (vals p w).c)) - (vals p w).Aaux

/-- The auxiliary norm at ordinate `V` and partner `y`. -/
def rNa (A V y : R) : R := A * (V * V - y * y) + y * y

/-! ## Gap and pullback identities -/

/-- The first gap: `r² + ℓ(2r − k) = (ℓ + r)² − ℓ(ℓ + k)`. -/
theorem first_gap (p : Fin 4 → ℤ) (w : Fin 15 → R) (r : R) :
    r * r + (vals p w).ell * (2 * r - (vals p w).k) = rN0 p w ((vals p w).ell + r) := by
  unfold rN0; ring

/-- The auxiliary gap: `(V + u)² − A·u(V + (V + u)) = A(V² − (V + u)²) + (V + u)²`. -/
theorem aux_gap (A V u : R) :
    (V + u) * (V + u) - A * (u * (V + (V + u))) = rNa A V (V + u) := by
  unfold rNa; ring

/-- The old ordinate at `fT` is the squared-modulus ordinate at `T`. -/
theorem old_new (c Rr f T : R) :
    c * ((f * T) * f - 1) - Rr * (f * f) = (f * f) * (c * T - Rr) - c := by ring

/-- The scaled strong norm of package 59's p67 is `Δ` times the normalized one. -/
theorem scaled_strong (Δ f i c2 : R) :
    Δ * (f * f) - (i * (Δ * c2)) * (i * (Δ * c2)) = Δ * (f * f - Δ * ((i * c2) * (i * c2))) := by
  ring

end Ring

end Short15Graph

#print axioms Short15Graph.first_gap
#print axioms Short15Graph.aux_gap
#print axioms Short15Graph.old_new
#print axioms Short15Graph.scaled_strong
