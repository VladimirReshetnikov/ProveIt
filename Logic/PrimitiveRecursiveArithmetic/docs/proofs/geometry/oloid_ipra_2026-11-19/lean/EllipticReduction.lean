import IPRADerivations.Core.PolynomialImplications

/-!
# Three exact differentials, with all denominators cleared

Use Q = x/d for the rational argument q in the report. Write g=P/(s q^j),
R=F/(s q^j) and the target constant plus linear term as (k+e q)/b.
For polynomials of degree at most j, the row xP' below is the homogeneous
numerator of q P'(q). The displayed target is homogeneous of degree j+2.
The hypotheses list is empty. Positive d and q justify recovering the
rational identity when passing to the finite Riemann sums.
-/
namespace Oloid.Reduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "x" => (ZExp.var 0 : ZExp 2)
local notation "d" => (ZExp.var 1 : ZExp 2)

/-- Numerator representing 3 s q^j times the exact-differential operator
applied to P/(s q^j), homogenized to total degree j+2. -/
def differential (j : ZExp 2) (P xP' : ZExp 2) : ZExp 2 :=
  (12 * x ^ 2 - 10 * x * d + d ^ 2) * P +
  2 * (x - d) * (4 * x - d) * (xP' - j * P)

def volumeF : ZExp 2 :=
  -(d ^ 4) + 4 * x * d ^ 3

def volumeP : ZExp 2 :=
  d ^ 2 - 2 * x * d

def volumeD : ZExp 2 :=
  -(2 * x * d)

theorem volume_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (3 * (3 * volumeF - differential 2 volumeP volumeD),
                3 * 2 * x ^ 2 * d * (2 * d + 4 * x))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [differential, volumeF, volumeP, volumeD]
    ring)

def axialF : ZExp 2 :=
  7 * d ^ 6 - 60 * x * d ^ 5 + 144 * x ^ 2 * d ^ 4 - 80 * x ^ 3 * d ^ 3 - 48 * x ^ 4 * d ^ 2 + 576 * x ^ 5 * d - 512 * x ^ 6

def axialP : ZExp 2 :=
  -(3 * d ^ 4) + 18 * x * d ^ 3 - 4 * x ^ 2 * d ^ 2 - 16 * x ^ 3 * d - 128 * x ^ 4

def axialD : ZExp 2 :=
  18 * x * d ^ 3 - 8 * x ^ 2 * d ^ 2 - 48 * x ^ 3 * d - 512 * x ^ 4

theorem axial_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (45 * (3 * axialF - differential 4 axialP axialD),
                3 * 240 * x ^ 4 * d * (32 * x - 2 * d))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [differential, axialF, axialP, axialD]
    ring)

def transverseF : ZExp 2 :=
  -(7 * d ^ 6) + 35 * x * d ^ 5 - 25 * x ^ 2 * d ^ 4 - 12 * x ^ 3 * d ^ 3 + 16 * x ^ 4 * d ^ 2 - 128 * x ^ 5 * d + 256 * x ^ 6

def transverseP : ZExp 2 :=
  3 * d ^ 4 - 3 * x * d ^ 3 - 15 * x ^ 2 * d ^ 2 - 78 * x ^ 3 * d + 64 * x ^ 4

def transverseD : ZExp 2 :=
  -(3 * x * d ^ 3) - 30 * x ^ 2 * d ^ 2 - 234 * x ^ 3 * d + 256 * x ^ 4

theorem transverse_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (90 * (3 * transverseF - differential 4 transverseP transverseD),
                3 * 120 * x ^ 4 * d * (142 * x - 19 * d))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [differential, transverseF, transverseP, transverseD]
    ring)

end Oloid.Reduction
