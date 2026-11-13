import Mathlib.Data.Nat.GCD.Basic
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Trace74ScaledCertificate
def modulus : Nat := 17179869183
def coeffL : Nat := 4325377
def coeffD : Nat := 8651841
def step (xy : Nat × Nat) (bit : Bool) : Nat × Nat :=
  let A := (xy.1*xy.1 + coeffD*xy.2*xy.2) % modulus
  let C := (2*xy.1*xy.2) % modulus
  if bit then ((coeffL*A+coeffD*C)%modulus, (A+coeffL*C)%modulus) else (A,C)
def state00 : Nat × Nat := (1, 0)
def state01 : Nat × Nat := (4325377, 1)
def state02 : Nat × Nat := (17303683, 8650754)
def state03 : Nat × Nat := (11447526532, 9595710842)
def state04 : Nat × Nat := (7001484310, 10453645178)
def state05 : Nat × Nat := (5226465991, 11255274802)
def state06 : Nat × Nat := (12340690846, 6164241228)
def state07 : Nat × Nat := (13376039500, 15845335087)
def state08 : Nat × Nat := (6888687724, 4432429370)
def state09 : Nat × Nat := (14160306265, 4648027279)
def state10 : Nat × Nat := (15812109460, 3510813839)
def state11 : Nat × Nat := (128091646, 6752477597)
def state12 : Nat × Nat := (12460012087, 10735696076)
def state13 : Nat × Nat := (7670847085, 3959609440)
def state14 : Nat × Nat := (15454767280, 9800976647)
def state15 : Nat × Nat := (14322596407, 16487733097)
def state16 : Nat × Nat := (13157075296, 9313205390)
def state17 : Nat × Nat := (2052296653, 12291592535)
def state18 : Nat × Nat := (15302349913, 7044798806)
def state19 : Nat × Nat := (13428337519, 7932138748)
def state20 : Nat × Nat := (1332088726, 10392094475)
def state21 : Nat × Nat := (15237034687, 15615767228)
def state22 : Nat × Nat := (14576304868, 11579895833)
def state23 : Nat × Nat := (2416500748, 5822647609)
def state24 : Nat × Nat := (2989424461, 14322702632)
def state25 : Nat × Nat := (16685968420, 9350443669)
def state26 : Nat × Nat := (17130673774, 15121319883)
def state27 : Nat × Nat := (17110521043, 6909441972)
def state28 : Nat × Nat := (3242235013, 4707432868)
def state29 : Nat × Nat := (10976842318, 13658773757)
def state30 : Nat × Nat := (14044053805, 6601038355)
def state31 : Nat × Nat := (14662520056, 13290181496)
def state32 : Nat × Nat := (6867570283, 1242386546)
theorem transition00 : step state00 true = state01 := by decide
theorem transition01 : step state01 false = state02 := by decide
theorem transition02 : step state02 true = state03 := by decide
theorem transition03 : step state03 true = state04 := by decide
theorem transition04 : step state04 false = state05 := by decide
theorem transition05 : step state05 true = state06 := by decide
theorem transition06 : step state06 true = state07 := by decide
theorem transition07 : step state07 false = state08 := by decide
theorem transition08 : step state08 false = state09 := by decide
theorem transition09 : step state09 false = state10 := by decide
theorem transition10 : step state10 true = state11 := by decide
theorem transition11 : step state11 true = state12 := by decide
theorem transition12 : step state12 false = state13 := by decide
theorem transition13 : step state13 false = state14 := by decide
theorem transition14 : step state14 false = state15 := by decide
theorem transition15 : step state15 false = state16 := by decide
theorem transition16 : step state16 true = state17 := by decide
theorem transition17 : step state17 true = state18 := by decide
theorem transition18 : step state18 false = state19 := by decide
theorem transition19 : step state19 false = state20 := by decide
theorem transition20 : step state20 true = state21 := by decide
theorem transition21 : step state21 true = state22 := by decide
theorem transition22 : step state22 false = state23 := by decide
theorem transition23 : step state23 false = state24 := by decide
theorem transition24 : step state24 false = state25 := by decide
theorem transition25 : step state25 true = state26 := by decide
theorem transition26 : step state26 false = state27 := by decide
theorem transition27 : step state27 true = state28 := by decide
theorem transition28 : step state28 false = state29 := by decide
theorem transition29 : step state29 false = state30 := by decide
theorem transition30 : step state30 false = state31 := by decide
theorem transition31 : step state31 true = state32 := by decide
def bezoutS : Nat := 4508969228
def bezoutT : Nat := 326072489
theorem bezout : bezoutS*state32.2 = bezoutT*modulus+1 := by decide
theorem coprime : Nat.Coprime state32.2 modulus := by
  have h₁ : Nat.gcd state32.2 modulus ∣ bezoutS*state32.2 :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) bezoutS
  have h₂ : Nat.gcd state32.2 modulus ∣ bezoutT*modulus :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) bezoutT
  have h₃ : Nat.gcd state32.2 modulus ∣ 1 := by
    have h := Nat.dvd_sub h₁ h₂
    simpa only [bezout,Nat.add_sub_cancel_left] using h
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h₃)
#print axioms Trace74ScaledCertificate.transition00
#print axioms Trace74ScaledCertificate.transition31
#print axioms Trace74ScaledCertificate.bezout
#print axioms Trace74ScaledCertificate.coprime
end Trace74ScaledCertificate
