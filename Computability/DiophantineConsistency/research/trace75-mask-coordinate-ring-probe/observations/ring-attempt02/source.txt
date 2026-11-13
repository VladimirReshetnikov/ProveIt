import DiophantineConsistency.TenPositiveTrace75

/-! 74-row coordinate identity; positive-domain inverse is conditional. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Mask
open DiophantineConsistency.TenPositiveTrace75
variable {R : Type*} [CommRing R]

def value74 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let J : R := v 0
  let F : R := v 1
  let C : R := v 2
  let i : R := v 3
  let T : R := v 4
  let w : R := v 5
  let s : R := v 6
  let n : R := v 7
  let eta : R := v 8
  let zeta : R := v 9
  let beta : R := p 0
  let K0 : R := p 1
  let MC : R := p 2
  let MF : R := p 3
  let bJ := beta * J
  let q := bJ + 1
  let q2 := q * q
  let q3 := q2 * q
  let Y := q3 * s
  let qmF := q - F
  let X := w * q
  let k := eta + zeta
  let kY := k * Y
  let c := kY + eta
  let XY := X * Y
  let Am1 := XY + Y
  let fourAm1 := 4 * Am1
  let Hp := fourAm1 - 1
  let Ap1 := Am1 + 2
  let V0k := XY * kY
  let V0kk := V0k + k
  let V0k2 := V0k * V0kk
  let Dtau := V0k2 + 1
  let G1 := q * qmF
  let G := G1 - C
  let q2m1 := q2 - 1
  let Gq := G * q2m1
  let qMF := q * MF
  let MCqMF := MC + qMF
  let RJ := MCqMF * J
  let R := Gq + RJ
  let kR := k - R
  let e := kR - 1
  let K0w := K0 + w
  let K0wC := K0w * C
  let Bt := K0wC - F
  let c2 := c * c
  let U := i * c2
  let UE := U * Dtau
  let Delta := Am1 * Ap1
  let SE := Delta * UE
  let DpI2 := SE * U
  let Df := DpI2 + 1
  let aF0 := DpI2 * Df
  let fouraF0 := 4 * aF0
  let trace_f := DpI2 + Df
  let Q := Delta * fouraF0
  let cT := c * T
  let cTR := cT - R
  let DfcTR := trace_f * cTR
  let V := DfcTR - c
  let V2 := V * V
  let P1mu2 := bJ * XY
  let LBt := V2 * Bt
  let center := n - LBt
  let Hn := Hp * center
  let threec := 3 * c
  let twoX := 2 * X
  let gap := threec - twoX
  let Kpos0 := X * gap
  let Kpos := Kpos0 + 2
  let lin := Hn + Kpos
  let Zpart1 := P1mu2 * lin
  let mu2inner := XY * Bt
  let P1e := bJ * e
  let brk := mu2inner + P1e
  let Zpart2 := Hp * brk
  let Znum := Zpart1 - Zpart2
  let Mtot := P1mu2 * Hp
  let M2 := Mtot * Mtot
  let Dg := Dtau * Df
  let Z2 := Znum * Znum
  let RG := M2 * Dg
  let RGV2 := RG * V2
  let inside := Z2 - RGV2
  let Qinside := Q * inside
  let correction := RG - Z2
  let N := Qinside + correction
  N

def core (p : Fin 4 → R) (v : Fin 10 → R) (mask rankPart : R) : R :=
  let J : R := v 0
  let F : R := v 1
  let i : R := v 3
  let T : R := v 4
  let w : R := v 5
  let s : R := v 6
  let n : R := v 7
  let eta : R := v 8
  let zeta : R := v 9
  let C : R := mask
  let beta : R := p 0
  let K0 : R := p 1
  let MC : R := p 2
  let MF : R := p 3
  let bJ := beta * J
  let q := bJ + 1
  let q2 := q * q
  let q3 := q2 * q
  let Y := q3 * s
  let X := w * q
  let k := eta + zeta
  let kY := k * Y
  let c := kY + eta
  let XY := X * Y
  let Am1 := XY + Y
  let fourAm1 := 4 * Am1
  let Hp := fourAm1 - 1
  let Ap1 := Am1 + 2
  let V0k := XY * kY
  let V0kk := V0k + k
  let V0k2 := V0k * V0kk
  let Dtau := V0k2 + 1
  let G : R := rankPart
  let q2m1 := q2 - 1
  let Gq := G * q2m1
  let qMF := q * MF
  let MCqMF := MC + qMF
  let RJ := MCqMF * J
  let R := Gq + RJ
  let kR := k - R
  let e := kR - 1
  let K0w := K0 + w
  let K0wC := K0w * C
  let Bt := K0wC - F
  let c2 := c * c
  let U := i * c2
  let UE := U * Dtau
  let Delta := Am1 * Ap1
  let SE := Delta * UE
  let DpI2 := SE * U
  let Df := DpI2 + 1
  let aF0 := DpI2 * Df
  let fouraF0 := 4 * aF0
  let trace_f := DpI2 + Df
  let Q := Delta * fouraF0
  let cT := c * T
  let cTR := cT - R
  let DfcTR := trace_f * cTR
  let V := DfcTR - c
  let V2 := V * V
  let P1mu2 := bJ * XY
  let LBt := V2 * Bt
  let center := n - LBt
  let Hn := Hp * center
  let threec := 3 * c
  let twoX := 2 * X
  let gap := threec - twoX
  let Kpos0 := X * gap
  let Kpos := Kpos0 + 2
  let lin := Hn + Kpos
  let Zpart1 := P1mu2 * lin
  let mu2inner := XY * Bt
  let P1e := bJ * e
  let brk := mu2inner + P1e
  let Zpart2 := Hp * brk
  let Znum := Zpart1 - Zpart2
  let Mtot := P1mu2 * Hp
  let M2 := Mtot * Mtot
  let Dg := Dtau * Df
  let Z2 := Znum * Znum
  let RG := M2 * Dg
  let RGV2 := RG * V2
  let inside := Z2 - RGV2
  let Qinside := Q * inside
  let correction := RG - Z2
  let N := Qinside + correction
  N

def oldVal (p : Fin 4 → R) (v : Fin 10 → R) : Fin 10 → R :=
  fun i => if i = 2 then (p 0 * v 0 + 1) - v 1 - v 2 else v i

theorem coordinate_identity (p : Fin 4 → R) (v : Fin 10 → R) :
    value74 p v = value75 p (oldVal p v) := by
  change core p v (v 2) ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) - v 1) - v 2) =
    core p v ((p 0 * v 0 + 1) - v 1 - ((p 0 * v 0 + 1) - v 1 - v 2))
      (p 0 * v 0 * ((p 0 * v 0 + 1) - v 1) + ((p 0 * v 0 + 1) - v 1 - v 2))
  congr 1 <;> ring

#print axioms coordinate_identity
end Trace74Mask
