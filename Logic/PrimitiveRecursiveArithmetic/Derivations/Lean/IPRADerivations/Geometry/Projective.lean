import IPRADerivations.Core.LinearAlgebra

/-!
# Projective incidence identities (`desargues_pascal_ipra`, `eight_geometry_theorems_ipra`)

Points and lines of the projective plane are integer 3-vectors, the line
through two points is their cross product, and `[u v w] = u · (v × w)`. The
packets reduce Desargues', Pappus's and Pascal's theorems to polynomial
identities; the following are derived in iPRA:

* the double cross identity `(u × v) × (r × s) = [u v s] r − [u v r] s`
  (`desargues_pascal_ipra/sections/03_geometry.tex`);
* the universal Desargues identity `[X Y Z] = [a b c] [A B C] [a×A, b×B, c×C]`
  for `X = (a×b)×(A×B)`, `Y = (b×c)×(B×C)`, `Z = (c×a)×(C×A)`
  (`sections/04_desargues.tex`), proved as in the packet: by the double cross
  identity, multilinearity, and the product of the determinants;
* the Plücker relation `[r s t][r u v] − [r s u][r t v] + [r s v][r t u] = 0`
  (`sections/05_pascal.tex`);
* the Pappus identity `X − Y + Z = 0` for the three intersection points of the
  hexagon (`eight_geometry_theorems_ipra/sections/09_pappus_hexagon.tex`).
-/

namespace LeanProofs.IPRA.Geometry.Projective

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

/-! ## Identities over an arbitrary commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

theorem doubleCross (u v r s : Fin 3 → R) :
    (u ⨯₃ v) ⨯₃ (r ⨯₃ s) = (u ⬝ᵥ (v ⨯₃ s)) • r - (u ⬝ᵥ (v ⨯₃ r)) • s := by
  ext i
  fin_cases i <;> simp [crossProduct, dotProduct, Fin.sum_univ_three] <;> ring

private theorem trilinear (s₁ s₂ s₃ s₄ s₅ s₆ : R) (A B C : Fin 3 → R) :
    (s₁ • A - s₂ • B) ⬝ᵥ ((s₃ • B - s₄ • C) ⨯₃ (s₅ • C - s₆ • A))
      = (s₁ * s₃ * s₅ - s₂ * s₄ * s₆) * (A ⬝ᵥ (B ⨯₃ C)) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]
  ring

private theorem desarguesE (a b c A B C : Fin 3 → R) :
    (a ⬝ᵥ (b ⨯₃ B)) * (b ⬝ᵥ (c ⨯₃ C)) * (c ⬝ᵥ (a ⨯₃ A))
        - (a ⬝ᵥ (b ⨯₃ A)) * (b ⬝ᵥ (c ⨯₃ B)) * (c ⬝ᵥ (a ⨯₃ C))
      = (a ⬝ᵥ (b ⨯₃ c)) * ((a ⨯₃ A) ⬝ᵥ ((b ⨯₃ B) ⨯₃ (c ⨯₃ C))) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]
  ring

theorem desargues (a b c A B C : Fin 3 → R) :
    ((a ⨯₃ b) ⨯₃ (A ⨯₃ B)) ⬝ᵥ (((b ⨯₃ c) ⨯₃ (B ⨯₃ C)) ⨯₃ ((c ⨯₃ a) ⨯₃ (C ⨯₃ A)))
      = (a ⬝ᵥ (b ⨯₃ c)) * (A ⬝ᵥ (B ⨯₃ C)) * ((a ⨯₃ A) ⬝ᵥ ((b ⨯₃ B) ⨯₃ (c ⨯₃ C))) := by
  rw [doubleCross a b A B, doubleCross b c B C, doubleCross c a C A, trilinear,
    desarguesE]
  ring

theorem plucker (r s t u v : Fin 3 → R) :
    (r ⬝ᵥ (s ⨯₃ t)) * (r ⬝ᵥ (u ⨯₃ v)) - (r ⬝ᵥ (s ⨯₃ u)) * (r ⬝ᵥ (t ⨯₃ v))
      + (r ⬝ᵥ (s ⨯₃ v)) * (r ⬝ᵥ (t ⨯₃ u)) = 0 := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]
  ring

end Ring

/-! ## The iPRA theorems -/

section Cross

abbrev u : Vec 3 24 := Vec.vars 3 0 (by norm_num)
abbrev v : Vec 3 24 := Vec.vars 3 6 (by norm_num)
abbrev r : Vec 3 24 := Vec.vars 3 12 (by norm_num)
abbrev s : Vec 3 24 := Vec.vars 3 18 (by norm_num)

/-- `(u × v) × (r × s) = [u v s] r − [u v r] s`. -/
def doubleCrossFormula : Fm PTm 24 :=
  Vec.eqFm (Vec.cross (Vec.cross u v) (Vec.cross r s))
    (Vec.sub (Vec.smul (Vec.triple u v s) r) (Vec.smul (Vec.triple u v r) s))

theorem double_cross : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 24 doubleCrossFormula :=
  closeUniv 24 (Vec.derive (by simpa [doubleCrossFormula] using doubleCross _ _ _ _))

end Cross

section Desargues

abbrev a : Vec 3 36 := Vec.vars 3 0 (by norm_num)
abbrev b : Vec 3 36 := Vec.vars 3 6 (by norm_num)
abbrev c : Vec 3 36 := Vec.vars 3 12 (by norm_num)
abbrev A : Vec 3 36 := Vec.vars 3 18 (by norm_num)
abbrev B : Vec 3 36 := Vec.vars 3 24 (by norm_num)
abbrev C : Vec 3 36 := Vec.vars 3 30 (by norm_num)

/-- The intersection points of corresponding sides of the triangles `abc` and `ABC`. -/
def X : Vec 3 36 := Vec.cross (Vec.cross a b) (Vec.cross A B)
def Y : Vec 3 36 := Vec.cross (Vec.cross b c) (Vec.cross B C)
def Z : Vec 3 36 := Vec.cross (Vec.cross c a) (Vec.cross C A)

/-- `[X Y Z] = [a b c] [A B C] [a×A, b×B, c×C]`. -/
def desarguesFormula : Fm PTm 36 :=
  ZT.eq (Vec.triple X Y Z)
    (Vec.triple a b c * Vec.triple A B C * Vec.triple (Vec.cross a A) (Vec.cross b B) (Vec.cross c C))

/-- The universal Desargues identity: the three intersection points are
collinear (`[X Y Z] = 0`) exactly when the triangles are nondegenerate and in
perspective from a point (`[a×A, b×B, c×C] = 0`), or degenerate. -/
theorem desargues_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 36 desarguesFormula :=
  closeUniv 36 (ZT.derive (by simpa [desarguesFormula, X, Y, Z] using desargues _ _ _ _ _ _))

end Desargues

section Plucker

abbrev p₁ : Vec 3 30 := Vec.vars 3 0 (by norm_num)
abbrev p₂ : Vec 3 30 := Vec.vars 3 6 (by norm_num)
abbrev p₃ : Vec 3 30 := Vec.vars 3 12 (by norm_num)
abbrev p₄ : Vec 3 30 := Vec.vars 3 18 (by norm_num)
abbrev p₅ : Vec 3 30 := Vec.vars 3 24 (by norm_num)

/-- `[r s t][r u v] − [r s u][r t v] + [r s v][r t u] = 0`. -/
def pluckerFormula : Fm PTm 30 :=
  ZT.eq (Vec.triple p₁ p₂ p₃ * Vec.triple p₁ p₄ p₅ - Vec.triple p₁ p₂ p₄ * Vec.triple p₁ p₃ p₅
    + Vec.triple p₁ p₂ p₅ * Vec.triple p₁ p₃ p₄) (ZT.natLit 0)

theorem plucker_relation : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 30 pluckerFormula :=
  closeUniv 30 (ZT.derive (by simpa [pluckerFormula] using plucker _ _ _ _ _))

end Plucker

section Pappus

abbrev pa : ZT 12 := .var2 0 1
abbrev pb : ZT 12 := .var2 2 3
abbrev pc : ZT 12 := .var2 4 5
abbrev pd : ZT 12 := .var2 6 7
abbrev pe : ZT 12 := .var2 8 9
abbrev pf : ZT 12 := .var2 10 11

/-- The three Pappus points of the hexagon with vertices on two lines. -/
def PX : Vec 3 12 := ![pa * pd - pb * pe, pd - pe, pa - pb]
def PY : Vec 3 12 := ![pa * pd - pc * pf, pd - pf, pa - pc]
def PZ : Vec 3 12 := ![pb * pe - pc * pf, pe - pf, pb - pc]

/-- `X − Y + Z = 0`: the three points are linearly dependent, hence collinear. -/
def pappusFormula : Fm PTm 12 := Vec.eqFm (Vec.add (Vec.sub PX PY) PZ) fun _ => ZT.natLit 0

theorem pappus : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12 pappusFormula := by
  refine closeUniv 12 (Vec.derive ?_)
  funext i
  fin_cases i <;> simp [PX, PY, PZ, Vec.toZ, Vec.add, Vec.sub] <;> ring

end Pappus

end LeanProofs.IPRA.Geometry.Projective
