import IPRADerivations.Probability.Variance
import IPRADerivations.Probability.FiniteLaws
import IPRADerivations.Core.LinearCombination

/-!
# Strip budgets and cyclotomic norms for the intrinsic diameters of the Platonic solids

Packet: `geometry/platonic_surface_diameters_2026-11-19` (intrinsic diameters of the tetrahedron, octahedron,
icosahedron and dodecahedron). Imported from the packet's `lean/IntrinsicIPRA.lean` (object-language
derivations written against this library), adapted to the library's namespace: the six octahedral strip
lengths and their budget (`octSixStrips`, `stripBudget`, `octMinimum`: the least strip has squared length at
most `3`, so the octahedral diameter is `√3`), the two-weight variance identity, the natural form of twice a
triangular norm (`twiceSq_correct`), the minimum of six (`sixMinimum`), and the cyclotomic norm identities
in `ℤ[ζ₅]` (`cyclNorm`, `cyclNormMultiplicative`) used for `φ`.
-/

namespace LeanProofs.IPRA.Geometry.PlatonicSurface

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev z (u : PTm n) : ZT n := ZT.ofNat u

/-- The triangular-lattice norm squared in the object language. -/
def triQ (x y : ZT n) : ZT n := x*x + x*y + y*y

/-- Homogeneous squared distance in the strip flipping axes in the order 1,2,3.
The source and target barycentric triples have integer masses of total A and B.
Multiplying the displacement by AB clears both denominators. -/
def strip (a b c d e f : PTm n) : ZT n :=
  let A := a+b+c
  let B := d+e+f
  triQ (z (A*(d+f)) - z (B*b)) (z (A*(d+e+f+e+f)) - z (B*c))

def mixed (a b c : PTm n) : PTm n := a*b + a*c + b*c

/-- The six actual developed squared lengths sum to the stated constant minus
the two barycentric variance deficits. This is a syntactic iPRA derivation. -/
theorem octSixStrips (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
       (strip a b c d e f + strip a c b d f e +
        strip b a c e d f + strip b c a e f d +
        strip c a b f d e + strip c b a f e d +
        z ((num 6) * ((d+e+f)*(d+e+f)*mixed a b c +
                       (a+b+c)*(a+b+c)*mixed d e f)))
       (z ((num 18) * ((a+b+c)*(a+b+c)*((d+e+f)*(d+e+f))))) := by
  unfold strip triQ mixed z
  ipra_ring

/-- The two-weight Jensen identity for the non-orthogonal triangular norm.
It also applies to real approximants after clearing denominators. -/
theorem twoWeightVariance (a b : PTm n) (x y u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (triQ (z a*x + z b*u) (z a*y + z b*v) +
       z (a*b)*triQ (x-u) (y-v))
      (z (a+b)*(z a*triQ x y + z b*triQ u v)) := by
  unfold triQ z
  ipra_ring

open LeanProofs.IPRA.Probability.Variance (ad ad_sq)

def sqGap (x y : PTm n) : PTm n := ad x y * ad x y

/-- Twice the squared norm of (x-u,y-v), in natural-number syntax. -/
def twiceSq (x y u v : PTm n) : PTm n :=
  sqGap x u + sqGap y v + sqGap (x+y) (u+v)

theorem twiceSq_correct (x y u v : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (z (twiceSq x y u v))
      (z (num 2) * triQ (z x-z u) (z y-z v)) := by
  unfold twiceSq sqGap triQ z
  ipra_lc natEq (ad_sq (Γ := Γ) x u) + natEq (ad_sq (Γ := Γ) y v) + natEq (ad_sq (Γ := Γ) (x+y) (u+v))

def stripNat (a b c d e f : PTm n) : PTm n :=
  let A := a+b+c
  let B := d+e+f
  twiceSq (A*(d+f)) (A*(d+e+f+e+f)) (B*b) (B*c)

theorem stripNat_correct (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (z (stripNat a b c d e f)) (z (num 2) * strip a b c d e f) :=
  twiceSq_correct _ _ _ _

def clearance (a b c d e f : PTm n) : PTm n :=
  ((a+b+c)*(a+b+c))*((d+e+f)*(d+e+f))

/-- Twice the sum of squared lengths, cleared to a natural number, is at most
36 times the common squared denominator. The explicitly supplied nonnegative
slack is twice the two variance terms in the signed identity. -/
theorem stripBudget (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] le
      (stripNat a b c d e f + stripNat a c b d f e +
       stripNat b a c e d f + stripNat b c a e f d +
       stripNat c a b f d e + stripNat c b a f e d)
      (num 36 * clearance a b c d e f) := by
  refine le_of_eq_add (d := num 12 * ((d+e+f)*(d+e+f)*mixed a b c +
                                      (a+b+c)*(a+b+c)*mixed d e f)) ?_
  unfold clearance
  ipra_lc -2*ZT.toZ_eq (octSixStrips (Γ := Γ) a b c d e f) - ZT.toZ_eq (stripNat_correct (Γ := Γ) a b c d e f) -
    ZT.toZ_eq (stripNat_correct (Γ := Γ) a c b d f e) - ZT.toZ_eq (stripNat_correct (Γ := Γ) b a c e d f) -
    ZT.toZ_eq (stripNat_correct (Γ := Γ) b c a e f d) - ZT.toZ_eq (stripNat_correct (Γ := Γ) c a b f d e) -
    ZT.toZ_eq (stripNat_correct (Γ := Γ) c b a f e d)

/-- A four-coefficient cyclotomic integer in the basis 1,ζ,ζ²,ζ³. -/
structure Cycl (n : ℕ) where
  a : ZT n
  b : ZT n
  c : ZT n
  d : ZT n

/-- Convolution modulo 1+ζ+ζ²+ζ³+ζ⁴. Here ζ⁵=1 and ζ⁶=ζ. -/
def cyclMul (p q : Cycl n) : Cycl n :=
  let h₄ := p.b*q.d + p.c*q.c + p.d*q.b
  ⟨p.a*q.a-h₄ + p.c*q.d + p.d*q.c,
   p.a*q.b+p.b*q.a-h₄ + p.d*q.d,
   p.a*q.c+p.b*q.b+p.c*q.a-h₄,
   p.a*q.d+p.b*q.c+p.c*q.b+p.d*q.a-h₄⟩

def conj (p : Cycl n) : Cycl n :=
  ⟨p.a - p.b, -p.b, p.d-p.b, p.c-p.b⟩

def adjSum (p : Cycl n) : ZT n := p.a*p.b+p.b*p.c+p.c*p.d

def normA (p : Cycl n) : ZT n :=
  p.a*p.a+p.b*p.b+p.c*p.c+p.d*p.d - adjSum p

def normB (p : Cycl n) : ZT n :=
  adjSum p - (p.a*p.c+p.b*p.d+p.a*p.d)

/-- In the real subring, (A,0,-B,-B) represents A+Bφ, since
ζ²+ζ³=-φ. This derivation checks every component of p times its conjugate. -/
theorem cyclNorm (p : Cycl n) :
    Γ ⊢[PRAAx]
      ZT.eq (cyclMul p (conj p)).a (normA p) ⋏
      (ZT.eq (cyclMul p (conj p)).b (ZT.natLit 0) ⋏
       (ZT.eq (cyclMul p (conj p)).c (-(normB p)) ⋏
        ZT.eq (cyclMul p (conj p)).d (-(normB p)))) := by
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  all_goals
    simp only [cyclMul, conj, normA, normB, adjSum]
    ipra_ring

/-- Multiplicativity in the real basis (1,φ), including the φ²=1+φ carry. -/
theorem cyclNormMultiplicative (p q : Cycl n) :
    Γ ⊢[PRAAx]
      ZT.eq (normA (cyclMul p q)) (normA p*normA q + normB p*normB q) ⋏
      ZT.eq (normB (cyclMul p q))
        (normA p*normB q + normB p*normA q + normB p*normB q) := by
  refine .andI ?_ ?_
  all_goals
    simp only [cyclMul, normA, normB, adjSum]
    ipra_ring

open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Probability.FiniteLaws (min_le_left min_le_right)

def least (a b : PTm n) : PTm n := monus a (monus a b)

def leastSix (a b c d e f : PTm n) : PTm n :=
  least (least (least a b) c) (least (least d e) f)

theorem sixMinimum (a b c d e f t : PTm n)
    (budget : Γ ⊢[PRAAx] le (a+b+c+d+e+f) (num 36*t)) :
    Γ ⊢[PRAAx] le (leastSix a b c d e f) (num 6*t) := by
  let l := least (least a b) c
  let r := least (least d e) f
  let m := least l r
  have hl : Γ ⊢[PRAAx] le m l := min_le_left l r
  have hr : Γ ⊢[PRAAx] le m r := min_le_right l r
  have hab := le_trans hl (min_le_left (least a b) c)
  have hde := le_trans hr (min_le_left (least d e) f)
  have ha := le_trans hab (min_le_left a b)
  have hb := le_trans hab (min_le_right a b)
  have hc := le_trans hl (min_le_right (least a b) c)
  have hd := le_trans hde (min_le_left d e)
  have he := le_trans hde (min_le_right d e)
  have hf := le_trans hr (min_le_right (least d e) f)
  have hs := le_trans (add_le_add₂ (add_le_add₂ (add_le_add₂
                (add_le_add₂ (add_le_add₂ ha hb) hc) hd) he) hf) budget
  change Γ ⊢[PRAAx] le m (num 6*t)
  apply mul_le_cancel (d' := num 5)
  refine le_congr ?_ ?_ hs <;> ipra_ring

/-- For independent barycentric triples with positive masses A,B, the least
twice-squared cleared strip length is at most 6A²B². Dividing by 2A²B² gives
the geometric squared-diameter bound 3. The object formula also handles A=0
or B=0 harmlessly. -/
theorem octMinimum (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] le
      (leastSix (stripNat a b c d e f) (stripNat a c b d f e)
        (stripNat b a c e d f) (stripNat b c a e f d)
        (stripNat c a b f d e) (stripNat c b a f e d))
      (num 6 * clearance a b c d e f) :=
  sixMinimum _ _ _ _ _ _ _ (stripBudget a b c d e f)

end LeanProofs.IPRA.Geometry.PlatonicSurface
