"""Generate the uncompiled object-iPRA polynomial certificate candidates.

This script only writes Lean source. It does not prove/typecheck that source.
Run it from any directory; output is adjacent to this script.
"""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent

header = r'''import IPRADerivations.Core.Tactic

/-!
# Analytic geometry: candidate object-iPRA polynomial certificates

STATUS: NOT TYPECHECKED IN THIS DELIVERY. No Lean executable was available.
These statements have actual `Prf PRAAx` types; they are not merely theorems
about Mathlib's real numbers. Their proofs use the repository's `ipra_ring`
reflection interface, inspected at commit
bbb85238dac533fc4b7b84a750cca864fe35fed5.

Each signed integer is a difference of two natural-number variables. Rational
versions require the separately described positive-denominator bridge. The
identities alone do not prove the classification or analytic existence results.
-/

namespace LeanProofs.IPRA.Geometry.AnalyticGeometryPacket

open LeanProofs.ConciseIPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def N2 (x y : ZT n) : ZT n := x.sq + y.sq
def D2 (x y u v : ZT n) : ZT n := x * u + y * v
def W2 (x y u v : ZT n) : ZT n := x * v - y * u
def N3 (x y z : ZT n) : ZT n := x.sq + y.sq + z.sq
def D3 (x y z u v w : ZT n) : ZT n := x*u + y*v + z*w
def Q2 (a b c x y : ZT n) : ZT n := a*x*x + b*x*y + c*y*y
def F2 (a b c d e f x y : ZT n) : ZT n := Q2 a b c x y + d*x + e*y + f

/-- Two natural variables for each signed integer; no universal evaluator. -/
def zvar {k : ℕ} (i : Fin k) : ZT (2*k) :=
  .var2 ⟨2*i.val, by omega⟩ ⟨2*i.val+1, by omega⟩

'''

# (name, arity, documentation, formula body, helper definitions to unfold,
#  conjunction count). Formulas use v : Fin arity -> ZT n.
items = [
('lagrange2',4,'Two-dimensional Lagrange identity.',
 '''(N2 (v 0) (v 1) * N2 (v 2) (v 3)).eq
    ((D2 (v 0) (v 1) (v 2) (v 3)).sq + (W2 (v 0) (v 1) (v 2) (v 3)).sq)''', ['N2','D2','W2'],1),
('parallelogram',4,'Parallelogram identity, including degenerate vectors.',
 '''(N2 (v 0+v 2) (v 1+v 3) + N2 (v 0-v 2) (v 1-v 3)).eq
    (ZT.natLit 2 * (N2 (v 0) (v 1) + N2 (v 2) (v 3)))''',['N2'],1),
('cosine',4,'Squared-distance cosine identity.',
 '''(N2 (v 0-v 2) (v 1-v 3)).eq
    (N2 (v 0) (v 1) + N2 (v 2) (v 3) - ZT.natLit 2*D2 (v 0) (v 1) (v 2) (v 3))''',['N2','D2'],1),
('cramer_row1',6,'First Cramer numerator identity: aX+bY=det(A)e.',
 '''(v 0*(v 4*v 3-v 1*v 5)+v 1*(v 0*v 5-v 4*v 2)).eq
    ((v 0*v 3-v 1*v 2)*v 4)''',[],1),
('cramer_row2',6,'Second Cramer numerator identity: cX+dY=det(A)f.',
 '''(v 2*(v 4*v 3-v 1*v 5)+v 3*(v 0*v 5-v 4*v 2)).eq
    ((v 0*v 3-v 1*v 2)*v 5)''',[],1),
('cramer_recover',6,'Adjugate recovery of both coordinates; uniqueness after guarded cancellation.',
 '''((v 3*(v 0*v 4+v 1*v 5)-v 1*(v 2*v 4+v 3*v 5)).eq
      ((v 0*v 3-v 1*v 2)*v 4)) ⋏
    ((v 0*(v 2*v 4+v 3*v 5)-v 2*(v 0*v 4+v 1*v 5)).eq
      ((v 0*v 3-v 1*v 2)*v 5))''',[],2),
('rotation_norm',4,'Norm under a scaled rotation; set c²+s²=1 for a rotation.',
 '''(N2 (v 0*v 2-v 1*v 3) (v 1*v 2+v 0*v 3)).eq
    (N2 (v 0) (v 1)*N2 (v 2) (v 3))''',['N2'],1),
('rotation_dot',6,'Dot product under the same scaled rotation.',
 '''(D2 (v 0*v 2-v 1*v 3) (v 1*v 2+v 0*v 3)
      (v 0*v 4-v 1*v 5) (v 1*v 4+v 0*v 5)).eq
    (N2 (v 0) (v 1)*D2 (v 2) (v 3) (v 4) (v 5))''',['N2','D2'],1),
('affine_determinant',8,'An invertible linear map scales oriented doubled areas by its determinant.',
 '''(W2 (v 0*v 4+v 1*v 5) (v 2*v 4+v 3*v 5)
      (v 0*v 6+v 1*v 7) (v 2*v 6+v 3*v 7)).eq
    ((v 0*v 3-v 1*v 2)*W2 (v 4) (v 5) (v 6) (v 7))''',['W2'],1),
('reflection_norm',4,'Cleared-denominator reflection identity.',
 '''let q := N2 (v 0) (v 1)
  let h := D2 (v 0) (v 1) (v 2) (v 3)
  (N2 (q*v 2-ZT.natLit 2*h*v 0) (q*v 3-ZT.natLit 2*h*v 1)).eq
    (q.sq*N2 (v 2) (v 3))''',['N2','D2'],1),
('projection_remainder',4,'Cleared squared norm of the orthogonal residual.',
 '''let q := N2 (v 0) (v 1)
  let h := D2 (v 0) (v 1) (v 2) (v 3)
  (N2 (q*v 2-h*v 0) (q*v 3-h*v 1)).eq
    (q*(q*N2 (v 2) (v 3)-h.sq))''',['N2','D2'],1),
('circle_parameter',1,'Rational parametrization of the unit circle after clearing 1+t².',
 '''(N2 (ZT.natLit 1-(v 0).sq) (ZT.natLit 2*v 0)).eq
    ((ZT.natLit 1+(v 0).sq).sq)''',['N2'],1),
('sphere_parameter',2,'Stereographic rational parametrization of the unit sphere.',
 '''(N3 (ZT.natLit 2*v 0) (ZT.natLit 2*v 1)
      (ZT.natLit 1-(v 0).sq-(v 1).sq)).eq
    ((ZT.natLit 1+(v 0).sq+(v 1).sq).sq)''',['N3'],1),
('quadratic_completion',4,'4a(ax²+bx+c)=(2ax+b)²-(b²-4ac).',
 '''(ZT.natLit 4*v 0*(v 0*(v 3).sq+v 1*v 3+v 2)).eq
    ((ZT.natLit 2*v 0*v 3+v 1).sq-((v 1).sq-ZT.natLit 4*v 0*v 2))''',[],1),
('parabola_focus',3,'Focus/directrix squared-distance identity for y²=4px.',
 '''(N2 (v 1-v 0) (v 2)-(v 1+v 0).sq).eq
    ((v 2).sq-ZT.natLit 4*v 0*v 1)''',['N2'],1),
('conic_line_expansion',11,'Exact second-order expansion of a conic on a line.',
 '''(F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6+v 10*v 8) (v 7+v 10*v 9)).eq
    (F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) +
     v 10*((ZT.natLit 2*v 0*v 6+v 1*v 7+v 3)*v 8 +
           (v 1*v 6+ZT.natLit 2*v 2*v 7+v 4)*v 9) +
     (v 10).sq*Q2 (v 0) (v 1) (v 2) (v 8) (v 9))''',['F2','Q2'],1),
('discriminant_congruence',7,'Conic discriminant multiplies by the square of the linear determinant.',
 '''let a' := v 0*(v 3).sq+v 1*v 3*v 5+v 2*(v 5).sq
  let b' := ZT.natLit 2*v 0*v 3*v 4+v 1*(v 3*v 6+v 4*v 5)+ZT.natLit 2*v 2*v 5*v 6
  let c' := v 0*(v 4).sq+v 1*v 4*v 6+v 2*(v 6).sq
  (b'.sq-ZT.natLit 4*a'*c').eq
    ((v 3*v 6-v 4*v 5).sq*((v 1).sq-ZT.natLit 4*v 0*v 2))''',[],1),
('cross_orthogonal',6,'The cross product is perpendicular to both original vectors.',
 '''let a := v 1*v 5-v 2*v 4
  let b := v 2*v 3-v 0*v 5
  let c := v 0*v 4-v 1*v 3
  ((D3 a b c (v 0) (v 1) (v 2)).eq (ZT.natLit 0)) ⋏
    ((D3 a b c (v 3) (v 4) (v 5)).eq (ZT.natLit 0))''',['D3'],2),
('lagrange3',6,'Three-dimensional Lagrange identity.',
 '''(N3 (v 0) (v 1) (v 2)*N3 (v 3) (v 4) (v 5)).eq
    ((D3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).sq+
     N3 (v 1*v 5-v 2*v 4) (v 2*v 3-v 0*v 5) (v 0*v 4-v 1*v 3))''',['N3','D3'],1),
('vector_triple',9,'u×(v×w)=v(u·w)-w(u·v), with all three coordinates stated.',
 '''let a := v 4*v 8-v 5*v 7
  let b := v 5*v 6-v 3*v 8
  let c := v 3*v 7-v 4*v 6
  let h := D3 (v 0) (v 1) (v 2) (v 6) (v 7) (v 8)
  let k := D3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  ((v 1*c-v 2*b).eq (v 3*h-v 6*k)) ⋏
    (((v 2*a-v 0*c).eq (v 4*h-v 7*k)) ⋏
      ((v 0*b-v 1*a).eq (v 5*h-v 8*k)))''',['D3'],3),
('skew_line_invariant',11,'The normal component of an interpoint displacement is constant along two lines.',
 '''let a := v 1*v 5-v 2*v 4
  let b := v 2*v 3-v 0*v 5
  let c := v 0*v 4-v 1*v 3
  (D3 (v 6+v 9*v 0-v 10*v 3) (v 7+v 9*v 1-v 10*v 4)
      (v 8+v 9*v 2-v 10*v 5) a b c).eq
    (D3 (v 6) (v 7) (v 8) a b c)''',['D3'],1),
('weighted_variance',9,'Three-point weighted variance identity; positivity is a separate guarded result.',
 '''((v 0+v 1+v 2)*(v 0*N2 (v 3) (v 4)+v 1*N2 (v 5) (v 6)+v 2*N2 (v 7) (v 8))-
      N2 (v 0*v 3+v 1*v 5+v 2*v 7) (v 0*v 4+v 1*v 6+v 2*v 8)).eq
    (v 0*v 1*N2 (v 3-v 5) (v 4-v 6)+v 0*v 2*N2 (v 3-v 7) (v 4-v 8)+
      v 1*v 2*N2 (v 5-v 7) (v 6-v 8))''',['N2'],1),
('radical_axis',8,'Subtracting two circle powers gives an affine linear expression.',
 '''((N2 (v 0-v 2) (v 1-v 3)-v 6)-(N2 (v 0-v 4) (v 1-v 5)-v 7)).eq
    (ZT.natLit 2*((v 4-v 2)*v 0+(v 5-v 3)*v 1)+
      N2 (v 2) (v 3)-N2 (v 4) (v 5)-v 6+v 7)''',['N2'],1),
('conic_midpoint',10,'Symmetric second difference of a quadratic is twice its homogeneous quadratic part.',
 '''(F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6+v 8) (v 7+v 9)+
      F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6-v 8) (v 7-v 9)).eq
    (ZT.natLit 2*F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)+
      ZT.natLit 2*Q2 (v 0) (v 1) (v 2) (v 8) (v 9))''',['F2','Q2'],1),
]

parts = [header]
for name, arity, doc, body, helpers, count in items:
    parts.append(f'/-- {doc} -/\ndef {name} {{n : ℕ}} (v : Fin {arity} → ZT n) : Fm PTm n :=\n  {body}\n\n')
    proof = '  unfold ' + ' '.join([name] + helpers) + '\n'
    if count == 2:
        proof += '  constructor <;> ipra_ring\n'
    elif count == 3:
        proof += '  refine Prf.andI ?_ (Prf.andI ?_ ?_) <;> ipra_ring\n'
    else:
        proof += '  ipra_ring\n'
    # Prf is an inductive family with several constructors; be explicit.
    proof = proof.replace('  constructor <;> ipra_ring', '  refine Prf.andI ?_ ?_ <;> ipra_ring')
    parts.append(f'theorem {name}_open (v : Fin {arity} → ZT n) :\n    Γ ⊢[PRAAx] {name} v := by\n{proof}\n')
    parts.append(f'def {name}_sentence : Fm PTm 0 :=\n  univ {2*arity} ({name} (fun i : Fin {arity} => zvar i))\n\n')
    parts.append(f'theorem {name}_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] {name}_sentence :=\n  closeUniv {2*arity} ({name}_open _)\n\n')

parts.append('end LeanProofs.IPRA.Geometry.AnalyticGeometryPacket\n\n')
parts.append('/-! Audit all intended closed object-language endpoints after a successful build. -/\n')
for name, *_ in items:
    parts.append(f'#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.{name}_closed\n')

(HERE / 'ObjectCertificates.lean').write_text(''.join(parts), encoding='utf-8')
(HERE / 'certificate_index.json').write_text(json.dumps([
    {'name': name, 'signed_integer_parameters': arity,
     'natural_parameters': 2*arity, 'description': doc,
     'lean_endpoint': 'LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.'+name+'_closed',
     'status': 'uncompiled candidate object-iPRA derivation'}
    for name, arity, doc, *_ in items], indent=2), encoding='utf-8')
print(f'Wrote {len(items)} candidate closed object-iPRA certificates.')
