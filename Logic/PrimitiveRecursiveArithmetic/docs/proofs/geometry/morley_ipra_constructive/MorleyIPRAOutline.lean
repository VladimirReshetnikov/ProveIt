/-!
# Lean/iPRA completion map for Morley's trisector theorem

This is an implementation outline, not a completed formalization.  It is meant
to live beside the current ProveIt tree at commit
`0bba41d70f061442357cae0f6de055434a33fb09`.

Suggested imports in that checkout:

```
import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation
import ConciseIPRA.NativeFullNormal
```

The existing infrastructure supplies:

* `PR k`, `PTm n`, and `PRAAx` for the usual first-order iPRA presentation;
* `Prf` for intuitionistic natural deduction with equality;
* `native_iff_pra` and `pra_iff_native` for transfer between the native scalar
  calculus and iPRA.

No declaration below is asserted as already present.  The comments give exact
module boundaries, representations, theorem statements, and dependencies.
-/

namespace LeanProofs.ConciseIPRA.Morley

/-!
## M1: reflected sparse polynomials (`Morley/Poly.lean`)

Encode a signed coefficient as a pair of naturals, a monomial as a bounded
exponent vector, and a polynomial as a bounded list.  Define primitive-recursive
symbols

```
polyAdd polyMul polyPow polyNorm polyEq : PR ...
```

and prove their computation equations in `PRAAx`.  Reify the eighteen exact
checks from `morley_identity_certificate.json`; the two central ones are the
shifted triple-angle and Morley-bracket ideal-membership certificates.

Target theorem:

```
theorem check_core_identities :
  [] ⊢[PRAAx] app morleyCoreCheck ![] ≐ numeral 1
```

The proof is quantifier-free evaluation plus `PRA.qfInd`; no excluded middle is
required.
-/

/-!
## M2: exact scalar certificates (`Morley/ScalarCert.lean`)

Use one monic square-free `p : Z[X]` and represent every scalar by a normalized
residue `q/d` in `Q[X]/(p)`, with `d > 0`.  The certificate also carries a
rational isolating interval and a finite Sturm/Thom (or signed-subresultant)
trace for the selected real root.  Equality is normalized residue equality.
Every factor canceled by the Morley proof has an explicit local inverse witness;
there is no need to prove that the whole quotient is a field.

Primitive-recursive symbols:

```
polyRem scalarNorm scalarAdd scalarNeg scalarMul scalarEq : PR ...
inverseClaimOK signTraceOK scalarCertOK                   : PR ...
```

Required correctness lemmas are purely finite: normalization commutes with the
coded operations, accepted inverse equations multiply to one, and accepted sign
traces choose the intended internal branches.  The equality core uses only
residue normalization and inverse equations; the sign layer is for the
Euclidean interpretation.
-/

/-!
## M3: rotation pairs and exact plane geometry (`Morley/GeometryCert.lean`)

Represent a vector by two scalar codes.  Define primitive-recursive checkers for
pair multiplication, conjugation, dot product, determinant, ray incidence,
unit directions, and squared distance.

```
rotMul conjPair dot det onPositiveRay sqDist : PR ...
```

A `MorleyCert` contains:

* `A,B,C,P,Q,R`;
* positive side lengths and a positive common scale `lambda`;
* unit side directions;
* one-third rotations `a,b,g` and the positive sixty-degree rotation `u`;
* the scale equations
  `ellBC=lambda*im(a^3)`, `ellCA=lambda*im(b^3)`,
  `ellAB=lambda*im(g^3)`;
* six positive ray parameters and the three double-incidence equations;
* inverse witnesses for the shifted-sine factors used in the three cyclic
  cancellations;
* the orientation/sign traces selecting internal trisectors.

```
def morleyCertOK    : PR 1
def equilateralSqOK : PR 1
```

Main object-theory statement:

```
theorem ipra_morley_certificate :
  [] ⊢[PRAAx]
    all (morleyCertOK (var 0) ≐ one ⟶
         equilateralSqOK (var 0) ≐ one)
```

Proof route: unfold the checker; invoke the reflected polynomial certificates;
derive the two adjacent-trisector lengths at `A` by determinant extraction;
apply the algebraic angle-sum pair identity and squared-distance expansion;
repeat by cyclic renaming; combine the two equalities.  The matrix is
quantifier-free.  Quantifier-free induction is needed only for bounded
polynomial/list traversals.
-/

/-!
## M4: generic Mathlib layer (`Morley/Core.lean`)

Before reflection, prove the same theorem over a generic `LinearOrderedField K`
(or over a commutative ring equipped with the named inverses).  This is the
fastest place to debug geometry.  `MorleyAlgebra.lean` in this archive supplies
candidate proofs of the algebraic lemmas.

Suggested theorem:

```
theorem morley_of_certificate
    (d : MorleyData K) (hd : d.Valid) :
    sqDist d.P d.Q = sqDist d.Q d.R ∧
    sqDist d.Q d.R = sqDist d.R d.P
```

The proof should import no trigonometric or analytic API.
-/

/-!
## M5: transfer to the concise native calculus (`Morley/Native.lean`)

Translate the iPRA formula by `NFm.ofPRA`, then use `pra_iff_native` (or prove it
natively first and use `native_iff_pra`).  A compact final result should have
shape

```
theorem native_morley_certificate :
  NPrf [] (NFm.ofPRA morleyCertificateFormula)
```

The bridge theorem records exact derivability equivalence, not merely
consistency or equiconsistency.
-/

/-!
## M6 (optional): constructor for algebraic triangles (`Morley/Alg.lean`)

For a coded real-algebraic triangle, construct a certificate by fixed-degree
root isolation:

1. adjoin positive square roots for side norms;
2. solve the cubic unit-rotation equations at each vertex;
3. select the internal root by a Sturm/Thom sign certificate;
4. solve three 2x2 linear systems for `P,Q,R`;
5. combine the finitely many coordinates into one primitive-element
   presentation and emit normalized residues, inverse witnesses, and sign
   traces.

All searches are bounded by explicit degree, height, and root-separation bounds,
so the constructor is primitive recursive.  Its correctness is a substantial
separate formalization and is not needed for the core witness-parametric
implication.
-/

end LeanProofs.ConciseIPRA.Morley
