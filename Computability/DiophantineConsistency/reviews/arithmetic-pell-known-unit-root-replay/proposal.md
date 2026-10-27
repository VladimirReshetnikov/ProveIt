# Next substantive integrality checkpoint: classify from a known positive unit

27 October 2026. Read-only proposal, no new Lean source, compiler or overlay.
This incorporates ROOT's bounded-unit observation after rereading the complete
`PellRelaxedMain.lean` and the relevant `PellHalf90` odd-polynomial contracts.

The smallest coherent next pair is `ArithmeticPellKnownUnit` plus Checks,
importing only accepted `ArithmeticPellClassification`. It replaces the
arbitrary-discriminant fundamental-unit existence/classification step actually
used by `Jones1980.relaxed_aux`, without importing that external Nat theorem.
Unlike another residue corollary, this supplies a missing part of integrality.

All variables below are in an arbitrary `[ORingStructure V]` model of IΣ1.
The proposed public result is:

```lean
theorem known_unit_classification (D A S : V)
    (hD : 0<D) (hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) :
    ∃ b v : V, 0<v ∧ b+2≤A ∧ v≤S ∧
      (b+2)*(b+2)=1+D*v*v ∧
      ∀ x y : V, x*x=1+D*y*y →
        ∃ n : V, n≤y ∧ x=xcoord n b ∧ y=v*ycoord n b
```

No least-unit or classification premise is supplied. The known positive
solution supplies the finite search bound. Pick the least positive ordinate
v≤S admitting some F≤A with F²=1+Dv². The seed makes this bounded open
predicate nonempty. Any smaller positive solution has x≤A by square
comparison, so this bounded minimum is also the required minimum among
all positive norm solutions. Positivity implies F≥2; set b=F−2 with its
explicit bound, so b+2=F. This avoids unbounded Pell existence, continued
fractions and an external minimality oracle.

For any positive solution (x,y), minimality gives v≤y. Put
u=F*x−D*v*y and z=F*y−v*x. All subtractions are justified:

- `(F*y)²−(v*x)²=y²−v²≥0`, hence z is a genuine nonnegative difference.
- `(F*x)²−(D*v*y)²=F²+D*y²>0`, hence u>0.
- `v²*x²−(F−1)²*y²=v²+2*(F−1)*y²>0`, hence z<y.

The exact identities are u²=1+Dz², x=F*u+D*v*z and y=v*u+F*z.
The zero-ordinate case is x=1. An internal Sigma1 order induction, with
bounded x≤(D+1)*y+1 and an existential index n≤y, classifies all solutions.
The inverse identities and the represented recurrence identify the new
index n+1, retaining the exact ordinate scale v. The discriminant bridge
`delta b=D*v²` follows from F=b+2 and its norm. This is the meaningful
generalization of the accepted direct descent for base b+2; no standard
Nat induction is substituted for the internal order induction.

Remaining work is explicit. This leaf does not by itself produce the common
discriminant or prove `delta A ∣ i*c²`, `c∣m`, or p=R. The external
`relaxed_aux` next uses sequence composition, strong divisibility/gcd,
the large-c estimate and a cubic-modulus ordinate congruence. Those are
substantial internal lemmas, not assumptions to hide in this result.

A useful possible simplification of the common-discriminant step is recorded
as unimplemented algebra. Let I=i*c², E=A²−1, g=gcd(I,E), I=g*t and E=g*d.
Then gcd(t,d)=1 and I²=E*(f²−1) imply d∣g. Write g=d*s; cancellation gives
E=d²*s, I=d*s*t, and f²=1+s*t². Thus (A,d) and (f,t) are known positive
solutions for the same discriminant s, without requiring s to be squarefree.
The proposed known-unit theorem applies directly. A later proof must actually
construct internal gcd/quotients and prove the coprime cancellation; this
note does not assert those APIs are already available in the selected cache.

Qh remains another substantive branch, but it need not require an internal
integer-polynomial type. Define the natural odd quotient
`Q(h,b)=xcoord(2*h+1)b/(b+2)`. Prove actual divisibility and the additive
recurrence `Q(h+2)+2*Q(h+1)+Q(h)=4*(b+2)^2*Q(h+1)` by internal induction.
A correlated pair of equal/opposite remainder relations can then express
the two evaluations at I²+A²≡1 and I²≡0, avoiding an unrepresented negative
parameter. A future endpoint should derive auxiliary norm index s, oddness,
`u²≡ycoord(s,a)² (mod f)` and `u≡±s (mod c)` from the actual norm and
those literal modulus relations. It must not accept those evaluations as
oracles. This Qh branch is deferred in favor of the first integrality step.

The exact minimal cache is the already accepted
`research/arithmetic-pell-congruences-cache-plan.json`, SHA256
`a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99`:
97 custom modules,95 Foundation,382 artifacts,38 external boundaries,
114 companions, zero refresh. Its sole direct import is Classification.
A read-only rehash of all listed pins and selected source/object/boundary
records checked642 distinct paths. No new provider or source union is needed.

The two non-Foundation providers are:

- Recurrence source `92acf4d2ce4d63e13cccb1afc5ebe5731e3648957dfd18a5311e537c41597c0e`,
  object `17f45d72cbc6e3388dc1bd34e7e57868ef57dc99c0d5b7b14a8334726ea71f62`,
  `/tmp/arithmetic-pell-recurrence-peer-zvk0fyyh/lib`.
- Classification source `93cb97fababdd4a1aac7766e5be1d35b3af69b52e4a7ac23726f2c6c42ec8f73`,
  object `29fc853c66cbea0cd892ad5a38fb1c708388b80c2a448965fef25822c10ffb5e`,
  `/tmp/arithmetic-pell-classification-peer-ugrz4njr/lib`.

The external source guide `PellRelaxedMain.lean` is pinned at
`8a18a6a953b8c529c35362c394e67065e943bbe17c2c22348d64d5eecbd898a4`;
`PellHalf90.lean` at `1d737e0cf751e1d5dbca3b4d75a1a66560fd2147f48da638b44d54db158be1a9`.
They are mathematical references only, not proposed imports. ResidueClasses
is accepted at a2df24bead but is not needed for this narrower first leaf.
No implementation is authorized by this note; the independent RootPerm
review/replay has priority next.
