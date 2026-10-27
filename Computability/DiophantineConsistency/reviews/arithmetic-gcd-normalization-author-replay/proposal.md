# Internal gcd certificate and actual relaxed-norm normalization

27 October 2026. Read-only plan; no new Lean source, compiler or overlay.
The proposed pair is `ArithmeticGcdNormalization` plus focused Checks.
All mathematical variables below belong to an arbitrary ORingStructure V
model of IΣ1. The leaf derives the actual normalization needed after
KnownUnit; it will not assume a gcd, coprimality, least-element or desired
normalization certificate.

## Fixed graph and public target

Use natural coefficients throughout:

```lean
def Bez (a b g : V) : Prop :=
  ∃ u v w z : V, g+a*u+b*v=a*w+b*z

def GcdCert (a b g : V) : Prop := g∣a ∧ g∣b ∧ Bez a b g

-- Fixed syntax, defined before model parameters:
def gcdDef : 𝚺₁.Semisentence 3 := .mkSigma
  “g a b. g ∣ a ∧ g ∣ b ∧
    ∃ u v w z, g+a*u+b*v=a*w+b*z”

theorem gcd_certificate_total (a b : V) : ∃! g : V, GcdCert a b g

noncomputable def gcdValue (a b : V) : V :=
  Classical.choose (gcd_certificate_total a b)

instance gcd_defined : 𝚺₁-Function₂[V] gcdValue via gcdDef

theorem norm_normalization (R D f : V)
    (hR : 0<R) (hD : 0<D) (hf : 0<f)
    (hnorm : R*R+D=D*(f*f)) :
    ∃ d s t : V, 0<d ∧ 0<s ∧ 0<t ∧
      D=d*d*s ∧ R=d*s*t ∧ f*f=1+s*t*t
```

The graph is syntactically Sigma1: divisibility has an existing fixed Sigma0
graph and the four coefficients are unbounded existentials. It contains no
unbounded universal over common divisors. Totality and uniqueness are proved
first, then the chosen function receives the exact fixed-graph instance.
The object `gcdValue` is not used inside an induction until that instance
exists. No primitive-recursive Euclid interpreter or Nat gcd is assumed.

The positive f premise is available in the actual carrier domain. It is
redundant for the additive norm but permits a direct literal adapter from
`R*R=D*(f*f-1)`: positivity gives1≤f*f, hence adding D and cancelling the
justified natural subtraction gives the additive norm. Both statements
remain all-internal arithmetic. The final endpoint is normalization, not
merely a helper that takes the desired coprimality as an extra hypothesis.

## Shorter existence proof: least positive natural Bezout certificate

For a+b>0, use the Sigma1 predicate

```text
P(g) := 0<g and g≤a+b and Bez(a,b,g).
```

It has the explicit witness g=a+b with coefficients (0,0,1,1). Apply
`InductionOnHierarchy.least_number 𝚺 1` to this represented predicate.
This is an existing internal IΣ1 least-number theorem, not a standard-Nat
minimum or an assumed fundamental principle for arbitrary Lean predicates.
All coefficient witnesses remain natural internal values. The minimum is
bounded by a+b even though its coefficient witnesses need no bound.

Let its certificate be `g+a*u+b*v=a*w+b*z`. Put q=a/g, r=a%g.
The existing division equation gives a=g*q+r, and g>0 gives r<g.
Multiplying the certificate by q yields the exact natural equality

```text
r + a*(q*w) + b*(q*z) = a*(1+q*u) + b*(q*v).
```

Thus Bez(a,b,r) holds. If r>0, then r<g≤a+b puts r in P, contradicting
minimality. Therefore r=0 and g∣a. With q=b/g and r=b%g the corresponding
certificate is

```text
r + a*(q*w) + b*(q*z) = a*(q*u) + b*(1+q*v).
```

It gives g∣b identically. No subtraction of Bezout coefficients occurs.
For a+b=0, both inputs are0 and g=0 has a direct GcdCert; its coefficients
can all be0. No division by zero is used in the positive minimum argument.

This replaces the longer but valid fixed-N Euclid proposal. That alternate
induction would transport a certificate for (b,r), a=b*q+r, by
`g+a*v+b*(u+q*z)=a*z+b*(w+q*v)`. It is unnecessary for this leaf and will
not be implemented in parallel.

## Greatestness, uniqueness, and cancellation actually derived

For any GcdCert(a,b,g), every common divisor h of a,b divides g. If h=0,
a=b=0 and the certificate forces g=0. If h>0, taking the natural remainder
of its certificate modulo h removes every a/b multiple and yields g%h=0.
The existing `Arithmetic.mod_eq_zero_iff_dvd` gives the required divisibility.
Two certificates therefore divide each other; existing
`Arithmetic.dvd_antisymm` gives uniqueness, including the all-zero case.

For positive R,D choose its actual certificate g, and quotients t,d with
R=g*t and D=g*d. Positivity forces g,t,d>0. Cancelling the positive g in
the *same* Bezout equality gives

```text
1+t*u+d*v=t*w+d*z.
```

This is the derived coprimality witness. A separate local cancellation lemma
will prove that, for d>0, this equality and d∣t*x imply d∣x: multiply the
equality by x and reduce modulo d. Every term except x is a multiple of d.
There is no invocation of an unavailable internal Coprime API, no prime
factorization, and no normalized-gcd hypothesis.

Substitution in the actual norm and cancellation of g gives

```text
g*t*t+d=d*f*f,
```

so d∣g*t*t. Apply the proved unit-certificate cancellation twice, first at
x=g*t and then at x=g, obtaining d∣g. Choose s with g=d*s; positivity of g
and d gives s>0. Then ordinary multiplication identities yield
D=d*d*s and R=d*s*t. Substitute g=d*s in the last norm and cancel d to
get f*f=1+s*t*t. This completes the proposed public endpoint without any
source rank, Pell index, cofinality or squarefree premise.

## Actual available contracts and source pins

All of these APIs are already in the selected closure:

- `Foundation.FirstOrder.Arithmetic.Schemata`, lines218–220:
  `InductionOnHierarchy.least_number`, and lines268–275 its sigma wrapper.
  Source SHA `5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd`.
- `Foundation.FirstOrder.Arithmetic.IOpen.Basic`: `div_add_mod` at275,
  `mod_lt` at314, `mod_eq_zero_iff_dvd` at324,
  `mod_add_remove_right_of_dvd` at333 and left variant at339,
  `mod_add` at342 and `mod_mul` at347. Source SHA
  `4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b`.
- `Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions`: bounded
  divisibility graph at163–175, `le_of_dvd` at188, `dvd_antisymm` at196,
  `dvd_one_iff` at204. Source SHA
  `289c1c72c5a87a8dfbd1c4f4fcbead879570dbb47ab33f4612df05f3f91ee168`.

The external mathematical guide remains
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRelaxedMain.lean`,
SHA `8a18a6a953b8c529c35362c394e67065e943bbe17c2c22348d64d5eecbd898a4`.
Its literal E16 at the relaxed_aux statement is
`(i*c^2)^2=(A^2-1)*(f^2-1)`. Positive i,c and A>1 supply the proposed R,D
positivity. This guide is not an import or proof oracle. The later consumer
must still combine the normalization with the same derived KnownUnit for
both (A,d) and (f,t), then prove sequence composition/strong divisibility,
the large-c estimate and the final cubic-modulus conclusion. None is silently
included in this normalization claim.

## Minimal authenticated cache and next execution boundary

Proposed imports are only
`Foundation.FirstOrder.Arithmetic.IOpen.Basic` and `Mathlib.Tactic.Ring`.
They need86 custom modules, all86 Foundation,344 custom artifacts,37 external
names and111 recorded boundary artifacts (37 primaries plus74 companions),
with zero refreshes. KnownUnit, PRF, other Pell leaves and the old external
Jones proof are not imported. This is a strict source-header subgraph of the
accepted97-module Classification inventory, not a new dependency union.

`arithmetic-gcd-normalization-cache-audit.py` was fully read before its
read-only run. It reconstructed the exact reachable topological DAG,
rehashed selected current sources/objects, original accepted provider pins,
all boundaries and their actual first providers. It made1,978 hash
comparisons over644 paths, with no compiler invocation or overlay creation.
The resulting `arithmetic-gcd-normalization-cache-plan.json` has SHA256
`1206727b503151356d3ba49f713e09bf88b84d3d6af131ca6a29625e221c2a14`.
The immutable parent inventory retains SHA256
`a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99`.
All package/central cached objects retain that existing authenticated
provenance; none was refreshed or claimed freshly compiled.

After ROOT review/authorization, only the proposed new main/Checks would be
compiled in a private overlay with fresh regular outputs, Lean4.32,
-M6000 -j1 -DElab.async=false and the512MiB reserve. Every attempted source,
input, driver, log and result would be preserved. No source implementation,
compiler run, dependency refresh, shared-document edit or Git change has
occurred for this plan.
