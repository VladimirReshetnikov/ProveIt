# Internal Pell strong divisibility: next checkpoint

27 October 2026. Read-only proposal for `ArithmeticPellStrongDivisibility`
and focused Checks. No new Lean source, overlay, compiler or dependency
refresh has been created. The accepted CommonUnit sources remain unchanged.

The minimal imports are exactly:

```lean
import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ArithmeticGcdNormalization
```

Use the existing fixed represented `gcdValue` and `xcoord/ycoord` in an
arbitrary internal IΣ1 model. Write X(j),Y(j) for the coordinates at base b
and delta=(b+1)*(b+3). No standardness condition on an index is allowed.

## Main statements

```lean
theorem strong_divisibility (b m n : V) :
    gcdValue (ycoord m b) (ycoord n b)=ycoord (gcdValue m n) b

theorem y_dvd_iff (b m n : V) :
    ycoord m b ∣ ycoord n b ↔ m∣n

theorem scaled_common_divisor (b m n T h : V)
    (hm : h∣T*ycoord m b) (hn : h∣T*ycoord n b) :
    h∣T*ycoord (gcdValue m n) b
```

All statements include zero indices, zero h and zero T. The caller provides
neither coprimality nor a desired index/divisibility conclusion. The third
statement is the precise common-divisor operation needed for the later
relaxed-norm estimate; it does not claim that estimate or ep∣n already.

## Derived arithmetic and cancellation helpers

First derive the usual elementary gcd identities from the existing actual
`GcdCert`, rather than importing a standard-Nat gcd. `gcd_spec` supplies
both divisibilities and a natural Bezout certificate; `bez_divisor` makes
its greatest-divisor property valid even for divisor0. Thus identical
common divisors imply equal gcds by mutual divisibility. Symmetry, zero
identities, and `gcdValue a b=a` when a∣b follow directly. In particular,
`GcdCert a b a` has certificate coefficients `(0,0,1,0)` when a∣b.

Subtraction of a known divisible summand needs no sign or modulus premise.
For all a,b, the identity

```text
a + (a+b)*0 + b*1 = (a+b)*1 + b*0
```

is exactly `Bez (a+b) b a`. Applying `bez_divisor` proves
`h∣a+b → h∣b → h∣a`, including h=0. Together with explicit addition
witnesses, this gives the ordinary common-divisor equivalence
`(h∣m ∧ h∣m+n) ↔ (h∣m ∧ h∣n)` and hence the numeric gcd addition rule.

The Pell norm supplies the required cancellation certificate. If
`h∣Y(m)`, choose the actual quotient k with Y(m)=h*k. The norm is
`X(m)*X(m)=1+delta*Y(m)*Y(m)`. Consequently the coefficients
`(0, delta*k*Y(m), X(m), 0)` prove **`Bez (X(m)) h 1`**:

```text
1 + X(m)*0 + h*(delta*k*Y(m)) = X(m)*X(m) + h*0.
```

This remains valid for h=0; no inverse modulo0 is asserted. The accepted
`unit_certificate_cancel` now derives `h∣z` from `h∣X(m)*z`.
No generic coprimality predicate or theorem is assumed.

Using the actual addition equation
`Y(m+n)=X(m)*Y(n)+Y(m)*X(n)`, remove the second divisible summand and
apply this norm-derived cancellation. This proves

```text
(h∣Y(m) ∧ h∣Y(m+n)) ↔ (h∣Y(m) ∧ h∣Y(n)).
```

Therefore both the numerical indices and their represented ordinates have
exactly matching gcd addition/subtraction rules. This avoids introducing
a new quotient-remainder recurrence or a modular unit representation.

## Genuine internal Euclidean descent

Prove the main theorem with `ISigma1.sigma1_order_induction` at the internal
sum bound k. Its exact bounded-universal invariant is

```text
∀m≤k, ∀n≤k, m+n≤k → gcdValue(Y(m),Y(n))=Y(gcdValue(m,n)).
```

The coordinate and gcd functions have existing fixed Sigma1 definitions;
the represented equality and bounded universal closures give a Sigma1
predicate. The guard m+n≤k is elementary bounded arithmetic. There is no
unbounded universal induction hypothesis or metatheoretic Nat recursion.

If m=0 or n=0, use the derived gcd zero identities and Y(0)=0. Otherwise,
when m≤n, put r=n-m. The justified identity `m+(n-m)=n` rewrites both
gcd addition rules. The induction query is the pair (m,r) at bound n:
m≤n, r≤n and m+r=n, while n<m+n≤k since m>0. It gives exactly the
needed result. When n<m, swap the two gcd arguments, then query (n,m-n)
at bound m<k. Equality m=n is included: the smaller pair has a zero entry.
Every subtraction is used only after the corresponding order premise.
No divisibility of the queried index is assumed to drive the descent.

## Index reflection and zero indices

For the `y_dvd_iff` endpoint, derive strict growth
using only the actual recurrence APIs. Addition, `one_le_x`, and
`time_le_y` give

```text
Y(m)+r ≤ Y(m+r).
```

If m<n, then r=n-m>0 and m+r=n, so Y(m)<Y(n). Thus the actual represented
Y is injective at all internal indices. This is the same elementary route
used in accepted `ArithmeticPellCongruences.y_add_ge/y_strictMono`, whose
full source was inspected, but it needs no Congruences or Classification
import and no residue/index oracle.

If Y(m)∣Y(n), the direct gcd certificate yields
`gcdValue(Y(m),Y(n))=Y(m)`. Strong divisibility and the derived injectivity
give `gcdValue(m,n)=m`, and its actual gcd specification gives m∣n.
Conversely m∣n gives `gcdValue(m,n)=m`; strong divisibility and the gcd
specification give Y(m)∣Y(n).

This proof does not divide by Y(m) or take a remainder modulo Y(m), so
there is no concealed positive-modulus premise. At m=0, it says
`0∣Y(n) ↔ 0∣n`: Y(n)=0 implies n=0 by `time_le_y`; both reverse
implications are immediate. At n=0, both divisibilities are true. At m=1,
Y(1)=1 and all indices are allowed. Focused checks should retain these
boundaries explicitly, along with positive and arbitrary internal queries.

## Scaling and the remaining relaxed-norm use

Derive `gcdValue (T*x) (T*y)=T*gcdValue x y` directly from the same
certificate: multiply its equality by T and reuse its four coefficients;
scale both divisibility witnesses. This is valid even for T=0 and does not
cancel T. Combining it with strong divisibility and `bez_divisor` proves
`scaled_common_divisor` above.

The accepted CommonUnit decomposition later supplies
`R=T*Y(n)`, `delta(a)=T*S`, and `S*c=Y(e*p)` with
`T=delta(b)*S`. When the later caller derives c∣R and c∣delta(a)*c,
this checkpoint will give `c∣T*Y(gcd(n,e*p))`. Positivity then gives the
corresponding upper bound on c. **The argument forcing e*p∣n still needs
the separate large-c/growth comparison**; it is not supplied by this
structural gcd result alone. Cubic congruences, c∣m, full Jones relaxed
integrality, Qh and cofinal witnesses remain open.

## Exact sources and reuse

The complete Recurrence, Congruences, Periodicity and GcdNormalization
sources were read; only Recurrence and GcdNormalization are imports.
The actual Recurrence contracts used are `norm`, `addition`, `x_zero`,
`y_zero`, `x_succ`, `y_succ`, `one_le_x`, `time_le_y`, and the coordinate
representation instances. The actual gcd contracts are `GcdCert`, `Bez`,
`gcd_graph`, `gcd_spec`, `gcd_defined`, `gcd_definable`, `bez_divisor`, and
`unit_certificate_cancel`. Generic arithmetic order/subtraction and
`Arithmetic.dvd_antisymm` are already in the selected Foundation closure.

- Recurrence source: `92acf4d2ce4d63e13cccb1afc5ebe5731e3648957dfd18a5311e537c41597c0e`.
- Accepted Recurrence provider: `/tmp/arithmetic-pell-recurrence-peer-zvk0fyyh/lib`,
  object `17f45d72cbc6e3388dc1bd34e7e57868ef57dc99c0d5b7b14a8334726ea71f62`.
- Gcd source: `488783700b1663f66b4caee71e7121eb6c50ab4efe04b39f30d63727cc6c8627`.
- Accepted Gcd provider: `/tmp/arithmetic-gcd-normalization-root-pnbeaddq/lib`,
  object `517c17d6efc7aa6ef20c4f269c082252daf9c77051e402ddbbf5f085cd4ea0c7`.
  ROOT acceptance is commit e821823841, packet
  `b74df44673d2f89c82b6c85237c1e203a03296068dd0f6d455ecf4ad29d14512`.

The exact new inventory is **97 custom modules, 95 Foundation, 382 custom
artifacts, 38 boundary names and 114 total boundary artifacts (38 primaries
plus 76 companions), zero refresh**. The two non-Foundation modules are
Recurrence and GcdNormalization; Classification, Congruences, Periodicity,
KnownUnit and CommonUnit are absent. Historical provenance observations may
mention those packets but do not load their objects into this closure.

The fully read cache auditor rehashed 2,099 observations across 674 pinned
paths, including the accepted Gcd evidence. It verifies the exact reachable
source/header DAG and inherited source/trace authentication. Its SHA256 is
`82c788098e15059f0512899f424d4f9fce31aa567db81202f42efc5b2b5387e1`.
The new cache plan SHA256 is
`6540842617bdadcad5f9d28b42447ff6b3ed9b3ad28d225b323a808997bd4015`.

A separate fully read provider mapper checks all 496 intended first
artifacts: 382 authenticated custom files mapped to prospective private
links and 114 actual first artifacts in explicit package/toolchain paths,
including Init. It checks collisions and every expected artifact's
hash/size without creating any overlay. Mapping JSON SHA256:
`37335c562ed6c82eba945bcfa1e04033828d047aa668dce415f5de16cb082a08`;
mapper SHA256 `fe50e7106092837740ab76e791ddba76affe3632c37a6c31d7598f94d8d41678`.
A later authorized runner must recheck the actual private first providers.

This proposal permits no compiler launch itself. A later two-leaf run must
retain Lean4.32, -M6000, -j1, -DElab.async=false, fresh regular target
objects, a 512MiB reserve, and all failed source/Checks/driver snapshots.
No Foundation rebuild, accepted-source edit, full relaxed-integrality or
PA/HA endpoint claim is part of this checkpoint.
