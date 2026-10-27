# Actual half-carrier index recovery: next internal checkpoint

27 October 2026. Read-only proposal; no new Lean source, overlay, compiler,
or dependency refresh. IndexDivisibility is now independently accepted:
the inventory selects its ROOT provider, not its earlier author provider.

## Decision and exact maintained input

The next missing implication is **main Pell index = literal rank**. Propose
`ArithmeticPellHalfIndex` and focused Checks. This includes the odd-coordinate
quotient transport which is genuinely absent from the current internal
library, followed by the signed step-down and strict half-window argument.
It does not assume the desired index, its parity, a valid source system,
or a canonical Pell witness. The later relation `2*n = rank+1` is separate.

The maintained polynomial is `CurrentPolynomialWindow2011.polynomial`,
definitionally `Carrier65.polynomial CurrentWindowCarry2011.ports`.
`CurrentKernelData2011` binds those ports to
`CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)`; their order is
`[beta,K,lowPort,highPort+beta]`, with **one** fourth-port shift.
`CurrentMaskData2011` defines radix `2^47`, length `2011`, width `94517`,
and beta `2^94517-1`. No compact44 or historical coefficient tuple is used.

In the literal fourteen-coordinate core, write `A=a+2`, `D=delta(a)=A²-1`,
`R=rank`, `I=D*i*c²`, and retain the independent positive `y`. The norm
factors at a positive zero give

* main: `d² = 1+D*c²`;
* strict strong: `f² = 1+D*(i*c²)²`;
* half auxiliary: `I²*V²+y² = 1+I²*y²`;
* literal signed `V=f²*(c*T-R)-c`.

Thus `I²+D=D*f²`, `c|I`, `f²=1 (mod c)`,
`V=-c (mod f)` and `V=-R (mod c)` are algebraic consequences.
The rank abbreviation is not assumed nonnegative until its separate scalar
window has been derived. The old `PellDoubled.doubled_index_core` E17 is
`(o*f-d²)*(o*f-d²+1)=K*(K-1)*(R+j*c)²`: that is **not** this literal
half-parameter E17. There is no `PellRelaxedHalf.lean` in this source tree;
the relevant actual guides are `PellHalf90`, `PellRelaxedMain`, and
`NativePellStepDown`.

## Proposed public mathematical endpoint

Everything below is over an arbitrary `V` with `ORingStructure V` and
`V ⊧ IΣ1`, with all parameters and indices internal to that model.
Use the accepted names `xcoord time a`, `ycoord time a`, and `delta a`;
their Pell base is `a+2`. Define notation for signed natural residues:

`SignMod M u v := u%M=v%M ∨ (u+v)%M=0`.

The substantive endpoint should have exactly this shape (multiplication
may be spelled out in Lean to avoid notation overhead):

```text
half_index (a c d f i R y u : V)
  (hc : 0<c) (hi : 0<i) (hf : 0<f) (hR : 0<R) (hy : 0<y)
  (hmain : d*d=1+delta a*c*c)
  (hstrong : (i*c*c)^2+delta a=delta a*f*f)
  (hbig : (a+2)*delta a*delta a<c)
  (hhalf : 2*R<c)
  (haux : (i*c*c)^2*u*u+y*y=1+(i*c*c)^2*y*y)
  (huf : SignMod f u c)
  (huc : SignMod c u R) :
  d=xcoord R a ∧ c=ycoord R a
```

Here `i` is the coefficient of the relaxed auxiliary parameter `I=i*c²`.
For the maintained strict strong norm it is instantiated as `D*i_original`;
it is not silently identified with the displayed independent `i_original`.
All classification indices and both `p|m,c|m` are conclusions of imported
proved theorems. The signature has no `f=xcoord m a`, `p=R`, `2*n=R+1`,
`Odd R`, source-row predicate, or externally classified pair premise.

A useful final literal adapter in the same pair can take the strict strong
norm, `u=absdiff(f²*c*T, f²*R+c)`, and the additive half norm, replacing
`huf,huc,hstrong` by their exact algebraic derivations. Here
`absdiff L M := (L-M)+(M-L)` uses natural truncated subtractions.
Split `L≤M` or `M≤L`; in each branch prove the exact difference identity
before reducing modulo the positive modulus. This covers either sign and
zero of the displayed `V`; do not assume `c*T>R` or `V>0`.
The adapter retains `hbig` and `hhalf` explicitly. Its conclusion is the
actual represented main pair at `R`, not a full polynomial or HA endpoint.

## Missing transport, without a signed-Qh evaluator

For a base `B=b+2`, use the already represented natural quotient
`U(h,b) := xcoord (2*h+1) b / (b+2)`.
No new primitive-recursion engine or integer model is necessary. Prove:

1. Exact divisibility and reconstruction
   `xcoord (2*h+1) b=(b+2)*U(h,b)` for every internal `h`.
   Derive the odd-coordinate additive recurrence from accepted addition,
   or first derive `X_(j+2)+X_j=2*B*X_(j+1)` and eliminate even terms.
   Prove divisibility by genuine Σ1 induction on adjacent odd indices.
   When using divisibility of a difference, replace it by an exact
   nonnegative ordered subtraction, or use existing divisor/addition
   cancellation. Never cancel `B` modulo an unrelated modulus.
2. `U(0,b)=1`, `U(1,b)+3=4*B²`, and
   `U(h+2,b)+U(h,b)+2*U(h+1,b)=4*B²*U(h+1,b)`.
   Obtain these by exact positive multiplication cancellation, not modular
   inversion. `B≥2` is automatic; use `b=I-2` only after deriving `I≥2`.
3. With `I²+delta a=delta a*f²`, derive
   `SignMod f (U(h,I-2)) (ycoord (2*h+1) a)`.
   The reference polynomial law is
   `Q_h(1-A²)=(-1)^h*Y_A(2h+1)`. Retain that alternating sign.
   Use a Σ1 disjunction on adjacent indices: current equal/opposite
   residues and next opposite/equal residues; successor exchanges them.
   The target odd Y subsequence satisfies the same additive recurrence
   with `A` in place of `I`. Since `I²+A²=1+D*f²`, the two coefficients
   are negatives modulo `f`; additive modular cancellation proves the step.
4. If `c|I`, the same adjacent-sign induction gives
   `SignMod c (U(h,I-2)) (2*h+1)`.
   The positive linear targets obey
   `(2(h+2)+1)+(2h+1)=2*(2(h+1)+1)`; the quotient coefficient is `-2`
   modulo `c`. The resulting sequence is `1,-3,5,-7,...` modulo `c`.

Both signed congruences may be packaged in a single alternating-pair
invariant to keep their sign bookkeeping explicit. The public conclusions
need not expose or assume the parity. All quotient/modulo functions have
existing definability instances. Use actual represented Σ1 induction,
never induction over standard natural indices or an external `Qh` theorem.

## From the norms to the exact rank

Classify the positive main ordinate using `Classification.solution_index`;
obtain `d=X_p(a),c=Y_p(a),p>0`. Derive `2*p<c` rather than assume it.
The bound `A*D²<c` implies `c>Y_2(a)=2*A`, hence `p≥3` by monotonicity.
At `p=3`, `Y_3=4*A²-1>6`; successor growth
`Y_(j+1)≥1+2*Y_j` maintains `2*j<Y_j` for `j≥3`.
This also derives `I=i*c²>1`, allowing the natural base `I-2`.

`IndexDivisibility.relaxed_auxiliary` derives the **same** positive `m`
with `f=X_m(a)`, `p|m`, `c|m`, `I=D*Y_m(a)`. Thus `c≤m` and
`2*p<c≤m`. Classify the actual half norm at base `I`: obtain
`I*u=X_s(I-2), y=Y_s(I-2)`. The equality and `I|I*u` let
`ResidueClasses.odd_index_witness` derive `s=2*h+1`.
Cancel positive `I` in the exact reconstruction to identify `u=U(h,I-2)`.

The first transport and `huf` give `Y_s(a)²=c² (mod f)`.
`Periodicity.double_x` therefore gives
`X_(2*s)(a)=X_(2*p)(a) (mod f)`. This is the positive input branch of
the accepted `ResidueClasses.doubled_step_down`; no square-root cancellation
modulo `f` occurs. It yields `s=±p (mod m)`, then modulo `c` because `c|m`.
The second transport and `huc` give `R=±p (mod c)`.
Now `R,p>0` and `2*R,2*p<c` imply `R+p<c`. The plus-residue alternative
is impossible and the equal-residue alternative forces `R=p`.
Oddness of `R` has not been used.

Boundary checks: the generic signed doubled theorem retains `2*p=m`;
the present norms actually derive strict `2*p<m`. Zero `c,i,R,y` are
explicitly excluded; `u=0` is ruled out by the actual auxiliary norm.
The base2 case `a=0` is allowed: `hbig` still forces `p≥3`.
The modulus `f` is positive by hypothesis and in fact at least2 by the
relaxed norm. No quotient by `c,I,f` is taken before proving positivity.

## Later callers and the first-index identity are still obligations

`Carrier65.value_zero_iff_norms` is an external all-positive theorem. It
identifies the required literal input equations, but is not itself an
internal source-logic proof and is not imported into this arithmetic leaf.
Later internal polynomial callers must derive the norm factors and:

* positivity of the literal rank from the exact transport and port box;
* `R+2<E`, where `E=w*s*q^4`, using the once-shifted fourth port;
* positivity of the first trace `tau=E*nCarrier+k-R` and the omitted
  quotient `k=1+R+E*h`, from the first norm and that window;
* `A*D²<c` and `2*R<c` from these literal first/main data;
* the natural signed-difference encoding of the auxiliary norm.

The existing external `Carrier65Witness`, `FirstPellCarrier`,
`CarrierRankBounds` and `NativePellBootstrap` show their noncircular order.
They must not be replaced by a supplied source-validity premise internally.
Neither `CurrentPolynomialWindow2011.Facts` nor a canonical assignment is
an input: each already packages precisely the source/calibration to prove.

After HalfIndex, `2*nFirst=R+1` can be a separate small useful checkpoint.
Let `Q=E*Y>0`, first base `P=2*Q+1`, main base `A=E+Y+2`.
FirstNorm derives `k=2*Y_nFirst(P)` from the actual consecutive-product
norm. The literal data give `k<c`, `P≥A`, and `E|2*Q`.
An internal joint coordinate monotonicity theorem in the base (Σ1
successor induction on both coordinates) yields `nFirst<p=R` directly:
otherwise `c=Y_p(A)≤Y_nFirst(A)≤Y_nFirst(P)≤k`, contradiction.
This avoids importing external power-growth estimates merely to compare
the two bases. Congruences gives `2*nFirst=R+1 (mod E)` from
`k=1+R+E*h`. With `nFirst<R` and `R+1<E`, the only possible multiple of
`E` in their difference is zero, so `2*nFirst=R+1` and rank oddness follow.
These later premises must be derived from first/main literal data, not
included as desired-index assumptions in a claimed complete endpoint.
The pending first scalar bootstrap can use `R≥8` to get `nFirst≥5`,
then `p≥6` and the finite recurrence bound `Y_6(A)>A*(A²-1)²` for large-c.
Power recovery, cofinal simultaneous witnesses, and final equation/PA/HA
equivalence remain outside both checkpoints.

## Exact minimal proposed cache

Only `ArithmeticPellIndexDivisibility` and `ArithmeticPellResidueClasses`
are proposed imports. The authenticated union is **106 custom modules,
95 Foundation,391 custom artifacts,38 boundaries with114 total artifacts
(38 primaries+76 companions),505 first providers,zero refresh**.
FirstNorm and all ordinary/native/current-data guides are references only,
so their much wider import closures are not loaded. No Foundation build.

The read-only auditor rehashed4,679 observations across997 paths, including
both accepted ROOT supplements and their complete manifests, the accepted
IntegralSolution supplement applied only in memory, every reachable current
source/header/object, all overlap source/object equalities, all boundary
sources and first provider artifacts, and pinned compiler. It created only
the JSON inventory, no overlay. Historical package provenance qualifications
remain; matching hashes are not a new proof replay of dependencies.

ROOT Index provider: `/tmp/arithmetic-pell-index-divisibility-root-imkszv7b/lib`.
ROOT Residue provider: `/tmp/arithmetic-pell-residue-classes-root-er_y8ywe/lib`.
Inventory SHA256:
`d208392a2a3b6c4f32d2525b242c13adc588d3af9fce2e5579a4476bf883ad1b`.
Exact source/object pins and505 mappings are in the inventory; the auditor
and plan are additionally pinned by the standalone plan manifest.
Any later authorized compiler remains two fresh private regular leaf
outputs at `-M6000 -j1 -DElab.async=false`,512MiB reserve, with all attempts
and both source snapshots retained. No implementation is authorized here.
