# Independent review of synchronized arithmetic certificates

**Accepted at the ordinary mathematical level.** I found no gap in the
shared Pell frame, simultaneous index witnesses, deferred binomial
radix, source reduction, or natural/integer conversions. Both complete
normal and optimized delivery replays passed, as did the additional
independent source, polynomial and contraction checks described below.
Lean remains paused. This review supplies no new kernel proof or
encoded internal object-ZFC derivation.

The reviewed archive is
`docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip`, SHA256
`ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf`.
It contains 89 files. The archive and incoming files were not changed.
Review/replay scratch is `/tmp/proofs62ff-synchronized-review`.

| Equation | Domain | Variables | Residuals | Degree | Terms | Height |
|---|---|---:|---:|---:|---:|---:|
| source895 | Natural | 895 | 773 | 4 | 4,863 | 63,908,265 |
| natural596 | Natural | 596 | 474 | 4 | 7,263 | 63,909,160 |
| natural529 | Natural | 529 | 407 | 4 | 10,782 | 211,184,624 |
| natural522 | Natural | **522** | **400** | **4** | 20,225 | 83,900,628 |
| integer2088 | Integer | **2,088** | **922** | **4** | 26,791 | 83,901,150 |

Here “Natural” means nonnegative integers; “Integer” means unrestricted
integers. Every coefficient and quantified coordinate is literal in the
delivered JSON. All variables occur and every degree is exactly four.
These are direct C222 equations with an inherited ordinary refutation
calibration, not native-window or Jones-polynomial instances.

## The shared frame needs an exponential bound

For all distinct atoms that occur as a power base, exponent or output,
the actual frame imposes

```
W=2+sum(atoms),    Z=z0+1,
A^2-W^3(W+2)Z^2=1.
```

On natural assignments, `W>=2,Z>=1` imply `A>W^2`. Every requested
base n, exponent k and proposed output m is at most W. Its natural
modulus T satisfies `2An=T+n^2+1`; n=0 contradicts this equality, so
base positivity does not depend on factorial or binomial soundness.
The independent syntax audit proves all 27 exponents positive without
assuming their intended arithmetic meanings. The quadratic estimate
already implies `T>m`.

The true power `n^k<T` requires more. The final norm is the Pell norm
at base W+1 and ordinate WZ. Nonnegative Pell classification gives

```
A=chi_(W+1)(j),    WZ=psi_(W+1)(j).
```

The Pell recurrence modulo W gives `psi_(W+1)(j)=j mod W`; consequently
`W|j`. Its positive ordinate implies j>0 and hence j>=W. Therefore

```
A>W^W>=n^k,    T>=2A-2>=A>n^k.
```

The T inequality uses `1<=n<=W<A`. This resolves the strongest possible
soundness concern. A quadratic estimate alone would be insufficient:
W=5,A=26 satisfies A>W^2, but at n=k=5 its T is only 234<3125. That
example does not satisfy the frame norm; it isolates why classification
must be retained. The delivered proof does retain it.

Completeness chooses true outputs of the finite semantic circuit first,
then W. The explicit choice
`A=chi_(W+1)(W), Z=psi_(W+1)(W)/W` satisfies the frame and Z>=1. It is a
simultaneous choice, rather than an unsupported identification of
separately existential frames.

## Simultaneous index witnesses are compatible

There are 22 distinct exponent atoms and 10 distinct base atoms. At the
common A, the index for each exponent is certified separately by X_i,Y_i,
S_i,R_i and its retained index/congruence conditions. One common U,V,B
suffices, with the stronger literal conditions

```
V=(product_i Y_i^2)(v+1),    B=1+4V(q+1),    B=A+Ub.
```

For soundness, Y_i>=k_i>=1 gives V>0, `Y_i^2|V`, B>=5 and
`4Y_i|(B-1)`. All hypotheses of each original indexed-Pell criterion
are restored. Sharing constrains the zero set; it does not weaken an
individual index test.

For completeness take true `X_i,Y_i` and let `L=4 product_i Y_i^2`.
In the finite ring `(Z/LZ)[s]/(s^2-(A^2-1))`, A+s is a unit with inverse
A-s. A positive power is 1. Its ordinary Pell coordinates U,V satisfy
`U=1 mod L`, `V=0 mod L`, and V>0. In particular U is odd. The Pell
norm implies gcd(U,V)=1, so gcd(U,4V)=1. CRT therefore gives

```
B=A mod U,    B=1 mod 4V,
```

with B>A after adding a positive common period. This proves the crucial
common-residue compatibility. Set `S_i=chi_B(k_i),R_i=psi_B(k_i)`.
Polynomial recurrence congruences give `S_i=X_i mod U` and
`R_i=k_i mod 4Y_i`. Monotonicity in the base supplies S_i>=X_i, and
`psi_B(k_i)>=k_i`; every oriented quotient in the actual rows is natural.
The finite ring and its order are proof devices, not hidden polynomial
coordinates or coefficients.

The one-sided power quotient is also justified for all indices. With
`H_j=chi_A(j)-(A-n)psi_A(j)`, the exact recurrence is

```
H_0=1,    H_(j+1)=nH_j+T psi_A(j).
```

Thus `H_k-n^k` is T times a nonnegative finite sum. This supplies the
natural quotient in the emitted equality
`X+nY=AY+m+Th`. For soundness its congruence and the two strict T bounds
force m=n^k. No signed-quotient assumption is silently imposed.

## The deferred radix has a noncircular interpretation order

All 14 binomial outputs are first allocated in the original semantic
macro circuit. The final common radix is

```
q=2^K+1,    K=sum(distinct binomial upper-argument atoms).
```

Soundness proceeds pointwise. First all shared power relations are
correct simultaneously, using only natural assignments and independently
proved exponent positivity. Then K>=n gives q>2^n at every binomial
request. The quotient/remainder rows therefore select the exact base-q
digit `binom(n,k)`, including k>n. Only afterward is induction on the
original semantic macro order used to interpret factorials, modulus
products and the outer source. It does not assume a binomial's intended
value while proving the common power relation.

Completeness reverses this construction: evaluate the genuine semantic
macro circuit, choose q from its actual upper arguments, compute its new
internal power outputs, choose W and A, then extend all shared index and
quotient witnesses. No fixed-point existence principle is required.
The actual ledger and syntax audit match this order and include every
requested power atom and every distinct binomial upper atom.

## The reduced source and its cheap majorant are valid

The original 13 local coordinates become 11 by deleting only the two
remainder slacks and their rows. All seven label/schema parameters are
bounded by m, states S,Sp by y, and beta quotients by x. A finite C222
proof admits such an m before choosing its carrier `(m+1)^t`. Then choose
y above the finite accumulator states and divisible by t!, and construct
the beta code x by CRT. Its canonical quotients are at most x.

For soundness, `S,Sp<=y<1+(i+1)y` makes each retained beta reconstruction
a canonical remainder. Adjacent rows recover identical middle states;
the unchanged endpoints recover the complete accumulator. This does not
require divisibility of y in soundness. That divisibility is only a
completeness choice ensuring the finite beta moduli are pairwise coprime.

The axiom-factor change preserves zero sets. For C=p^2+q^2, an axiom
product of factors `C+d_j^2` plus its guarded bundle alternative vanishes
exactly when C=0 and some unconditional difference or the guarded
bundle vanishes. The factored `C+(product d_j)^2*G` has the same
condition because G is a sum of squares. Modus ponens, generalization
and the accumulator/beta suffix remain unchanged and nonnegative.
This is zero-set equivalence; their polynomial values need not agree.

The majorant is recomputed from the actual nonnegative pair DAG after
factoring. Each of its 388 addition/multiplication gates receives a
verified exponent bound relative to `R=2+t+x+y+m+M0`. The computed
exponent 6,893,159 is rounded up to 8,388,608=2^23. Hence
`H=R^(2^23)` costs 23 squarings and bounds both pair members, the index,
every heterogeneous coordinate bound and its successor. In particular
the range factorials divide H!, are coprime to the CRT product, and
cancel exactly from the binomial range tests. The bound excludes encoded
columns; changing it does not introduce a semantic dependency cycle.

## Contractions and the integer companion

Each contraction is an exact monic elimination `x=P` whose restoring
polynomial has nonnegative integer coefficients. Affine substitutions
preserve quadratic residuals. A quadratic restoration is used only
where substitution still leaves every other residual quadratic; the
complete independent replay checks this directly. Reverse restoration
gives natural preimages. Unused free coordinates are separately listed
and restored to zero. No expression is truncated by a support cap.

The 522-variable integer companion retains all natural residuals and
adds, for every original coordinate, the guard

```
8x+1=a^2+b^2+c^2.
```

It forces integer x>=0. Conversely, for natural x, 8x+1 is positive and
1 modulo 8, so Legendre's three-square theorem supplies its witnesses.
The new auxiliaries occur only in quadratic guards; the degree remains
four. The fresh fourth-power coefficient is 1. Guarding fewer coordinates
would require a separate nonnegativity certificate; this release guards
all 522 and does not assume that metadata alone proves wire signs.

## Provenance, replay and proof boundary

All 27 copied immediate-upstream files are byte-identical members of
the earlier `ConZFC_Shared_Certificates_2026-10-24.zip`, SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
All seven entries of `CALIBRATION_PINS.json` match the actual Git blobs
at commit `08200eb10fde2db408c69dffd840d6920a569b1f`.

I reread the unconditional interface
`KEndpoint.c222_iff_zf_refutation` and the subsequent
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The former occurs
before the machine-parameter section and has no halting/simulation
hypothesis. Its import graph does contain machine-related modules; the
present equation's arithmetic certificate encodes the numerical calculus,
not their machine execution. The latter interface supplies the stated
ZF-to-ZFC refutation transport. This review authenticates and reads their
interfaces and immediate proofs; it does not rebuild the full transitive
Lean dependency closure during the pause.

The source ZIP was safely extracted and all executed scripts inspected.
Only the authored Python audit/release chain and its authenticated
arithmetic/calculus dependencies ran. No Lean, TeX, machine search,
inherited H10 emitter, package installer or network command ran.

Both `python3 -B verify.py` and `python3 -O -B verify.py`, with receipts
outside the extracted package, passed: 88 manifest files, all 22
regenerated JSON files byte-identical, all five exact polynomial results,
and all three deliberately corrupted contraction certificates rejected.
The normal/optimized receipts are embedded in the independent review JSON.

`tools/review_synchronized_certificates.py` imports no delivered module.
Its normal and optimized runs additionally authenticate the two archives
and seven Git blobs, independently replay every natural contraction,
check all 522 integer guards and reconstruct all five complete SOS
polynomials. Its separate arithmetic controls cover 27 classified frames,
1,152 oriented power identities, four finite-unit/common-CRT families,
63 common-radix digits including zero/out-of-range edges, and 16,875
axiom-factor cases. These controls check transcription; the unbounded
arguments above establish the ordinary mathematical transformations.

The resulting ordinary argument is formalizable in ZFC and identifies
zero existence with the inherited sealed syntactic ZFC-refutation
predicate. It does not assume consistency, establish absence of zeros,
or convert an external Lean equivalence into a new internal object-ZFC
proof file. Completion of that formalization remains separate.
