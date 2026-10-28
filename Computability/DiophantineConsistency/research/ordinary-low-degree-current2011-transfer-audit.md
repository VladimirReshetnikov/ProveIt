# Ordinary low-degree fronts at the current2011 ports: transfer plan

This is a read-only source and mathematical audit, dated 2026-10-26. It does
not transfer a historical equation, claim a new Lean endpoint, execute an
incoming checker, or establish an internal HA/ZFC theorem. No compiler was
run. The approved13/178/86 packet remains frozen. The next useful work is
two small source adapters; the substantially harder carrier lemmas follow
only after those adapters have been checked.

## Conclusion and scope

There is no identified coefficient obstruction to using the historical
13-positive88-operationdegree51 and12-positive96-operationdegree70 fronts
at the current complete2011 tuple. The historical derivations use an
ordinary strong norm already covered by `NativePellStepDown`, and the
current masks discharge the same numerical source interface. However, the
historical adaptive-carrier and free-J arguments are ordinary proofs, not
existing Lean lemmas. Substitution of the new ports into a JSON graph does
not prove their transfer.

The best first checkpoint is a generic positive old-source-to-Carrier65
existence map, preserving its five scalar coordinates and rebuilding only
private Pell witnesses. It avoids repeating the current tile/carry/machine
proof and avoids dividing an arbitrary ordinary strong multiplier by the
discriminant. The next checkpoint binds the historical shifted-z source to
that authoritative old-z source by every literal row.

The historical metrics refer to the larger compact44 tuple, beta
`2^590069-1`. They are not current47313-byte formalized endpoints. Conversely,
the current178/86 point is not globally nondominated against those older
variable/operation/degree triples; see
`scaled-norm-syzygy-search/COMPARISON_SCOPE.md`.

## Exact current coefficient interface

`CurrentMaskData2011` defines rho=`2^47`, d=`47*2011=94517`,
beta=`rho^2011-1`, and ports `[beta,K,lowPort,highPort+beta]`.
The fourth port is shifted **once**. `CurrentWindowCarry2011.interface`
specializes `NativeSourceMask.Interface` at the actual K. Its fields give
d>=4, the Mersenne beta, K>=0, the exact low/high ports, both unshifted masks
below beta, low parity, high residue4 modulo8, and total population d.
`CurrentMasks2011.lowPort_four` additionally gives MC%4=2.
`CurrentKernel2011.K_pos` gives the stronger K>0 used in the old text.
Thus the historical bounds 0<MC<beta and 0<MF_source<2beta hold.

The degree86 packet's already checked complete raw ports have the following
hashes; this audit only reads its receipt, and does not repeat that finite
coefficient construction:

| Port | Bytes | SHA256 |
|---|---:|---|
| beta |11815|`a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27`|
| K |11868|`64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`|
| MC |11815|`2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f`|
| MF_source |11815|`5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25`|

The sum is47313 bytes. No compact44 K or mask is mixed into this tuple.

## First proposed checkpoint: positive ordinary source to current zero

Suggested new module `NativeOrdinarySourceConstruction`, importing the
existing `NativePositiveSourceConstruction` and `ThirteenCarrierComplete`.
The central prospective signature is:

```lean
-- Proposed; not yet implemented.
theorem source_constructs_carrier65
    (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    ∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p) = 0 ∧
      v 0 = x 0 ∧ v 1 = x 1 ∧ v 2 = x 2 ∧
      v 3 = x 3 ∧ v 8 = x 10
```

The proof uses the **same** original x and its native rank throughout:

1. `NativeSourceWindow.source_native_window` supplies N>0, q=`2^(d*N)`,
   the repunit J, positive C, C+F+alpha=q, both masks, rank population,
   w=`2^(R-d*N)` and exact old-z transport. Set
   R=`(NativePellBootstrap.nativeRank x).toNat`.
2. `NativePellBootstrap.source_native_rank_ge_twentyfour` justifies the
   rank's cast back to integers. `source_rank_eq_target` binds it to the
   displayed target, which is exactly `NativeRankVariation.windowRank`
   after C=q-F-alpha. This is a ring identity, not a new rank premise.
3. `NativePellScaleBounds.source_binary_exponent_bound` supplies d*N<=R;
   `NativePositiveSourceConstruction.forced_product_of_exponent` then
   gives w*q=`2^R`. `sourceQ_cast` gives beta*J+1=q.
4. **Already available**:
   `ThirteenCarrierComplete.source_rank_mod_four p hi hMC4 x hx hs`
   gives R%4=3 directly from this source's actual low mask. It does not
   require an existing Carrier65 zero or a separately constructed word.
5. Fill `NativePositiveSourceConstruction.Data p (d*N) R` with
   J=x0,F=x1,alpha=x2,z=x3,w=x10,C=gap. Apply
   `population_positive_polynomial_zero`. Both Pell seeds are constructed
   by the existing theorem. Its scalar equalities give the five bindings.

An actual-current corollary can then import `CurrentPositiveZero2011` and
conclude positive literal old-source existence implies
`¬ DiophantineConsistency.ConZFC`. Conversely the existing
`CurrentHaltPacking2011.not_conZFC_constructs_packing`,
`CurrentPositiveZero2011.packingData`, `exists_outer_seed` and
`NativePositiveSourceConstruction.exists_positive_source` already give
positive literal old-source existence. These are existence maps, not
pointwise inverses on the private Pell coordinates. No old compiler
calibration or historical cofinality is needed for this checkpoint.

## Second proposed checkpoint: the exact shifted-z ring adapter

`NativeArithmetic52` imports `NativeQuadraticParent.sourceRows`. That source
has `(K+w)C=F+(q-1)z_new`. The authoritative
`SplitCertificate59.sourceRows` has `(K+w)C=F+(q-1)(z_old-1)`.
They must not be identified by their similar descriptions.

The proposed universal row identity, for any commutative ring R, is:

```lean
-- Proposed; not yet implemented.
def toOld (x : Fin 31 → R) := Function.update x 3 (x 3 + 1)
theorem rows_toOld (p : Fin 4 → R) (x : Fin 31 → R) (j : Fin 22) :
    SplitCertificate59.sourceRows p (toOld x) j =
      NativeQuadraticParent.sourceRows p x j
```

The22 row positions agree; only transport row14 requires the z update.
In particular the rank row13 and the fourth-port shift do not change.
Each row is ordinary ring normalization of the existing literal sources.
Positive new-z inputs map to positive old-z inputs by addition of1.

For the reverse positive map, old-z>0 alone is insufficient. Under the
source interface, `ThirteenCarrierComplete.source_spatial_gt_base` yields
w>q; C>=1 and F<q then give (K+w)C-F>0. The exact old-z transport therefore
forces z_old>1, so z_new=z_old-1 is positive. This derives, rather than
assumes, the subtraction's domain. It is useful to expose this lemma before
claiming positive source equivalence.

`NativeArithmetic52.lift_zero_iff` already binds all22 rows to its7 residuals.
`exists_positive_zero_iff` deliberately retains positivity of **all31 lifted
coordinates**, including V and y²-V². Any later small-front reconstruction
must prove that stronger condition, not merely positivity of16 inputs.

## Subsequent13-positive transfer: what is genuinely missing

The historical free-J88 graph uses positive
`J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma`. Its carrier equations are A0=A1=0;
the tail gives ordinary `(i*c²)²=Delta*(f²-1)` and
`Q*V²-(Q-1)*(V+u)²=1`. Its unit-product extraction is universal modulo4,
not a numerical property of the compact44 masks. The exact current port
bounds above therefore suffice for the following staged lemmas:

* First adaptive carrier: integer square-root division, q³|Y,
  (q-1)|Bt, Bt>0 and C>0. This precedes any restored source index row.
* Main adaptive carrier: Dstar>0, integer D=Dstar/(q²Y), the main Pell norm,
  and q²Y|H(qXY-(k-R-1)). The positive source bootstrap cannot be invoked
  at this point, since its index row is precisely what is being recovered.
* Free-J divisibility: H=4Y(X+1)+3 and q³|Y give
  gcd(q,H)=gcd(q⁵,H)=gcd(q,3) in{1,3}; if3|q then v3(H)=1.
  Consequently q⁴|(k-R-1), even without q coprime to3.
* First/main Pell classification and this congruence give sufficiently large
  indices and c>(a+2)Delta², c>2p, c>2R. The existing generic
  `NativePellBootstrap.main_classification`, `twice_index_lt` and
  `NativePellStepDown.source_index_of_strong` cover the central classification
  and ordinary strong-rank step. The latter explicitly permits signed V,j,o
  and does not divide i by Delta. Its prerequisites still need derivation.
* After p=R, the first index is exactly(R+1)/2, and k-R-1 is a positive
  multiple of4XY². Hence q²Y divides it and q|3X. The free-J main projection
  is initially only X=`2^R` modulo H/gcd(q,3).
* The historical stronger ratio proof, including X=1 separately, proves
  X=`2^R` before claiming q|X. Existing `NativePellPower` has generic ratio
  infrastructure, but its `source_X_ge_sixteen` and source-specific power
  theorem already assume a fully restored source and cannot be used here
  circularly. The new X>=2 ratio and X=1 mod8 argument remain to formalize.
* If q|3*2^R and beta=(2^d-1) divides q-1 with d>=4, then q cannot be
  3*2^e: reduce e modulo d. Thus q is a power of2 and q|X. This is the
  exact additional argument that removes J%3 restrictions.
* Restore w=X/q, s=Y/q³, h=(k-R-1)/(XY), positive old gamma, positive
  transport z_new and z_old=z_new+1, o=f(cT-R), j_source=(V+R)/c, tau
  and all lifting registers. Prove every integral quotient and all31
  positive coordinates before applying either proposed source adapter.

These are all-positive **soundness** obligations. A proof for just the
canonical seeds would not establish them.

## Canonical completeness and the12-positive extension

For **completeness**, use the current same-word packing and actual scalar
Data, not an assertion that historical compact44 witnesses still exist.
`NativeOuterSeedConstruction.Seed` supplies actual X=`2^R`, Y=s*q³,
k,eta,zeta,c,D,tau,h,gamma_old and their exact equations. The current
canonical parent constructed with `ThirteenFreshSeed.auxiliary_exists`
uses b=1; its positive ordinary multiplier is Delta*i. If instead starting
from the13-carrier's b-scaled private witnesses, it is Delta*b*i. These
distinct conventions must not be conflated.

The adaptive gamma is gamma_old-w+(k-R-1)/(q²Y). Its positivity follows
from the positive4XY² multiple, giving the quotient>=4*w*s*q²>w. The first
carrier's independent positive gap is
`r=W*t+tau-ell-k-s`, with `t=q*(z_old-1)>=q`, tau>ell and k>s.
Those fields/equalities must be derived from the current seed. Positive
u=y_positive-V follows from the auxiliary norm and V>1. This gives a
canonical positive88-graph zero; it is not a pointwise inverse on all
88-graph assignments.

The restricted90/51 and100/70 parents are possible intermediate checkpoints:
the current constructed N=`120199^(k+1)` is odd and>1; d94517 is odd, so
J=repunit(d,N) is odd and1 modulo3, hence1 modulo6. This statement concerns
the constructed family only. Free-J88/96 do not need it.

The12-variable96/70 graph adds one substantive theorem beyond the13 argument:
if Q>1 and V is an integer, any rational y with
`Q*V²-(Q-1)*y²=1` is integral. The old proof uses strict descent on |V|
preserving the reduced denominator; no matching generic Lean lemma was
identified in the inspected files. Its resultant reconstruction produces
rational i0,u0 first, then requires this lemma before obtaining positive
integer i=|i0| and u=|y0|-V. Merely factoring the resultant is insufficient.
The polarized tail's2-operation saving is a universal ring identity and
can be handled after the ordinary98-graph transfer.

## Metrics, cache feasibility and recommended order

Read-only JSON parsing confirms the stored13 graph has88 rows
(48*,23+,17−), and the12 graph96 rows(53*,26+,17−). This is not a new
all-gate degree/liveness audit. The historical homogeneous leaders select
coefficients -32*beta^15 and64*beta^18, nonzero at the current beta, so their
ordinary degree argument has no special compact44 coefficient cancellation.
Actual current-port graph materialization would still require its own
complete paid/liveness/leader audit and ports receipt.

The authenticated provider for the small first checkpoint is the frozen
degree86 inventory `/tmp/thirteen-scaled-syzygy-native-g4p5s1dn/inputs.json`,
itself bound to the root97/88 provider and current narrow-native overlay.
A static source import traversal of `CurrentPositiveZero2011` plus
`ThirteenCarrierComplete` selects364 custom modules, all present in its371
authenticated records; there are64 direct package-boundary module names.
All371 current source hashes were rechecked and match. Representative object
pins for the named endpoint/seed/source/Pell modules also match. This is a
cache feasibility check, not a new replay or blanket authentication claim.

Adding the literal shifted-z adapter with `NativeArithmetic52` selects10
custom modules,7 already in that inventory. The3 not authenticated there
are `SelectiveCertificate52`, `NativeQuadraticParent`, and
`NativeArithmetic52`. Before compiling that adapter, authenticate existing
exact-source objects for those3 or read and freshly build them in dependency
order. There is no reason to rebuild Foundation or the current native chain.
The current free disk at this inspection was553943040 bytes, only about16MiB
above512MiB; execution must recheck reserve and avoid copying caches.

Recommended order: (1) source-to-Carrier65 existence bridge and actual
consistency corollary, (2) exact shifted-z rows and positive reversal,
(3) adaptive-carrier early bootstrap, (4) ordinary13/free-J extraction and
canonical converse, (5) rational descent and12-variable polarization.
Only(1) and(2) are proposed as the next bounded implementation scope.

## Source pins

Paths below are relative to `Computability/DiophantineConsistency`, except
the explicitly marked repository-relative path. They pin the actual bytes
inspected, not an incoming source package's executable behavior. Generic
large Pell files were read at the named relevant definitions/theorems;
this note does not claim a new full review of every unrelated theorem.

| Source | SHA256 |
|---|---|
| `candidates/free-j-polarized-positive/source/positive/PROOF.md` | `4ce1e588973c7f703dea6a3c60ce747f6f0416544a522fe408d7d81a78a08dcf` |
| `candidates/free-j-polarized-positive/source/positive/p13_free_J.json` | `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8` |
| `candidates/free-j-polarized-positive/README.md` | `891d8bfc3540f05ef86a5147a6c11f903909cbaf43de783eca349ca87e5df85a` |
| `candidates/free-j-polarized-positive/equation.json` | `2a8da9ac141de5078fbdca96acccab5a7c44f6b39f4bc6063261b29179cb68be` |
| `research/ordinary-unit-products/ORDINARY13.md` | `de53d3340d41f0e24b1dfaaded5f166137d44b563f935fb6a4eddaf3bf395dbf` |
| `research/ordinary-unit-products/README.md` | `8dec2ab7b99257e97cbd3cb9e32f34dcd901e488727f9b7b837943bc5cf1c265` |
| `research/short-unit-products/README.md` | `7fc894e698393663559973eb3476b89552507c17b5c1d19a00532218cd639e70` |
| `con-zfc-diophantine-forms/73-guard-reanchoring/report.tex` | `5ce21924544c1bfebc31a15e3029ed26c0cc8d54ff1fa09afcbe98ffbf61f147` |
| `Lean/DiophantineConsistency/NativeArithmetic52.lean` | `b0cb8b658d200933cc47fc71aee016efd6bdad95a4926b377b794be95b49aada` |
| `Lean/DiophantineConsistency/NativeQuadraticParent.lean` | `6764c7bd216dabaf5338a245817d7297e14f152aa0c033d2b766aba472c38509` |
| `Lean/DiophantineConsistency/SplitCertificate59.lean` | `0b6082b0af3f092f6914263eb1568da1d3730df24032b6c1dff5489875da0a03` |
| `Lean/DiophantineConsistency/NativePellStepDown.lean` | `8fc2fb01654786bf8d7a9e104e84593dc43f74f73de53862ff411433fb482814` |
| `Lean/DiophantineConsistency/NativePellBootstrap.lean` | `351d51db7e438b4c9bb8f80f4146df1e9516704c4e47719e562fb9ce9ed521e4` |
| `Lean/DiophantineConsistency/NativePellPower.lean` | `91048f3de105e4d24677ed7467aba7231654e1dab31c029fbbec579c2fa10ebe` |
| `Lean/DiophantineConsistency/NativePellScaleBounds.lean` | `9a2716b017ebf1fd35042e233a165e80d44924c1a6ce09bb6cbe7f37e1b365b3` |
| `Lean/DiophantineConsistency/NativeSourceMask.lean` | `c92d1ee93dff4e8655005bf73d2cedb6ae95a55819c0a14de76202cd0b2a913e` |
| `Lean/DiophantineConsistency/NativeSourceWindow.lean` | `ed24370b1588e660829c26eefc0439a2ac8a53c7cdba73937c4175244418b09f` |
| `Lean/DiophantineConsistency/ThirteenCarrierComplete.lean` | `5f971560bae4ca88ba157fcb8a398e6f3f0bf418cd70491051c69bb8bf278fc0` |
| `Lean/DiophantineConsistency/ThirteenFreshSeed.lean` | `6312b55f52b22306d2f070920bfc1b3002d397ae171b9dbcc9df828087781992` |
| `Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean` | `201491d6c852eb0d5debf5ed3f852e4a640efe3dae636acd7c77ced3d7edaec5` |
| `Lean/DiophantineConsistency/NativePositiveSourceConstruction.lean` | `f96ba070ef8dac85ea4d63cf687efbee7b9f75f65e35ef498c9c028551bacf5d` |
| `Lean/DiophantineConsistency/Carrier66Source.lean` | `c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388` |
| `Lean/DiophantineConsistency/NativeRankVariation.lean` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |
| `Lean/DiophantineConsistency/CurrentMaskData2011.lean` | `14f32924a514865d4fbd297aac323679c8cfd75305dcc52bb2b588dfffdbdf36` |
| `Lean/DiophantineConsistency/CurrentMasks2011.lean` | `b1ad2349e696f647107b9abbbc2bb092a8a04d1be0e94283b690b52c898bfc8d` |
| `Lean/DiophantineConsistency/CurrentWindowCarry2011.lean` | `2ac2ddb722b7b23c7d528252da28d65486c551dc86d07f22eabbdb19e4a1b39e` |
| `Lean/DiophantineConsistency/CurrentPolynomialWindow2011.lean` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |
| `Lean/DiophantineConsistency/CurrentPackingRank2011.lean` | `bc9a9d22ae0c97817a2e8955819eb6b0c6445d938d59343b777985f55a5193f2` |
| `Lean/DiophantineConsistency/CurrentPackingParity2011.lean` | `78ac7146d33518ee410891d93df7d19384adc2fca5b2970f2a1a090841de99bb` |
| `Lean/DiophantineConsistency/CurrentHaltPacking2011.lean` | `6ed64c4b270ba07ababf8412dfad7ea8d69d7fbcd005f7f403f65fd34b4ead4f` |
| `Lean/DiophantineConsistency/CurrentPositiveZero2011.lean` | `cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c` |
| `Lean/DiophantineConsistency/CurrentSoundness2011.lean` | `1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef` |
| `research/thirteen-scaled-norm-syzygy86/CERTIFICATE.json` | `1e13e6970442a937db8af04ce5755839d1d2ad6446752dfccf21442657f5a507` |
| `reviews/thirteen-scaled-norm-syzygy86-replay.json` | `f17d48e3949967a512155dca3e078a6b8099f6dd83756092046b6c7e90e1d337` |
| repo: `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellHalf90.lean` | `1d737e0cf751e1d5dbca3b4d75a1a66560fd2147f48da638b44d54db158be1a9` |
| private provider `/tmp/thirteen-scaled-syzygy-native-g4p5s1dn/inputs.json` | `3d9c7d34461af3e5de8f1a26aca092eef4a5359562fdf01ba0df75361208ce1a` |
