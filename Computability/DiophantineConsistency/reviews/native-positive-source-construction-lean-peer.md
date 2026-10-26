# Positive source construction: independent Lean review

PASS. Reviewer: `complemented47_review`; author: `circuit_reduction`. No
mathematical or source-binding correction is requested. I read all253 main
lines and all75 check lines, the complete author receipt, the full279-line
outer-seed source,217-line fresh-private-seed source,254-line Carrier66
source,418-line canonical source map,112-line rank module, the full
FirstPellCarrier witness map, and the actual Carrier65 coordinate/core and
polynomial-evaluation definitions before replay. I also inspected the
literal22-row source definition used by the restored31 coordinates.

I did not author this packet, its outer/private seeds, the canonical parent,
the first-Pell carrier, or the source map. I authored earlier cyclic carry,
tile/geometry, controller, and the recent conditional halt-packing wrappers
that will supply the scalar data. This review is independent of this new
arithmetic construction, not of all eventual application prerequisites.

| Frozen source | SHA-256 |
|---|---|
| `NativePositiveSourceConstruction.lean` | `f96ba070ef8dac85ea4d63cf687efbee7b9f75f65e35ef498c9c028551bacf5d` |
| `NativePositiveSourceConstructionChecks.lean` | `3188d7772aef474c097901877d1acc6e1773bb7a6cbbccd35cba998065290f97` |
| `NativeOuterSeedConstruction.lean` | `fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159` |
| `ThirteenFreshSeed.lean` | `6312b55f52b22306d2f070920bfc1b3002d397ae171b9dbcc9df828087781992` |
| `Carrier66Source.lean` | `c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388` |
| `NativeRankVariation.lean` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |
| Author receipt | `b49ab748d9458be12cc72a5a683425d5858307a14b02781a7ba46df8e046c50e` |

Lean source paths are under `Lean/DiophantineConsistency/`, relative to
`Computability/DiophantineConsistency/`.

`Data p u R` has six positive natural scalars and five concrete arithmetic
bindings: q=2^u, C+F+alpha=q, wq=2^R, the old-z transport equation, and the
exact signed window rank. Neither its transport nor rank subtraction is
truncated. The high-mask input remains p3, the already shifted source port;
`parent_blocks` and the source map introduce no second beta shift. The
temporal product adapter correctly retains u<=R; its focused counterexample
shows why the hypothesis matters.

The parent has precisely the fifteen declared independent coordinates.
Its q,C,X,Y,k,c,a,delta,D and rank are individually identified with the
scalar data and outer seed. In particular X=wq=2^R, and the rank binding
uses the actual `NativeRankVariation.core_rank` identity. The supplied
seed interface contains all outer norms and index equations explicitly;
the population entry points construct that seed instead of asking for it.
R%4=3 gives R=2*(R/2)+1 and positive R. Together with u>0 and the actual
binary population it meets the complete `exists_outer_seed` contract.
No ratio bound, Pell interval, divisibility, or norm is an additional
population-endpoint premise.

The private call is the literal fresh-seed theorem at A=a+2, rank R and
b=1. Its ordinate c is identified through the outer seed's exact
`main_index`; an existing private witness is never presumed compatible.
It supplies positive f,i,T,V and negative y. The new parent uses -y,
which is positive; the auxiliary equation depends only on y squared.
The strong equation multiplied by delta yields Z=delta, while the private
auxiliary equation yields U=1. The outer seed supplies P=Q=index=1 and the
scalar transport supplies W=1. Thus all six canonical factor values and
positive rank are derived. The proof never invokes a desired source zero
or polynomial zero to establish them.

I checked the inherited positivity boundary in the canonical source map.
Its auxiliary gap c*T-R is strictly positive using the canonical index,
Y>=2 and positive coordinates. The strong equation gives f>=2, then V>c>1.
The auxiliary norm with S>1 gives y²-V²>0. These establish the formerly
nontrivial source slots, including8 and27, before taking `Int.toNat`.
Consequently all31 natural coordinates are strictly positive, their casts
are exact, and all22 literal source residuals vanish. The source-row ledger
is a complete algebraic identity; it is not a substituted surrogate system.

For the14-variable endpoint, the canonical drop theorem derives a positive
integer n from the first norm and index equation. Its carrier identity
preserves the complete core, including the first root, rather than only
one factor. The new proof then uses the actual `Carrier65.eval_polynomial`
identity. The surviving slots0,1,2,3,8 retain J,F,alpha,z,w exactly. At the
population endpoint both outer and private witnesses are freshly derived;
only the explicitly stated scalar Data, beta>0, u>0, population and R%4=3
remain. Supplying that Data from the literal packing is separate work,
so this packet alone is not a closed consistency equivalence.

I freshly replayed main and checks sequentially with `lean -M6000 -j1`,
using `Elab.async false` and a private namespace at
`/tmp/native-positive-source-complement-peer-ew5z0ib4/lib`. Both reviewed
object bundles were excluded from the prerequisite symlinks and rebuilt.
`LEAN_PATH` was prepended after `lake env`; checks imported the fresh main.

The replay deliberately used the author's authenticated current
PellRatio90, NativeHalfBinomial and NativeOuterSeedConstruction objects
from `/tmp/native-outer-seed-deps-2i8pllz8`, avoiding the recorded stale
shared Ratio90/Half interfaces. Their object hashes are respectively
`d54f59bc03a0648e360c124e18b7b0585cc98147553312b294a43c0fec67680b`,
`7ef4f6dc18292dc30cdea2f5a8e55228ee38c1d7f5a27319eba8db63a73efbfa`,
and `f15619430cc65f2744cef7ff49cb9cc512a4eaf6cec457b2d8eeba99b241f32d`.
Their source/build provenance is the separately read
`native-outer-seed-dependency-replay.json`, SHA
`b65f0efeab3739c8441ec0620923dae54f3a48777c558222edecf58f93de0905`.
These prerequisite objects were reused, not independently rebuilt here;
root is separately auditing/replaying that seed closure. All other
prerequisites were reused unchanged. This receipt claims a fresh replay
of the two reviewed modules, not of their entire dependency closure.

Both first replay attempts passed. Main18.94seconds, peak RSS3,306,868KiB;
checks3.27seconds, peak RSS3,241,708KiB. Main log is empty; checks contain
only eight axiom reports, all subsets of `propext`, `Classical.choice`, and
`Quot.sound`. Both objects are byte-identical to the author's private
outputs. No new axiom, `sorry`, or `native_decide` occurs in the reviewed
packet. All23 pinned input sources/objects remained unchanged.

| Replay artifact | SHA-256 |
|---|---|
| Main object | `33ccb138518d64b8798e85eb7edaf900d8de420f14e4985f80db1ec7792eba07` |
| Checks object | `84f0fceed0e32aa8f289d9a271e5106e9794b3d69d62525de531669ee30c062b` |
| Main log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Checks log | `75330e05d14923d119529c753c307054978aa67186cd540ee0733804a6fc08d5` |
| Before and after manifests | `4f9c0edea86850b0098e19d2dcc081d4685923394b700a7908cc4269ed7354f1` |
| `REPLAY.json` | `477c6cc99d1494a91cc248304ef82387ebc32d5c8011269c1019739a8a723ccb` |

Only this new receipt and temporary replay artifacts were written. No
source, shared object, existing receipt, central document or Git state
was modified by this review.
