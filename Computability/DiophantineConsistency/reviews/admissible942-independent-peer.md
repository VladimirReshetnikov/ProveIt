# Independent review of the complete admissible942 tuple

Reviewer `/root/controller_certificate`; ordinary proof author
`/root/complemented47_review`; probe/certificate author
`/root/circuit_reduction`; ROOT coordinates the candidate and page.
The reviewer did not change the reviewed artifacts.

**PASS.** I read the complete593-line proof,512-line final verifier,
434-line exploratory probe and probe note. The probe and final verifier
both passed in normal and optimized read-only modes, reproducing their
exact artifacts. A separately authored and fully read stdlib-only script,
importing no project module, decoded the whole seed and action table,
generated every new tile directly, checked the entire index bijection,
reconstructed every coefficient and whole constant, and verified the
changed geometry, phases, masks, controller and rank checks. No gap was
found in the ordinary deletion argument or the new finite premises.

## Exact reviewed versions

Paths are relative to `Computability/DiophantineConsistency`.

| Artifact | SHA256 |
|---|---|
| `research/admissible942-independent/PROOF.md` | `c181f726f07ed1803d4128f8dc739c78af2c5220acba0e0779d4bf33ecb2ded2` |
| `research/admissible942-independent/certify.py` | `cdd9020f6134870063b1cf5feb1e57d85406afe18070f3cf1d56f32711c49262` |
| `research/admissible942-independent/certificate.json` | `f27eebc9e6315291fcd60f07462d133621f117b6c9ce04777987fc2fedf694a2` |
| `research/admissible942-independent/coefficients.json` | `626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f` |
| `research/admissible942-probe/probe.py` | `df3d39b6b235b54ca27f0642d7aa08720957ce7c6a1882b325ac16ffeb7d8b44` |
| `research/admissible942-probe/RESULTS.json` | `471222bcd832cf2554e428f14369c76817709d09b12343d58ebe94dd6a5872a4` |
| `research/admissible942-probe/COEFFICIENTS.json` | `e711e7614932742fb350ccb1438e4e336bc00ac386b586a9460f0f537b2a8d0c` |
| `research/admissible942-probe/NOTE.md` | `48197106e0e7f9142cc001b07573449d52673efe49a153e634576b4253085a52` |

The final verifier authenticates the full new proof and preserved parent
before import. Its already reviewed one-anchor parent is
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`;
the complete radix55 source page is
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
All gates use explicit exceptions, so `-O` retains them. Neither reviewer
run used `--write`. A README in the new independent namespace was not
present during this review; the frozen proof, verifier and probe note are
the reviewed explanatory sources.

## Exact language deletion and marker identity

The map `g(0)=0`, `g(j)=j+1` for1<=j<=941 has image exactly the old
indices other than1. The omitted old tile is `(5,0,0,0)`, coefficient6145.
The prior actual first mask forbids that old selector in every cell.
Consequently the new language is pointwise bijective with the old allowed
language; it is not a newly assumed restriction on computations. Colors,
edge equalities, Start, signal data, periodic/helical seams and cofinal
canonical rectangles are preserved and reflected. Fresh packed words
are encoded after this map; equality of old and new packed integers is
neither needed nor claimed.

I independently parsed all436 base62 seed characters from the pinned page,
decoded all430 actions using explicit prefix sums, and built all new table
families directly. The new table indices are0; j+1 for the430 action tiles;
433−2a+b;423+2r+b;923+2a+b;927/928/929;496+t; and933+3a+b.
The action tile's north color remains j+2, not j+1. These rows cover0..941
exactly, with no duplicate index or tile. I compared every quadruple to
the mapped old quadruple independently recovered from its exact retained
selector coefficient. In particular initializer928 is `(3,436,4,4)`,
Start remains0, and new941 is old942 `(4,437,2,437)`.
The full new tile-list hash is
`8ac6dabe3485f8c29fe15fdb9f98a8f57823be532d01e12bcbdc43b04a95874c`.

Replacing `t^34*(2-t)*x^1005` by `(2-t)*x^1005` preserves the complete
specializations at t=1 and t=2 for every x: their marker coefficients
are respectively1 and0. Only these two specializations occur in the
four fixed constants. Thus this recipe simplification changes no port
within the new942 tuple. It is not a bivariate polynomial identity for
arbitrary t. The final verifier checks both specializations explicitly;
the exploratory probe's longer term gives the same full constants.

## Count, masks, alignment and native argument

There are942 selectors and34 weighted labels, hence976 nonzero
coefficients. Adding the Boolean dummy977 and zero-weight marker1005
gives978 physical positions. MC clears every physical bit; there is no
forbidden new field and no exceptional +rho term. New selector1 represents
old selector2 and is allowed. The actual lowest field still satisfies
`MC mod rho=rho-2`, so `(MC+1) mod rho=rho-1`; the first mask forces
`C=1 mod rho` and therefore Start at the origin. Removing a restoration
at field1 does not alter this binary low-field fact. The new dummy accepts
exactly0/1. This distinction between field1 and binary bit1 is essential
and is handled correctly.

The count clause uses `n<=942`, so `n+carry<=971<1024` with global
carry29. Its bit argument therefore still gives at most one selector
and all34 labels before phase recovery. The coefficient sum drops exactly
6145. The Boolean/no-spill phase argument and global29 bound remain valid
at the shifted layout. The full reflection geometry was recomputed, not
assumed invariant under deletion.

South942..950 copies to960..968; west969..976 copies to987..994, with
spatial9 bringing east978..985. The shared bare18 term appears once.
The marker1005 copies selector0. First reflection1007 lies above the
tests; clause centers1992/2998 have gap1006, and their predecessors
1991/2997 are exactly Aadj and `Aadj+c0*x1005`. All absent-source and
foreign-band exclusions hold. The Boolean adjacency bound remains
`Aadj<=2M-1024`, including the now shifted label boundaries and dummy.

The eight Start tests961..968 plus marker1005 first exclude every
nonzero fractional phase. The934 support candidates for the remaining
field offset split into zero,932 multiple-selector contradictions and
offset20. At20, target961 forces new selector941 while target962 forces
south bit0 at942; new941 has complemented south74, whose low bit is0.
Larger surviving offsets force two selectors in one already decoded cell.
The proof uses no prior occupation or marker-value premise.

The marker relation, all17 color equalities, positive-color occupation
propagation, nonzero temporal stride and reverse map g recover the same
retained syntactic refutation. Completeness transports the full admissible
canonical rectangles through inverse g and encodes them afresh. The
Boolean controller subsets leave selectors, colors and shifted marker
intact.

The last product4003 is exactly `c0*x1005`; its reset makes every later
field zero. The105-bit core plus18 full fields4004..4021 and27 bits at4022
gives873 padding bits and978 native tests. MC population is d−978,
with origin residues unchanged and the source-mask shift exactly beta.
All scalar boxes, strict native bounds and actual mask populations are
proved anew. The rank uses populations `(d-978)N+1` and `978N+1`, hence
`pc(R)=3t+2`, and retains residue3 modulo4. Ordinary safe increments use
dummy977, with exponent bounds3975/986/977; degree-plus-one margins
justify the three-term bound and exact ordinary rank increment.

The controller proof is applied to the new K and actual rank. Its orbit,
safe-index subset and full positive transport construction remain valid.
Both complete positive P66 witness maps are restated. The15-variable,
66-operation, degree157 front is the retained uniform symbolic fact at
the new ports, without identifying it with the old specialized polynomial.

## Independent finite checks and whole integers

The independent reconstruction compares every one of3297 coefficients to
both the probe and final artifact. It explicitly forms the full support,
every copy/clause/predecessor, the entire zero tail and all4027 possible
field offsets. The Boolean convolution maximum is3829914518400942,
6145 below the predecessor; all carry/reset checks pass. It reconstructs
the closed MC and positive padding sum independently and checks every
complete integer against its certificate hash.

Beyond the verifier's1/2/3-cell rank samples, I checked a four-cell
mask-compatible word containing new selector1 in a later cell and a
Boolean dummy in another cell. Its actual masks, two rank identities,
population and residue all agree. This checks the changed mask algebra;
it is not asserted to be a canonical tiling. The zero-weight-marker
omission negative control still rejects the full physical geometry and
population. The marker1004/offset19 pattern is correctly scoped to a
local obstruction, without claiming a full native witness or global minimum.

Trial division independently verifies47,4027 and246929 prime. Orders
of2 andB are23 and1342=`2*11*61`, with every proper-order test included
and both orders coprime to d189269. Spacing30866 and
`lambda=246929=8*30866+1>d` satisfy the complete progression condition.

| Modulus | B | K | B squared | H |
|---|---:|---:|---:|---:|
|47|4|17|16|38|
|4027|3596|452|519|3031|
|246929|104077|148485|234415|56296|

Termwise and whole-integer modular routes agree. The valuation-one lift
is45579142537=`1+246929*184584`. All required units are verified for
the actual new K, discharging Pca942.

| Port | Bytes | SHA256 |
|---|---:|---|
| beta |23659|`236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70`|
| K |23712|`930a43cdefe8e92f6f9761d84a1eb04f262ca6baf0a3d5494e7db4a7e338179e`|
| MC |23659|`84ae3c5b5cca2284ecfb4d9504804e45a7031120da900ebc300ad77f021d5cab`|
| MF_source |23659|`4b67d5768954dfbeb6d5cf02d26e42fad7bea6d12269802275d65dd6bf14e77b`|

The total remains94689 raw bytes. The intended gain is the complete
printed recipe; a page/rendering review must measure it separately.
This review establishes no actual unsolvability, consistency decision,
global minimum, new native compiler or formal-kernel/internal-ZFC replay.
The complete ordinary equivalence retains the named arithmetic,
syntactic-refutation and foundational contracts; its exact new finite
controller premise is discharged above.
