# Whole-tuple compatibility for the split116 candidates

The `compact57/`, `compact54/`, and `compact54-sharp/` directories are separate candidate instances
of the report59 split116/free-coordinate architecture. Each must contain its
own complete native tuple, regenerated packed coefficients and scale leaves,
and validation receipts. No delivered report59 equation is changed in place.
This note establishes ordinary mathematical compatibility of the coefficient
interfaces. It does not assert a new Lean native-compiler theorem or an
object-language ZFC derivation.

## Pins and authoritative source

The proposal collection is pinned to
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The exact input archive blobs are
retained at arrival commit `7331974b69` and authenticated by the generator.
The raw archives have the following SHA256 digests:

| Input | SHA256 |
|---|---|
|54, `con-zfc-calibrated-carry-4b4349064a.zip`|`e8045da2c6a33b84a51cfb7fa543fb5ccd1db857d283af5094a89f09ec6be2be`|
|55, `con_zfc_congruence_norms_2026-10-23.zip`|`83e9ff8c09deb57a93fcd8a7094f2d4a37f17618ad26a7ff7a403ca6aaea942e`|
|57, `ConZFC_Separated_Degrees_2026-10-23.zip`|`d495c1e4121d16117b14b7f298780702a638c373a2609f23a90f904ba08aef02`|
|59, `ZFC_Diophantine_Degree_Separated_2026-10-23.zip`|`68e5cf243341e41ba0555a53eb1110fa987babb3194241b9c005ddd7aba9d702`|

The authoritative input is report59's `nine_free_adjunct/data/parent_source.json`,
SHA256 `1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
It has 31 positive coordinates, 22 quadratic rows, and the **old** positive
transport coordinate. Report59's `nine_free_adjunct/PROOF.md` has SHA256
`763408bbf9ee9009902ec81091d49115f985fd03db75a1bcf7635479ef1ebaaa`.
Its two source row operations are rho14=r14+r2 and rho15=r15+r3, with the
remaining rows unchanged. These invertible row operations preserve every
common zero, independently of the native ports.

The copied `source_system60.json` is auxiliary provenance. Its shifted
transport convention does not override the authoritative `parent_source.json`.
The candidate generator must preserve the latter's old-z equation exactly:

```
q=beta*J+1, C=q−F−alpha,
(K0+w)C+(q−F)−z*(q−1)=1.
```

## Complete instances

| Instance | beta base | Port bit lengths beta,K,MC,MF_source | Native raw bytes | Safe H exponent | kappa |
|---|---|---|---:|---:|---:|
|compact57|B=2^590069|590069,592884,590069,590070|295388|1182955|1182967|
|compact54|B=2^429959|429959,434054,429959,429960|215492|864015|864027|
|compact54-sharp|B=2^429959|429959,434054,429959,429960|215492|864014|864026|

All three instances use beta=B−1, K0=DC+B*DR, and
MF=MF_source=MF_native+B−1. The last shift occurs exactly once. All four
native bytestrings must come from the selected single instance.

57 calls its instance `wang943-checksum67-shared-anchor-length8807-prime581197`.
Its four materialized raw hashes coincide exactly with the source44/report52
compact tuple; the different checksum/complement naming does not denote a
new bytestring. Its original binding SHA256 is
`b3741e8726b41529fd1c6bdcefe5bd8311cfc4b43c8273442f126c36ec233e0d`;
its coefficient-interface proof SHA256 is
`05783cac0892b584880ce4e57100aa67e7d1fb54f69c242ea4864357b8104d7d`.

54 selects `complemented-factorized-receiver-89x4831`. Its original binding
SHA256 is `feb51765de4225e02efde070e71562bdb219fc118f8985e1464984f3571ccbe0`.
Its native proof, `native/INHERITED_SEPARATED_PROOF.md`, has SHA256
`7893677f6da11ab32aba5bba759236962de5e18c9465702a8b421d131a6dc38a`.
The original 54 binding identifies source pin
`4b4349064a750ba6347293b55874a7f92abdd0db` and archive Git blob
`143a1487c8c28aac7e14c6e723a763040c508d0b`.

## Why the 54 interface applies to the old-z source

The54 native proof is a complete interface adapter, rather than only a
canonical path through report52's shifted source. Section4 proves soundness
from arbitrary native assignments: the receiver decoder rules out nonzero
payload in empty cells; two distinct temporal anchors recover whole-cell
alignment; occupancy and complemented-label matching recover the marked Wang
language; the inherited language theorem extracts a blank K215 halt.

Section 5 supplies the converse for every finite blank halt. Independent helical
padding and the actual-rank controller choose sufficiently large widths/heights
that are powers of the odd prime 106261. Boolean changes in safe dummy cells
adjust the actual packed rank to the required temporal rotation while preserving
labels, origin constraints and positive slack. In particular, the interface has

```
B=2^d, d=429959>=4,
0<DC<B, 0<MC,MF_native<B−1,
MC=2 (mod4), MF_native=4 (mod8),
popcount(MC)+popcount(MF_native)=d.
```

The canonical exponents are odd and cofinal. The low-origin condition gives
C=1(mod4), and hence the canonical rank R=3(mod4). The exact native mode count
and support size change, but these recovered arithmetic/interface properties do
not depend on retaining 943 separate selectors.

The direct old-z31 adapter is explicitly supplied in 55's
`native/SOURCE31_ADAPTER.md`, SHA256
`7144fb46281de8e6e295f0db84d60bb66ab69401285c82fb721bb2ced981c2f6`.
Its historical package31 coefficient choice is separate from the following
coefficient-independent argument. The source definitions reconstruct

```
X=wq, Y=sq³, E=XY, a=E+Y, c=(eta+zeta)Y+eta,
Delta=(a+2)²−1, D=X+ac+gamma*(4a+3), I=i*c².
```

Its norm/index/quotient equations give the ordinary strong kernel and exact
congruences V=of−c≡−c(mod f), V=jc−R≡−R(mod c). The old transport equation
already forces C>0, since

```
(K0+w)C=F+(z−1)(q−1)>0.
```

The usual bootstrap and ordinary strong-rank theorem therefore apply under
exactly the mask/port bounds above. Rank recovery supplies c²|(f²−1), after
which the displayed congruences give the auxiliary index step-down and the
same native masks. This does not cancel Delta informally in
I²=Delta*(f²−1). If desired, the positive old quotient
T=(o+Rf)/c is restored only after that divisibility is proved.

Conversely, the native/Pell completeness construction gives positive canonical
V=of−c=jc−R>1 and y with the auxiliary norm. It follows that

```
g=y²−V²=(V²−1)/(I²−1)>0.
```

The other auxiliary source coordinates are explicit positive arithmetic
registers, giving a positive old-z31 zero. Thus54's whole native interface and
the coefficient-independent old31 adapter compose in both existence directions.
There is no new z_old>=2 premise: that restriction is needed only when changing
to 52's shifted positive coordinate z52=z_old−1. Neither candidate makes that
change. The separate old-z/52 boundary is recorded in
[the arithmetic review](../../PROPOSAL_REVIEW_WAVE8_ARITHMETIC.md).

## Required regeneration and checks

The following are part of constructing either candidate, rather than optional
consequences of the whole-port substitution:

1. Preserve the authoritative old-z parent, its two row operations, the 31
   positive coordinate order, and the split116 isolation certificates. Rebuild
   all 89 weighted source records and all three kernel coefficient lists from
   the chosen four native integers.
2. Check the absolute height of each actual weighted record. The safe bound
   H=4*2^beta_bits*2^K_bits gives the exponents in the table. Both actual 89-record
   checks were completed by the candidate generator; the saved receipt must
   accompany any claim about the emitted instance.
3. Set a=2^kappa=4096H. Regenerate the outer threshold leaf
   c=2^(8*kappa−11): exponent 9463725 for 57 and 6912205 for 54. Reusing the former
   original31 threshold would change the population/divisibility predicate.
4. Rebuild every derived fixed leaf and the complete 473-operation circuit.
   Check complete liveness, the source extraction/isolation identities,
   the strict range estimates under g<4bB^116, and the exact population threshold
   N²|binomial(2R,R) iff the source masks are disjoint.
5. Establish the exact degree using an analytic upper bound plus a nonzero
   leading coefficient at the actual rebound integers. Regeneration or modular
   spot checks alone do not prove a degree upper bound or the unbounded semantic
   equivalence.

The architecture's numerical Jones ratio proof is source-parametric. Rebinding
the source and scale does not add a Sun interpolation dependency to this
nine-positive construction. The inherited native/Pell and K215/refutation
proofs remain mathematical inputs. A kernel-checked calibration of these native
ports, and an internal ZFC derivation of the final biconditional, remain distinct
formalization obligations.


## The sharp 54 scale

`compact54-sharp/` keeps the whole 54 native tuple and old-z source unchanged.
Its smaller height certificate factors record c007 as

```
c007 = 2*beta*(K0+1).
```

For beta<2^429959 and K0<2^434054, with nonnegative ports, integer discreteness
gives K0+1<=2^434054. Hence c007<2^864014. The other 88 actual records also satisfy
this strict bound; their original termwise box estimates already fit it. This
saves one bit from H while preserving all four native integers and the three
kernel coefficient lists. The regenerated scale is kappa=864026, which is even,
and the outer leaf becomes c=2^6912197. Even kappa causes no parity assumption in
the split-mask population calculation or the ratio construction. The separate
sharp instance has completed its generator and verifier replay; it does not
replace the wider-scale instances or their historical receipts.

The checked `SplitKernelData59.records0_lt`, `records1_lt`, and `records2_lt`
prove the stronger generic bound 2*Bcap*Kcap under the supplied box assumptions.
`kernelBounds_box` combines these actual89 recipe bounds with the three degree
ceilings and leading coefficient1; its axiom audit uses only Lean's standard
propext, Classical.choice and Quot.sound.
That formal certificate is separate from the native calibration and must not be
read as a proof of the omitted compiler-to-refutation bridge.
