# Positive source construction: author receipt

The new arithmetic packet constructs the literal positive fifteen-coordinate
canonical parent, all thirty-one positive natural source coordinates and all
twenty-two source equations, and an actual positive zero of Carrier65. Both
outer and private Pell seeds are derived in the population entry point. The
remaining hypotheses describe a calibrated scalar packing; no source zero,
polynomial zero, desired Pell norm, or old-witness compatibility is supplied.
This is the implementation author's receipt, not an independent review.

## Frozen files and fresh checks

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/NativePositiveSourceConstruction.lean` | 253 | `f96ba070ef8dac85ea4d63cf687efbee7b9f75f65e35ef498c9c028551bacf5d` |
| `Lean/DiophantineConsistency/NativePositiveSourceConstructionChecks.lean` | 75 | `3188d7772aef474c097901877d1acc6e1773bb7a6cbbccd35cba998065290f97` |

Both files were read completely before execution; the final main was read
again after all corrections. Final fresh sequential builds used
`lean -M6000 -j1`, with `Elab.async false` in both files. The main completed
in 18.71 seconds with peak RSS 3,306,112 KiB; checks completed in 3.46 seconds
with peak RSS 3,241,912 KiB. Both logs contain no warnings or errors. All eight
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`
(the exponent adapter needs only `propext`). There is no `sorry`, new axiom,
or `native_decide`.

The focused checks retain all fifteen literal coordinate positions, the
positive sign change of the fresh negative auxiliary ordinate, every canonical
factor, actual source rows, actual polynomial evaluation, and all five scalar
coordinates. The exponent adapter is checked at an ordinary example and at
R=u. The explicit u>R counterexample verifies that its order hypothesis
cannot be dropped. A final check uses the population entry point without
supplying any seed or norm.

## Exact scalar premises and endpoints

`Data p u R` contains natural J,F,alpha,z,w,C, all strictly positive, and:

```
p[0]*J+1 = 2^u
C+F+alpha = 2^u
w*2^u = 2^R
(p[1]+w)*C+(2^u-F)-z*(2^u-1) = 1
windowRank(2^u,C,F,p[2],p[3],J) = R.
```

The transport and rank equalities are over the integers; there is no
truncated subtraction in them. The mask port p[3] is the already shifted
source high-mask port. No second beta shift is introduced. The theorem
`forced_product_of_exponent` derives the temporal product from
`w=2^(R-u)` and u<=R; it does not equate w to an earlier packing multiplier.

`exists_construction data seed hR4` constructs a `Construction` containing
positive v:Fin15->Int and `Carrier66.Canonical p v`, with exact q,C,rank and
J,F,alpha,z,w bindings. Here the supplied seed is the actual `Seed u R`
previously constructed by `NativeOuterSeedConstruction`, and hR4 is R%4=3.

`population_constructs data hu hpop hR4` removes the seed input. It derives
R=2*(R/2)+1 and invokes `exists_outer_seed` from positive u and
`sigma(2,R)=3u+2`. It then constructs the independent private Pell data.

`exists_positive_source hb data seed hR4` returns all31 positive natural
coordinates with every literal `SplitCertificate59.sourceRows` residual zero,
preserving source slots0,1,2,3,10 as J,F,alpha,z,w. The only additional
condition is hb:0<p[0], needed by the existing source positivity theorem.

`exists_positive_polynomial_zero` returns a positive Fin14 point of the
actual `Carrier65.polynomial p`, preserving slots0,1,2,3,8 as J,F,alpha,z,w.
`population_positive_polynomial_zero hb data hu hpop hR4` derives both seeds
and exposes this endpoint directly. Neither endpoint needs a sign condition
on p[1], a finite mask interface, any tiling assumption, or a supplied norm.

## Binding argument

The parent coordinates are exactly

```
(J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,-y,gamma).
```

The private construction `ThirteenFreshSeed.auxiliary_exists (a+2) R 1`
returns positive f,i,T,V and negative signed y. The proof uses -y, which
equals abs(y), as the positive parent coordinate; only its square occurs in
the auxiliary norm. The main ordinate is identified using the seed's exact
`c=psi_(a+2)(R)`, rather than an assumed compatibility of private witnesses.

`parent_blocks` checks the literal Carrier66/Carrier65 definitions and binds
q,C,X,Y,k,c,a,delta,D,rank individually. In particular X=wq=2^R,
Y=s*q^3, and the rank is the actual once-shifted window expression. The
seed's first/main norm, split/index/root equations give P=Q=index=1.
The fresh auxiliary norm gives U=1; the scalar transport gives W=1; the
fresh strong norm gives Z=delta by multiplying its exact identity by delta.
R%4=3 supplies positive rank. Thus every canonical conjunct is established.

The source endpoint uses `Carrier66Source.sourceNat_pos` and
`sourceNat_rows` on that constructed canonical parent. The fourteen-variable
endpoint uses `Carrier66.canonical_drops_to_positive_zero`, which derives the
positive carrier n, followed by `Carrier65.eval_polynomial`. It does not
insert an unproved n or merely a zero of a surrogate system.

## Dependency provenance and reproduction

The direct imports and source hashes are:

| Import | Source SHA-256 |
| --- | --- |
| `NativeOuterSeedConstruction` | `fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159` |
| `ThirteenFreshSeed` | `6312b55f52b22306d2f070920bfc1b3002d397ae171b9dbcc9df828087781992` |
| `Carrier66Source` | `c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388` |
| `NativeRankVariation` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |

This author also wrote the outer seed, private fresh seed, and rank variation
modules, and previously independently reviewed the source map. Their frozen
contracts were inspected again here; this receipt does not claim a new
independent review of those prerequisites.

The build used `/tmp/native-outer-seed-deps-2i8pllz8` ahead of the ordinary
LEAN_PATH. That overlay contains freshly rebuilt current PellRatio90,
NativeHalfBinomial, and NativeOuterSeedConstruction objects. Their provenance
and the prior shared source/object interface mismatch are recorded in
`reviews/native-outer-seed-dependency-replay.json`, SHA-256
`b65f0efeab3739c8441ec0620923dae54f3a48777c558222edecf58f93de0905`,
and `native-outer-seed-construction-author.md`. They were reused here, not
rebuilt again. Other prerequisites were reused unchanged, not claimed fresh.

The direct imported object hashes were respectively
`f15619430cc65f2744cef7ff49cb9cc512a4eaf6cec457b2d8eeba99b241f32d`,
`57dc435923295967bf9477a084ba0733dbac48effe49f1bce561f5efe8c6e1c0`,
`025e5f72642e79ce4ae6d8c9e65eaa5bc4779b412c76adf998460b0266f42d47`,
and `4d73da3692ddee9ed725396f830bf859743bcbfaaf5c90b6341007bd2f8c9232`.

For each new module name M, the final command was equivalent to:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/native-outer-seed-deps-2i8pllz8:$LEAN_PATH"; /usr/bin/time -f "elapsed=%e max_rss_kb=%M" lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/M.lean -o /tmp/native-outer-seed-deps-2i8pllz8/DiophantineConsistency/M.olean'
```

The final main log is `/tmp/native-positive-source-stage3.log`, hash
`fae904a7892d4df5cc700c4d16eba468e88465b5d9d562352a37c1f13f6c4a72`.
The final checks log is `/tmp/native-positive-source-checks-stage2.log`, hash
`60336bde18df6ac0a32141c2ce291c2475321e2d536f011af832c5d8bce60fef`.
Fresh main/check object hashes are
`33ccb138518d64b8798e85eb7edaf900d8de420f14e4985f80db1ec7792eba07`
and `84f0fceed0e32aa8f289d9a271e5106e9794b3d69d62525de531669ee30c062b`.
Only these two new objects were copied to the shared build directory, after
checking the destinations did not exist. No prior dependency was overwritten.

## Scope

The scalar Data premises must still be supplied by the coherent concrete
packing, its controller calibration, and temporal rephasing. Their existence
is not asserted by this generic arithmetic packet. It does not by itself
claim a closed halting-to-polynomial or consistency-equivalence theorem.
No frozen mathematical source, main-page artifact, or existing receipt was
edited, and no commit was made by this author.
