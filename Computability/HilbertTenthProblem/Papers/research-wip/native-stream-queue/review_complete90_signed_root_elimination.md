# Independent review of the complete90 strong-root elimination

PASS, with no requested correction. The frozen source computes a complete **90=52M+38A** polynomial with **17 positive witnesses**, ordinary positive input and exact total degree **406** on every inherited valid fixed-program slice. Deleting f gives a bijection from the complete positive zeros of the actual84 parent to the new zeros, preserving every retained supplied coordinate. The inverse restores the unique positive f. This conclusion uses the separately reviewed, source-specific signed-T positivity theorem; the field-norm algebra alone would restore only a signed integer f.

## Frozen files and actual checks

Author stem: `complete90_signed_root_elimination`.

| File | SHA256 |
|---|---|
| Author PY | `5f41f627ef6649b7dc975f3500f99ede576b156fd787423408b2433a1cd0170c` |
| Author JSON | `ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22` |
| Author MD | `52211f6ab29781ea23a1fe07d8644f4012ca4740658b4e1f42b618a5fc0fb8ec` |
| Reviewer PY | `f70049f07c1739108922825d2ca6e2eb3d43a4bee3b35fb27191d0626b69795d` |
| Reviewer JSON | `5a91c0addaf2f32e85524592ac07381c1327af0017c4c9b7663e1c67595ba423` |

The reviewer authenticates the complete author trio and all ten pinned dependencies as inert bytes. The actual parent JSON is `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. I read the full author helper and proof, including the final positive-reconstruction addition, and the complete actual84 row array. I separately reviewed the signed-T theorem in `review_complete84_signed_quotient_soundness.md`, hash `e392d0c0c904d64a007234ec2a2759921ac6bbb1f2ca058539c15dd6705486f8`.

The fresh reviewer independently propagates dependence on f through every parent row. It reconstructs the new array as all67 literal independent rows followed by the stated23 charged rows, and checks all90 rows against the frozen author array. The cost is36M31A retained plus16M7A appended. Full topology and reverse liveness checks find no dead operation or unused supplied port. The input, six fixed numerals, positive domain and every witness other than f remain unchanged:24 total supplied ports, of which17 are witnesses.

Exact exponent-vector polynomial arithmetic proves the full57-term new field norm, the14-term normal form of the complete old output modulo `f²−D`, and the actual integer-D and denominator cones. These calculations expand the dependent producers c², S and Q and both complete finalizers. The only exterior cuts are the unchanged f-independent values Delta,c,R and the three already-paid factor ports; the67 literal-row comparisons bind them to the actual source. They are not unrelated free replacements of dependent auxiliary quantities.

## Integer-domain and sign proof

Write `D=1+Delta*i²*c⁴`, `Q=(Delta*i*c²)²`, `b=c+R*D` and `P5=norm_triple*norm_index*norm_transport`. The source pays D directly as `1+(i*c²)*S`. No division by Delta or supplied square root is hidden in the ledger.

The retained positive domain gives `D>c>0`, independently of any zero. Thus integer R cannot make b zero: nonnegative R gives b>0; R<=−1 gives b<0. Consequently `B_rat=2Q cT b` is nonzero even before the outer packing is typed. This avoids a circular appeal to R>0 or to native soundness.

The whole new polynomial is `alpha²−D*(P5*B_rat)²`, with `alpha=P5*(A_rat+1)−1`. At P5=0 it equals1, so a new zero permits the rational inverse `f=alpha/(P5*B_rat)`. Its square is the integer D; the lowest-terms argument therefore makes f an integer, and D>0 makes it nonzero. The exact old-output normal form then gives an old zero on the same retained coordinates. No positivity or divisibility is silently supplied by the algebraic inverse.

Conversely, at a signed-f parent zero, the full Delta factor cancels because Delta>0. The normalized strong factor is an integer unit. Since Delta is0 or3 modulo4, the negative unit is impossible, even when f is signed. Thus f²=D, and the exact quadratic norm vanishes. This also excludes f=0. Both implications hold without assuming an auxiliary-root sign.

The additional positive-domain conclusion is correctly separated. The actual direct consumers of f are exactly f² and Tf, and T occurs directly only in Tf. Negating both preserves every computed value. If the restored f were negative while the retained T is positive, that symmetry would produce a positive-f, negative-T zero with all other witnesses positive. The pinned signed-T theorem excludes precisely that tuple on the full valid compiler recipe. Hence the restored f is positive. The nonzero denominator proves uniqueness, so the result is a bijection of positive zero sets, not just equality of ordinary-input projections. Parent universality now transfers without replacing any native witnesses.

## Uniform degree and scope

The reviewer independently expands both actual norm cones, proving their six-term cancellation formulas rather than importing their degree numbers. It then propagates the highest homogeneous polynomial through all90 rows with fixed numerals of degree0. It reproduces retained factor degrees22,18,32,7,2, so P5 has degree81. Crucially the literal R has degree4; degree7 belongs to the separate index factor.

The computed degrees are `Q=46`, `D=34`, `b=38`, `L=173`, `M=203`, `Znew=129`. M uniquely supplies the degree203 part of alpha; `4LM` has degree376. The full degree406 leader is

    1024 h² (rho+sigma)² delta⁴ i¹² (eta+zeta)³⁰ w³⁶ s⁶⁶
         Q0²⁴⁶ (Q0−F)⁴ Ttransport².

Independent expansion gives7,533 terms. The coefficient of

    Jrep²⁵² h² rho² delta⁴ i¹² eta³⁰ w³⁶ s⁶⁶ transport_quotient²

is `1024*Bm1²⁵²`, nonzero on every valid slice. Thus406 is attained uniformly;426 is only the naive uncorrected degree bound.

The writer and fresh normal and optimized reviewer replays from `/` passed against the final pinned author trio. No author or predecessor helper was executed/imported. Author numerical diagnostics were read but not rerun; the independent checks above are exact source/algebra calculations, not sampled histories. No enormous native fixture or proof-assistant certificate was constructed. The existing compiler and signed-domain theorems are explicit mathematical dependencies. This gives one17-witness tradeoff, not an operation improvement over84, a minimum-witness theorem, unrestricted signed-zero equivalence or a generic elimination compiler.

Portable replay after installation:

```sh
python3 /absolute/path/review_complete90_signed_root_elimination.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/review_complete90_signed_root_elimination.json
python3 -O /absolute/path/review_complete90_signed_root_elimination.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/review_complete90_signed_root_elimination.json
```

For staged author files, `--artifacts /absolute/staging/directory` overrides matching dependency files. All hashes must still match; the helper has no required `/tmp` runtime dependency.
