# Independent audit of paid literal-ant initialization

## Decision and exact scope

**PASS, conditional on the frozen literal interface and inherited 174-operation history theorem.** No mathematical counterexample or correction was found in the fixed-length initialization family or its fixed outer wrapper. The uniform wrapper does not itself certify the raw binary-to-radix dilation outputs. This audit does not assert a combined universal arithmetic count.

Reviewed stable author sources:

- `literal-ant-initialization-bridge-20261003/PROOF.md`: SHA256 `f37fe7543af071d08d74ee6afadf0b8525070caa02bf8a24929164af97e47fc7`
- `literal-ant-initialization-bridge-20261003/bridge_dag.py`: SHA256 `08491ae6aaf2084c948276c383d37a28bb3c05376db98157b9831b1bb634c2d6`

Both are copied under `.uniform.reviewed` names in this independent directory. Earlier snapshots are retained solely to make the audit chronology explicit. The author’s files and frozen sources were not modified. No upstream program or saved arithmetic schedule was executed. The only executable source imported from outside this independent directory was copied new bridge code, inspected in full and interpreted with our own bounded interpreter. No upload or repository action occurred.

## 1. Geometry, phase, and finite-prefix converse

Write `u=481238074400`, `v=576000`. The parent establishes `W=3^w`, `Wp=3^(w-1)`, `Q=W^h`, odd `w>=3`, even `h>=2`, north-facing even-index initial position, and a history that cannot cross a board edge.

The first bridge equation forces `(3^u-1)|(3^(w-1)-1)`, hence `w-1=au`. The positive `HorizontalExtra` means its increment is at least two, excluding `a=1`; therefore `a>=2`. Conversely the required extra is `sum_(s<a)3^(su)-1>0`.

Positive `H` with `H^2=Q` must be `W^(h/2)`. Divisibility by `W^v-1` then forces `h/2=kv`. The padding equation `H=P*G^(n+1)`, with `G=W^v` and `P>0`, forces `k>=n+1` and uniquely `P=G^(k-n-1)`. At the minimal padding boundary `P=1`, so no zero witness is improperly required. `K=(G^k-1)/(G-1)>0` throughout.

The initial head is `3^u*W^(kv)`, exactly board cell `(u,kv)`. Its flattened index is even because both `u` and `v` are even. Board width `1+au` is odd, height `2kv` is even. The affine transformation `(a,b)->(b-75+u,288650-a+kv)` is an orientation-preserving quarter-turn followed by translations by integer multiples of the two normalized periods. It preserves the frozen accepting residue `(481225262775,29948,E)` and maps the start to north at `(u,kv)`.

The anchor bounds become `u-219<=x<=u+1` and `kv-550<=y<=kv+33`. The right marker gives the minimum input ordinate `kv-v(n+1)+23945>=23945`; every other input change is higher. Width `w>=2u+1` and height `h=2kv` therefore contain the complete initial support. The frozen global lower bound `b>=-144` gives `X>=-219` for every prefix. With the fixed horizontal translation `u`, increasing `a` handles any finite upper `X`, and increasing `k` handles both finite extremes of `Y`. Thus the symmetric vertical placement imposes no extra restriction on finite accepting prefixes. The converse bounded history agrees with the infinite initialized board by deterministic local evolution and the inherited no-edge-crossing relation.

## 2. Periodic rectangle without a false width divisibility premise

For a row tile of width `u`, `Hx=sum_(s<a)3^(su)` repeats its ternary Boolean digits in disjoint intervals. `Wp=3^(au)` supplies one additional copy of the tile’s first column, exactly completing width `au+1`. Requiring `u|w` would be incompatible with the odd-width parent; this construction correctly requires `u|(w-1)` instead.

The two row polynomials `A(W)` and `B0(W)` encode the full tile rows and their first-column bits. Since each row has fewer than `W=3^w` possible digit places, multiplication by distinct `W^j` creates disjoint rows. Finally `Hy=K(H+1)=sum_(t<2k)G^t` repeats the `v`-row block exactly `2k` times. Consequently `Hy*(Hx*A(W)+Wp*B0(W))` is the entire Boolean background on the exact rectangle, without row carry. The phase is correct because translating by `(u,kv)` is period-preserving.

The constants remain fixed by the frozen total color function. They are neither existential board colors nor arbitrary input-dependent coefficient ports.

## 3. Anchor and input algebra, including zero-only words

The 2,806-row anchor JSON contains 2,806 distinct physical cells, binary old/new colors differing at every cell, and exactly the stated extrema. Its signed polynomial has exponent pairs `(b+144,289200-a)` inside `[0,220] x [0,583]`. At each pair its coefficient is exactly one of `-1,0,1`; no two anchor cells collide.

After division by `Cbase*P`, an arbitrary anchor cell has exponent `W^(v(n+1)+288650-a)`. Factoring `W^(v-550)*G^n` leaves exactly `W^(289200-a)`. The horizontal factor is correct because `(u-219)+(b+144)=u+b-75`.

A two-cell source field at module `i`, slot `q`, has physical coordinates `(vi+704+24000q,54)` and its adjacent `a+1` cell. Factoring `Cbase*P` gives exactly

`-3^198*(W+1)*W^(v(n+1)+287945-vi-24000q)`.

The two tape fields at slots 13 and 0 become exponents differing by 264000; their common block exponent is `G^(n-i)`. The primary A0 head uses slots 14 and 1, reducing both exponents by 24000 and giving block exponent `G^R`. The right marker is module `n+1`, slot 11, and reduces to `W^23945`. These are precisely the displayed `E,Z,D` formulas.

The anchor already includes the left marker at `(288704,54)` and `(288705,54)`, each changed from one to zero. Omitting a second left-marker subtraction is necessary and correct. Every remaining source field is disjoint from the anchor and from every other field. Conditional on the frozen old-color guarantee, all corrected ternary digits therefore remain Boolean.

The left input is nearest-first, so reversal in the primary tape gives `T=G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j)`. The raw sentinel Horner equations enforce exactly `2^L<=RawLeft<2^(L+1)` and its right analogue. A positive bit adapter gives bit zero at witness value one and bit one at witness value two. The Boolean quadratic admits no other integer bit. Empty words have code one, `T=0`, and `G^0=1`; all equations and head/marker placement remain valid. Zero padding changes the sentinel code and marker module even if popcount remains zero. Changed support is exactly `2812+4(popcount(left)+popcount(right))`.

Signed intermediate expressions, including negative anchor coefficients and `D`, are not declared positive witnesses. Only actual supplied unknowns need positive adapters. `InitialMemoryPlus=memory+1` is positive because the proved final board word is nonnegative.

## 4. Independent operation counts

For fixed meta-lengths `L,R`, `n=L+R`, the literal source has

- `M=2(v-1)+583+3n+Cpow+18`
- `A=2(v-1)+583+4n+13`
- `n+8` equations and `n+4` new positive witnesses

where `Cpow=lambda(v)+lambda(n)+lambda(n+1)+lambda(R)+lambda(575450)+lambda(23945)+lambda(263945)+lambda(264000)+lambda(24000)` and `lambda(e)` counts the actual binary multiplication chain, with `lambda(0)=lambda(1)=0`.

The empty case has `Cpow=138`, hence 1,152,737 multiplications and 1,152,594 additions/subtractions: **2,305,331 operations**. Our independent full stream has SHA256 `448de3b8bf43de32dda5169ec47ae1af2dcdfd457bf828bd2ab399e27c98ef71`.

The conditional uniform wrapper replaces `G^n,G^R,T` by already-certified expression outputs `A,B,T` and obtains `G^(n+1)` by the paid product `A*G`. It has **2,305,332 operations** = 1,152,738 M + 1,152,594 A, six equations, four positive witnesses. Its independent full-stream SHA256 is `f275e8cbab5b1d9bf588a8148ab7e87126cff7e15a352b21164ee60d4178ef6c`.

`Wp` is already a charged parent witness, so reuse is a wire alias. If an attachment exports only `W`, adding `3*Wp=W` would add one multiplication and one positive witness. Neither the parent’s five original positive ports nor the bridge’s inherited ports are silently counted as new witnesses here.

## 5. Huge strict-constant prefix: exactly what is established

The exact prescribed unoptimized source grammar starts from 1 and 3, creates zero, minus one and two, and evaluates:

- `v` ternary Horner strings of `u` fixed binary symbols: `v(u-1)=277193130853824000` gates of each arithmetic class
- 584 signed ternary Horner strings of 221 symbols: `584*220=128480` gates of each class
- independent chains for exponents `u,u-219,198`: respectively 47, 50, 10 multiplications
- the three elementary constants and `Cx=Cu-1`: four additions/subtractions

This gives exactly **277,193,130,853,952,587 M + 277,193,130,853,952,484 A = 554,386,261,707,905,071 extra operations**.

This proof establishes that a fixed finite literal straight-line program has the stated length and, conditional on the frozen color recipe, the stated coefficients. It does not claim that this enormous source, its roughly hundred-billion-digit row numerals, or the dense literal background was materialized or evaluated. Our tests neither call the frozen color generator nor inspect each of its `uv` bit answers. Source generation can terminate in principle without contributing runtime variable arithmetic; it is fixed compilation of an input-independent board. The mathematical frozen-interface dependency cannot be replaced by the finite tests in this audit.

This prefix pays only the bridge’s numerals. It does not retrospectively pay constants used by a dilation relation, parent history, endpoint selector, or an equation-to-one-polynomial transformation. The total is a transparent finite construction bound, not an optimized record.

## 6. All-length composition boundary

The fixed-length family does not become all-length merely because `RawLeft` and `RawRight` are two integers. Both its variable count and source length depend on `L+R`.

The conditional wrapper can instead be composed with one fixed relation proving all of the following on the very same `G=W^576000`:

1. Sentinel-derived lengths and binary typing for arbitrary positive raw inputs
2. `A=G^(L+R)` and `B=G^R`
3. `T=G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j)` with the required left reversal
4. Completeness with positive supplied witnesses, including empty and zero-only inputs

The sibling dilation audit reports such a pair interface, but its proof and ledger are not independently recertified by this bridge audit. A final combined source must substitute its output expressions, not retain `A,B,T` as unconstrained free parameters. A zero `T` is harmless as an expression; a newly supplied `Tplus` would require a separately charged subtraction and witness.

The generated source order matters for an actual combined DAG: emit the wrapper’s `G` chain, then the dilation relation, then dependent wrapper gates, or perform an equivalent acyclic topological remapping. Recomputing `G` rather than sharing it adds 23 multiplications. Output equalities removed by expression aliases change the combined equation count but do not automatically change primitive-gate counts. Any stated total must specify this boundary, all inherited parameter internalizations, the chosen endpoint form, and whether equations remain a system or have been folded into one polynomial.

The witness-free polynomial obstruction is correctly limited: on zero words a polynomial would satisfy `f(2^L)=G^L`; its asymptotic ratio would be `2^degree`, impossible for an odd power of three greater than one. This does not obstruct existential Diophantine recoding.

## 7. Independent checks and limitations

New scripts in this directory provide:

- All 92 frozen-manifest entries checked byte-for-byte against size and SHA256
- 2,112 exhaustive miniature periodic rectangles (all tiles for periods 2x2, 2x4 and 4x2, with four repetition cases)
- 87 width and 1,620 height/padding threshold cases
- 961 exact sparse-polynomial comparisons covering every pair of binary words of length at most four, including all 25 zero-only length pairs, with literal anchor data and board-coordinate bounds
- 192 smaller generated streams with independently checked opcode/reference structure, counts and equality endpoints
- 216 finite-field source-residual comparisons with independently written closed formulas; these use bounded symbolic substitute coefficients, not actual giant background numerals
- Full independently interpreted current fixed-length empty and conditional-wrapper streams, with hashes above
- 216 finite-field wrapper/family comparisons after exact substitutions for `A,B,T`

The stream interpreter stores only its running count, digest, inputs and a small equation list; it never retains millions of gates or expands huge fixed numerals. The finite-field interpreter is restricted to tiny period overrides and length at most five. Neither test tool executes the inherited arithmetic schedule, Pell witnesses, physical program, or ant trajectory. Read-only source inspection plus the frozen mathematical theorems provide the global claims; these finite tests protect the new algebra and ledger against transcription defects.

## 8. Source pins and provenance

All pins below are SHA256 values calculated from local exact bytes. Frozen-manifest consistency authenticates the files against that already-pinned packet; it is not a claim of an independent digital signature.

- Parent note: `9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656`
- Official parent URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5883b08b7af362077f13bb4afa97a23a90ae4cf8/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md
- Frozen interface manifest: `e31de0a0a06b917c60071d500b72dd7891cd74bea103e449685c0041c9b0f615`
- Frozen interface global proof: `a8b4a65ad97a06f3c854a9d133e67dca240d6212749f42ed6c4a92b30318483b`
- Frozen color generator: `20d3cf2c57226910dff679b05a2209f7f6513d62bce824e448e3c94b7dfa5f67`
- Frozen input compiler: `3bf032f5dbf00b2622f4010e702ab9951ad99a3f38f86b7892d4375bc7e8cb58`
- Frozen anchor: `cc67f7c924bcb27ca1c4a48c8d3a630d837b639fbff3032d04515ec1d534ed68`
- Frozen interface v2 ZIP: `70a2a87ddb1ab018ec8c795dad56d053f66855a9b47ab7f3a9b64cf1164b852f`
- Frozen Report40 LaTeX: `c904862c3b9d4be71f1b7598ed2c68a555dc5969441cb0bbeef054724b682f60`
- Frozen Report40 reproducible ZIP: `0c3acc1e36c0931ea490c7526e053ef1bd8a17ad5ea72ec36b97dc4c3548e47e`

The author’s own checker and receipt were not used as substitutes for these independent tests. They remain separately pinned in the final audit manifest.
