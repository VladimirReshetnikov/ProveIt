# Independent review: native Grill weak input cone

**PASS. No correction requested.** The weak-cone child removes one multiplication from the complete fixed-program circuit. For program `(0,1,1)`, the native-unit form costs **208 = 93M + 115A**, with 31 positive witnesses and 11 comparisons; the SOS form costs **232 = 99M + 133A**, with 37 witnesses and 20 comparisons. This is a representation of the existentially padded Grill input language for a supplied fixed finite program. It is not a verified universal ordinary-input recognizer or an improvement to the separate 87-operation universal equation.

This independent review covers the full child source, its complete companion proof, all eight displayed complete circuits, the fresh weak-cone geometry and word interpretation, the exact coordinate substitution, source/metadata guards, and bounded semantic fixtures. It does not rerun the historical dependency suites or claim to construct enormous positive native Pell witnesses.

## Authenticated scope

Reviewed author artifacts:

- [Compiler](grill_tag_native_weak_cone.py): SHA256 `8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9`.
- [Author receipt](grill_tag_native_weak_cone.json): `855a973645e93f64d9e61998880bf270d0f048b8a13a4823ea756bf57092695a`.
- [Proof note](grill_tag_native_weak_cone.md), version read: `387e81a4f2ae12be01ba1da04d905d6017e55b974df7b9eb14897a247ce70d27`. Later review-provenance appendices may change that note's hash.
- Actual strong parent [phase-sharing source](grill_tag_native_phase_sharing.py): `760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069`.
- [Period-padding theorem source](grill_tag_padding_period.py): `299acc95d66b60fb7fe2b3e3a85ffd3ec7c77f8c53ce2f11d1b59d9f7d59ba48`; [proof](grill_tag_padding_period.md): `9dde1ba4982fbc2c84c406e46859c125a3c9a93fccb176a159c23ef6399b6d11`.

The [independent checker](review_grill_native_weak_cone.py) authenticates the child and separately loads the pinned strong parent from source bytes before constructing their packets. Its [deterministic receipt](review_grill_native_weak_cone.json) records the complete-source hashes and measured ledgers. It does not trust the child author's identity routine to prove the source transformation.

## Exact complete-source relation

For every reviewed form, the strong source has exactly one occurrence of the multiplication `three_x__0 = 3*x`, followed by `P0 = Z0 + three_x__0`. Both `three_x__0` and the free slack `Z0` have this width row as their only consumer in the entire polynomial source. The weak source deletes precisely that multiplication and changes precisely that width row to `P0 = Z0 + x`. Every remaining complete source instruction is literally identical, including the finalizer and all native rows.

An independent sparse-polynomial calculation verifies

\[
 3x+(Z-2x)=x+Z.
\]

The exact consumer check and induction through the identical remaining instruction sequence then prove the complete identity

\[
 F_w(x,Z,\mathbf y)=F_s(x,Z-2x,\mathbf y).
\]

This holds on arbitrary integer, rational or real coordinates, and indeed in any commutative ring. All 124 residual pairs and all 16 unit-factor instances across the eight forms inherit the same substitution identity. The checker also verifies topological closure, exact equality of the free-coordinate sets, no dead paid gates, the full finalizer, witness/comparison counts, and the propagated degree upper bounds. No input port, scale relation, range row, phase row or norm condition is removed.

The current top-level metadata correctly says `full_polynomial_identity=False`. Historical same-coordinate phase-sharing metadata is under `strong_parent_metadata`. The explicit signed pullback is not advertised as a positive restoration. The positive direction `Z_w=Z_s+2x` is a valid injective assignment map with unchanged complete output, but arbitrary positive weak tuples can pull back outside the positive domain.

A second independent sparse-polynomial calculation uses the actual global-bound residual, with `J` expanded from selector hats. On the **same** supplied coordinates it gives

\[
 R_{\mathrm{global},s}-R_{\mathrm{global},w}
 =-2\kappa xV_fJ.
\]

At every positive zero, the retained global row forces `J>0`; both finalizer theorems force that row to vanish. Thus no identical positive tuple is a zero of both complete sources. This is compatible with equality of their existential input languages.

## Fresh positive-domain argument

The weak source must be justified directly; the signed pullback alone is insufficient. For arbitrary positive supplied coordinates,

\[
 P_0=x+Z_0\ge2,\quad U_f=P_0V_f+x\ge3,\quad
 D=U_f+\mathrm{phase\_initial}+\rho\ge5.
\]

Moreover `U_f>P0`, `U_f>V_f`, `U_f>1`, and `D` exceeds both `U_f` and the initial phase. These inequalities use only positive integers and already hold before native typing. They retain the parent's required `D>=4` precondition and all individual endpoint bounds.

At a zero, the unchanged global row and natural selector hats give `P>1`, `J>0`, `B<=P` and all prescribed bounds. Consequently

\[
  P_0<D<B\le P.
\]

The input-width lane remains separated from the old radix and history lanes and has digits strictly below `P`. The retained native theorem and region separation still give dyadic `P`, the canonical history radix, and `P0 AND (P0−1)=0`; hence `P0` is dyadic. The range/controller/phase rows are literally retained. The initial phase lies below `D<B`, and the chronological phase digits still satisfy the same no-carry path argument. The unit-product norm-sign and positive-restoration arguments retain their positive scale, `q_native>=16` and `F3>=8` premises.

The sentinel equation requires only `0<x<P0`, not `3x<P0`. With `P0=2^ell`, uniqueness of binary concatenation yields the same global word equation `h=w_ell(x)G(h)`. This forces the actual queue to halt at or before the proposed closure length. A possible post-halt suffix is not a claim of legal transitions from an empty queue.

Conversely, an actual halting padded word with `P0>x` supplies the reversed affine path. Choose a dyadic `D>U_f+phase_initial`; the same positive global-slack estimate and native converse apply. No stronger cone is needed. This supplies complete positive witnesses by the existing native theorem, although the checker deliberately does not materialize them.

For language equivalence, append `2m` trailing zero bits to any halting weak-cone input word, where `m` is the fixed program period. The separately proved padding theorem preserves halting and makes the width `4^m P0>3x`. The strong converse then reconstructs a fresh positive history and native extension. This proves equality of the existential positive-`x` languages, not a bijection of their general positive witness fibers or a same-coordinate polynomial identity. If the original closure has a post-halt suffix, use its actual first halting run in this reconstruction.

## Concrete boundary evidence

For program `(0,)`, ordinary input `x=1` and weak width `P0=2`, the one-bit queue `1` actually halts after heads `10`. The independent constructor recovers

```
Z0=1, Vfinal=2, phase_initial=1, height_slack=2,
H_U=129, H_V=65, Shat0=2, Shat1=65,
ZVhat0=65, global_bound=3837,
D=8, B=64, J=65, P=4096.
```

Both emitted modes satisfy all four actual outer comparisons and the exact prescribed semantic AND at these values. Their formal strong pullback has `Z0=-1`. The same-coordinate strong global residual is `−2080`, exactly `−2*8*1*2*65`. Thus an inverse positive assignment cannot be inferred from the polynomial identity. Native fields in these finite fixtures are placeholders, and the checker explicitly verifies that they are **not complete polynomial zeros**. Existence of complete positive native extensions follows from the retained converse theorem. Appending two zeros produces the strong-cone word `100`, width 8 and actual halt time 4.

The bounded semantic census examines 1,008 chronological head words across the eight forms, with horizons 1 through 6. It independently derives 82 positive outer/AND fixtures; 40 use widths excluded by the strong cone, and two contain post-halt closure suffixes. These counts are mode-counted: the same semantic word can be checked in both complete finalizers. The census is evidence for the interface, not a substitute for the unbounded proof above.

## Independent checks and arithmetic scope

The saved checker passes:

- Eight exact complete literal source rewrites, 124 residual-pair identities, 16 retained unit-factor identities, and eight exact same-coordinate global-row polynomial corrections.
- Eight complete paid ledgers and formal upper-degree calculations. The default `209→208` saving is exactly one multiplication and zero additions; all eight forms have the same one-multiplication saving.
- 96 complete integer substituted-output checks, including 48 signed tuples, with 1,488 residual comparisons; eight rational substituted-output checks; 48 positive forward maps and pretyping checks.
- The 82 outer/AND fixtures above, with actual queue simulation and explicit rejection of the placeholder-native tuple as a complete zero.
- 743 malformed-call rejections, 32 defensive-copy checks, one cold poisoned-module check with exact caller-object preservation, and one warm parent-source mutation rejection in a private copy.

The measured full costs are:

| Program | SOS M+A | SOS witnesses / comparisons | Unit M+A | Unit witnesses / comparisons |
|---|---:|---:|---:|---:|
| `(0,)` | 83+108=191 | 32 / 20 | 77+90=167 | 26 / 11 |
| `(1,)` | 85+109=194 | 32 / 20 | 79+91=170 | 26 / 11 |
| `(0,1,1)` | 99+133=232 | 37 / 20 | 93+115=208 | 31 / 11 |
| `(2,0,1)` | 105+135=240 | 38 / 20 | 99+117=216 | 32 / 11 |

Degree entries remain upper bounds: SOS 304,304,484,520 and unit 737,737,1187,1277 in table order. No exact-degree or universal-program claim was added. The general source identity is proved from the literal guarded transformation; the explicitly enumerated ledger and API test scope is the eight forms above.

A fresh deterministic independent replay is run with:

```
/path/to/research-python review_grill_native_weak_cone.py \
  --source /path/to/grill_tag_native_weak_cone.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/review_grill_native_weak_cone.json
```

All paths are caller supplied or sibling-relative; the receipt contains no absolute worktree paths or timing fields. No repository files, original packets, or Git state were modified by this review.

Root independently read the complete source and proof, then replayed both suites in the research environment. Both fresh receipts matched byte for byte.
