# Independent mathematical challenge: eliminating the leaf tag

**PASS, with natural-domain scope.** The proposed substitution and unsquared integer guards give a bijection of complete natural zero tuples with the frozen **terminal-projection parent**. They save exactly `2N−1` additions and remove `N` witnesses without changing the exact degree. The restoration is natural only at zeros; a nonnegative rational counterexample prevents extending the zero-set theorem to that domain.

This is a mathematical and literal-parent-cut audit, **not an audit of the new maintained child's source/API**. It does not import that child or any parent Python module. The [checker](review_eager_tree_leaf_tag_math.py) independently reconstructs a proof schedule from the complete saved terminal sources; its [receipt](review_eager_tree_leaf_tag_math.json) contains the resulting ledgers and evidence. A separate source/API reviewer can compare the maintained emitter against this result.

Authenticated parent: [source](eager_tree_terminal_projection.py), [receipt](eager_tree_terminal_projection.json), and [proof](eager_tree_terminal_projection.md), with SHA256 respectively:

- `edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd`;
- `25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95`;
- `ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b`.

## Exact source-specific correction

For nonterminal row `i`, put `s_i=t1+t2+(t3+t4)`, reusing the actual shared `t3+t4` source register. At the last row put `s=t1+t2`; its other two tags were already removed by the terminal projection. Delete `t0`, and define the integer pullback by `t0=1−s`.

The literal parent has only two kinds of residual consumer of `t0`: its tag sum and its leaf-output row. The checker traces every other residual's complete dependency cone and confirms that none contains any removed `t0`. It expands the actual affine cuts to verify exactly

`tag_sum = t0+s−1`, and `leaf = t0*(z−2y−1)`.

On the pullback the first is identically zero. Replace the second by `(s−1)*(z−2y−1)`, its negative. Squaring therefore preserves its contribution exactly. All other parent residuals are unchanged. Finally replace the removed tag-sum square by the **unsquared** term `s(s−1)`. For arbitrary integer, rational or real retained coordinates, the complete identity is

`Fchild(v)=Fterminal(pullback(v))+sum_i s_i(s_i−1)`.

This is a correction identity, not a full polynomial graph identity without the guard sum. It does not use one-hot equations during source simplification.

## Natural zeros and retained computation semantics

For every integer `s`, the consecutive-integer product `s(s−1)` is nonnegative and vanishes exactly at `s=0` or `s=1`. The pulled-back parent is a real sum of squares even when its restored tag is negative. Consequently at a natural child zero, all parent residual squares and every guard must vanish separately. Each `s` is zero or one, so the restored `t0=1−s` is natural. This establishes positivity **after** the zero argument, without assuming the old natural theorem prematurely.

Because all remaining tags are natural and sum to `s`, they are zero or one, with at most one nonzero. The restored `t0` makes exactly one tag active. Thus the original one-hot conditions and all retained branch/strict-forward pointer-product semantics apply without change.

Conversely, a complete natural terminal-parent zero has `t0+s=1`. Its projection has `s` zero or one, so every added guard vanishes, and the polynomial correction gives a child zero. Projection and restoration are inverse on these complete natural zero sets: `t0` is uniquely determined. This is a bijection with the terminal parent, not with earlier parents that still have free terminal fields or nonunique pointers.

The pullback is not an unconditional map from the whole natural orthant to itself: for example `t1=2` and the other remaining tags zero restores `t0=−1`. Such a tuple is prevented from being a zero by its positive guard. A public natural restoration map should therefore require a child zero, while an unrestricted pullback should be labelled integer algebra.

In fact the new polynomial is nonnegative on all integer tuples, but this does not yield the same **full signed** parent zero set or signed Tree semantics. Over signed tags, a parent's sum-to-one equation need not make each tag Boolean; the new guards impose an additional restriction on the restored `t0`.

There is an exact one-row reverse counterexample: `t0=−1,t1=0,t2=2,a=0,b=1,y=0,z=1`, with `x=program=12`, `argument=0`, `output=1`. Since `F(0,1)=6`, the entire terminal parent is zero. Projection gives `s=2`, so the child has value **2**, its added guard. The checker evaluates both complete sources and confirms the same integer pullback. Thus the reverse proof really needs the parent's natural-tag hypothesis.

## Exact rational boundary

For the one-row child set

`a=b=y=t2=0`, `t1=1/2`, `x=program=1/2`, `z=output=2`, and `argument=0`.

Every supplied coordinate is nonnegative rational. The constructor input is `x=t1*(2a+1)=1/2`; the guarded stem-output row is zero since `F(0,0)=2`; root bindings also vanish. The new leaf square is `1/4`, while `s(s−1)=−1/4`, so the **complete child polynomial is zero**. The restored tag is `t0=1/2`, and the complete terminal parent has value `1/4`. The checker evaluates these full sources exactly with `Fraction`.

Thus nonnegative rational or real cancellation is a concrete false extension, not just an absent proof. Squaring the new guard would avoid this particular sign cancellation but would be a different paid polynomial and ledger.

## Paid count and unchanged degree

Each nonterminal parent tag-sum cone contains five private additions/subtractions. The replacement computes `t1+t2`, adds the already paid `t3+t4`, and subtracts one: three additions, saving two. The last parent's cone contains three such gates; its replacement needs two, saving one. There is one new guard multiplication per row, replacing one removed tag-sum square. Leaf multiplication counts are unchanged. The finalizer still accumulates `8N` terms, now `7N` residual squares plus `N` unsquared guards, so its addition count is unchanged.

The complete saving is therefore exactly **`0M+(2N−1)A`**, as confirmed by independently reconstructed, fully live schedules for all sixteen saved forms. With cleanup indicator `c` equal to zero or one, the new full counts are

```
M = (3N²+81N−46)/2
A = (3N²+(127−2c)N−76)/2
total = 3N²+(104−c)N−61
natural witnesses = 12N−5.
```

The three external `(program,argument,output)` ports are excluded from the witness count. Cleanup-enabled `N=8` gives **955=397M+558A, 91 witnesses**. At `N=1` it gives **45=19M+26A, seven witnesses**.

At `N=1`, the unchanged degree-three constructor/stem residuals retain the leading sum `t2²*b⁴+t1²*(a+y)⁴`, so the exact full degree is six. The changed leaf square has degree at most four and the new guard degree two. For `N>=2`, the root's unchanged third product residual still has leading form `(-1)^(N−1)t03^N(u0+v0)^(4(N−1))`. Its square reaches exact degree `10N−8`; neither lower-degree guards nor other highest homogeneous squares can cancel it. The checker also propagates the full all-fields-equal-to-an-indeterminate polynomial. Its top coefficient remains 17 at `N=1`, and `8*2^(10(N−1))+2^(8(N−1))` otherwise.

## Reproducible scope

The independent helper checks sixteen source-cut/cost proofs and exact degrees, 96 full correction evaluations including 32 rational cases, and 72 genuine natural projection/restoration pairs covering all five rules and padded later rows. It authenticates parent bytes before reading the saved sources, explicitly requires the exact sixteen size/cleanup forms, and records its own source hash in the receipt. These checks support the general mathematical arguments above; they do not replace a maintained-child source/API review or establish an unbounded/fixed-arity universal compiler.

```sh
python review_eager_tree_leaf_tag_math.py --root /path/to/terminal-parent-trio \
  --expect review_eager_tree_leaf_tag_math.json
```

`--output FILE` writes the deterministic receipt; saved comparison is recursively type-exact. All artifacts remain under `/tmp` during review, with no repository or Git mutation.
