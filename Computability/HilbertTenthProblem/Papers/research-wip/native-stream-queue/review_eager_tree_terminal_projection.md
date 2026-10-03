# Independent review of the terminal Tree projection

**PASS, with no requested author change.** This review covers the complete frozen
[eager_tree_terminal_projection.py](eager_tree_terminal_projection.py), its
[receipt](eager_tree_terminal_projection.json), and its
[proof note](eager_tree_terminal_projection.md). All sixteen saved complete
circuits have the claimed natural existential projection, paid operation
counts, and exact degrees. The public interface preserves the distinction
between this projection and a bijection with all parent witnesses.

The review source is
[review_eager_tree_terminal_projection.py](review_eager_tree_terminal_projection.py)
and its deterministic receipt is
[review_eager_tree_terminal_projection.json](review_eager_tree_terminal_projection.json).
It independently authenticates these author bytes:

| Artifact | SHA-256 |
|---|---|
| Author Python | `edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd` |
| Author receipt | `25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95` |
| Author note | `ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b` |

The three pointer-product parent files are separately authenticated against
their literal SHA-256 pins in the checker. The parent Python is not executed.
The child Python is compiled directly from the authenticated bytes in a private
module; neither its `verify` function nor historical suites are run. Public
API checks use that module, while the rewrite, residual, finalizer, expression,
ledger, and coefficient calculations below use independent reviewer code.
My earlier bounded terminal analysis informed this review; it is not an
executable dependency or substitute for checking the final maintained source.

## Quantified identity and the natural zero argument

For every saved external size `N`, let `l=N-1`. The checker reads the literal
parent membership expressions and confirms that its last three residual
occurrences are exactly `t[l,3]+t[l,4]`, the same expression again, and
`t[l,3]`. Repeated occurrences remain separately squared. Thus a complete
natural parent zero forces both terminal tags to be zero.

The independent expression interner proves the complete identity

\[
F_{child}(r)=F_{parent}(r,t_{l,3}=0,t_{l,4}=0,c_l=c)
\]

with `c` a free symbolic atom, for every retained tuple `r`. This is an
all-value polynomial identity, valid over any commutative ring. It checks
more than the special section `c=0`: no arbitrary terminal `c` survives in
the full output once the tags vanish. The last constructor field appears
only in the discarded tag-four input term; earlier membership tests use
only the last row's supplied `x,y,z`. Last `u,v` were already absent in the
parent. All retained residuals match, and the three deleted residuals
become zero.

Consequently, projecting a complete parent natural zero yields a child
natural zero, and inserting both tags and `c` as zero restores every child
natural zero. Restoration is natural even away from zeros. This proves
exact existential projection over all retained coordinates and preserves
represented `(program,argument,output)` triples at the same external size.
It requires no row permutation and no additional computational assumption.

The restored section is **not** inverse to projection on the full parent
zero set: terminal `c` is arbitrary there. It is inverse precisely on the
normalized parent zero slice `c=0`, whose terminal tags are already forced
zero. Handwritten complete leaf fixtures, including all three available
terminal branch types at `N=1`, and an authenticated parent nontrivial `N=5`
fixture exercise this distinction. For each zero, changing terminal `c`
to `1`, `7`, or `100` keeps a parent zero and the same child projection.
The `N=5` fixture is reused evidence from the parent receipt, not an
independent evaluator of Tree semantics.

## Literal schedules, full ledgers, and exact degrees

The checker reconstructs the arithmetic by substituting precisely the three
deleted coordinates, folding operations transitively affected by those
substitutions, and pruning dead gates. Unaffected constant expressions are
retained, preserving each parent cleanup convention. Subtraction `0-x` is
paid. No general CSE, free constructor, or zero-locus simplification enters
the ledger. The literal output rows and all residual occurrences match the
maintained child, including its full one-square-per-residual SOS finalizer.

The certificate loses `8M+17A`; deleting three residuals removes another
`3M+3A`, so every full form saves **31 operations = 11M+20A**. Every supplied
coordinate and paid gate is live. For cleanup flag `epsilon`:

\[
M=(3N^2+81N-46)/2,\quad
A=(3N^2+(131-2\epsilon)N-78)/2,
\]

with `13N-5` natural witnesses besides the three ordinary ports, and `8N`
residuals. At clean `N=8` this is **970 = 397M+573A**, `99` witnesses and
`64` residuals. At clean `N=1` it is **46 = 19M+27A**, `8` witnesses and
`8` residuals; selective cleanup costs one more addition there.

Independent formal degree propagation gives upper bound `6` for `N=1`
and `10N-8` otherwise. Exact integer coefficient propagation through the
entire source with every supplied coordinate replaced by `t` attains these
bounds, with leading coefficient

\[
17\quad(N=1),\qquad
8\,2^{10(N-1)}+2^{8(N-1)}\quad(N\ge2).
\]

This establishes exact total degree, without reducing modulo tag or
computation equations. The author's stronger leading-form explanations
agree: the one-row leader is `t2^2*b^4+t1^2*(a+y)^4`; for larger sizes the
unchanged root's third membership product already attains degree
`5(N-1)+1` before squaring. SOS highest forms cannot cancel. There are no
fixed compiler parameters needing an extra slice-uniformity argument.

## API checks and limits

The review checks exact family coverage, all saved canonical packets,
complete parent and child equality guards, every map and source accessor,
current metadata, assignment domains, defensive copies, and strict warm
pin rechecks of each parent Python/receipt/note through all eight public
entry points. It rejects Boolean or floating coordinates, invalid sizes,
non-Boolean cleanup/signed modes, wrong container types, absent/surplus
assignment fields, modified source or metadata, and nonzero parent tuples
passed to the zero projection. Explicit optimized-Python rejection is also
checked. Signed and rational whole-output evaluations supplement the
symbolic identities; rational arithmetic is an internal reviewer check,
not an advertised public assignment domain.

The saved independent run passes 16 literal full schedules, 16 graph identities,
16 arbitrary-`c` identities, 576 retained residual identities, 48 deleted zero
occurrences, all 7,828 paid live gates, and 16 exact degree certificates. It
also records 128 complete numeric checks (16 rational), 48 natural restorations,
22 complete zero projections, 66 explicit nonunique `c` fibers, 134 malformed
call rejections including 24 strict warm pins, and 18 defensive-copy checks.

The scope remains exactly the saved external sizes `1,...,8` and their two
cleanup modes. General formulas describe the same template; this review
does not manufacture certificates at unchecked sizes, remove the external
size, establish a fixed-arity universal polynomial, supply a new input
loader, or assert a global arithmetic lower bound.

Run from any working directory using only the Python standard library:

```sh
python /path/review_eager_tree_terminal_projection.py \
  --root /path/to/pointer-product-parent-trio \
  --artifacts /path/to/terminal-author-trio \
  --expect /path/review_eager_tree_terminal_projection.json
```

Both directories default to the review helper's directory and can be the
same installed research directory. `--output FILE` writes a deterministic
receipt; `--expect` compares all JSON types recursively. The finite fixtures
and guards supplement the quantified source and natural-projection proof;
they are not a replacement for it.
