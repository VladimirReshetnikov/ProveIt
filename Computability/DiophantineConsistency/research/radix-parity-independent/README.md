# Two obstructions to a direct smaller-radix transplant

This note concerns the frozen Boolean-dummy4027 ordinary proof, not an
impossibility theorem for all Diophantine equations or all outer converses.
It records why changing only the radix is insufficient at the retained
proof interface. No accepted tuple is changed.

For radix `rho=2^46`, every cell has `d=46L` binary bits and every native
word has `t=dN` even. The actual rank's origin calculation still gives
`R=3 mod4`, independently of N. Consequently both `R-t` and `R-3t` are
odd, and neither `w=2^(R-t)` nor `X/q^3=2^(R-3t)` is a square. The retained
complete converse explicitly requires these squares; see
[the complemented47 ordinary source](../compact66-complemented-three-anchor-radix47/README.md),
the completeness paragraph beginning “Odd d,N,R”. Its statement that a
square suffices does not waive the square condition. No choice of fresh
dimensions or controller subset fixes this parity while R remains odd.
Thus a direct radix46 substitution has no certified completeness map.
A new parity/rank interface or a different outer converse would be required.

Radix45 restores odd d, but the present clean-count lemma fails for the
available pre-decoding carry range. Here is an exact local counterexample
to that lemma, using all selectors except the already forbidden selector1.
The complete coefficient array is
[single-dummy-independent/coefficients.json](../single-dummy-independent/coefficients.json),
SHA256 `485f3e3bfa617cb5a1b7aa98447d3629b8e53057d0f2aed5eecb56fd6b52ac98`.
It has the same weighted coefficients as Boolean-dummy4027.

Let n=942 and incoming k=82, so n+k=1024. Put

    Qsel=sum_(j!=1)(c_j-1)/1024=3722971027692,
    W=(-1-Qsel) mod2^34=5060585235,
    raw=sum_(j!=1)c_j+1024*W+k=3817504371638272.

With `rho=2^45` and the retained mask `mu=2^44-2`, the actual digit is
`raw modrho=2^44=17592186044416`, its outgoing carry is108, and its
intersection with mu is zero. W is an allowed unsigned34-bit label value.
Thus this clean clause passes its mask despite containing942 selectors.
The full Boolean coefficient bound admits incoming carries through109,
so it does not exclude k=82. The old proof relied on n+k<1024; that is
exactly the inequality lost here.

These values were recomputed directly from the complete JSON array using
integer arithmetic, without importing project code. This local example
does not prove a cyclic native word exists, nor that the changed polynomial
has a zero. It proves only that the existing count-decoding lemma cannot
be reused with that carry range. A sharper carry argument or a changed
count encoding would need its own full proof before radix45 promotion.

Author: `/root/complemented47_review`,2026-10-25. The current label/selector
compression work is independent of these radix obstructions.
