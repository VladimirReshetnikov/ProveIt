# Independent review of the counted-suffix matrix construction

**PASS; no requested author change.** The frozen
[construction](matrix195_counted_suffix.md) gives an exact fixed-program
ordinary-input membership predicate with 195 integer matrices of dimension
seven. Its target has just one varying entry, a direct copy of x. The
suffix controls impose the integer count x inside the witness word; no
separate supplied Pell index remains. The unbounded product certificate
is still unpaid, so this does not lower the complete universal polynomial
bound of 84 operations.

I read the full frozen helper, note and receipt, as well as the complete
context-absorption and initialization notes. The latter results are
inherited mathematical dependencies; this review does not reimplement
their arbitrary-program compilation or reprove the original U15
simulation.

| Frozen author file | SHA256 |
|---|---|
| matrix195_counted_suffix.py | `bb876b65fa0544a8f8174e09a493715e47501a850ff518a2daed0643ead65b67` |
| matrix195_counted_suffix.json | `3c803a9a219eebf299a40dcece8958e905b3c59f8ba8b5cb1e60d9c52812c5bd` |
| matrix195_counted_suffix.md | `f53c2af29b0f3f292a047e9b16d29a94cd634ebd0337391bd8159beda63ca307` |

## The unrestricted control argument

The three control matrices are O=E00, F=E01 and
D=diag(0,[[1,1],[0,1]]). Their support proves the claimed language for
words of every length. A product with control entry (0,1)=1 must contain
F. Before its first F, any D kills the relevant product, because DO=0
and DF=0; thus that prefix consists only of O. After F, both another F
and an O kill the product, including after any number of D factors.
The only possible surviving suffix is D^k. Conversely O^n F D^k equals
F+k E02 for all n,k>=0, including either empty boundary. Words without
F and the empty word have (0,1)=0.

Thus the control equations force the entire literal word shape

    old_generators^n END COUNT^k

and force k=x by exact integer equality, with no congruence or additional
exponent witness. The physical lower block excludes n=0 because its
product would be I2 rather than P. The order of multiplication in the
source is correct: a surviving product has physical block

    M * diag(B^k,I2).

At k=x this equals diag(I2,P) exactly when
M=diag(B^(-x),P). Invertibility is needed only for this inherited physical
block B, not for the singular seven-dimensional control lift. Appending
END and x copies of COUNT gives the forward word map; deleting that
forced suffix gives its inverse. The exact new length is n+1+x.

The singularity does not permit invalid words to pass: the target's
specified control entry is nonzero. A zero-target mortality predicate
would require a different argument, and none is claimed here.

## All seven observations are sufficient on actual products

The two control observations first recover the whole control block and
the count/order above. Each physical lower block has determinant one,
so observations (1,2,0) on its first row and lower-left entry recover its
remaining entry. Every physical upper block belongs to H': the inherited
context-absorbed upper matrices do, END contributes identity, and COUNT
contributes B in the same group. The inherited injectivity of the first
row on H' therefore makes upper first row (1,0) equivalent to upper
matrix I2. Every off-block entry is structurally zero in every product.

These arguments establish equivalence between the seven displayed
observations and the full 49-entry target on all words over the emitted
alphabet. They do not assert that seven entries determine arbitrary
integer matrices. The projection introduces no new subgroup-recognition,
determinant or parity predicate that would need to be charged separately.

The ranks in the note also agree: every old physical block is invertible
of rank four; O and F have rank one, while D has rank two. Consequently
the old lifts and END have rank five, COUNT has rank six, and every input
target has rank five. These are singular directed-semigroup generators,
not a faithful SL(7,Z) group representation.

## Independent literal-source and witness checks

Using only the pinned parent JSON, I independently rebuilt all 195 full
arrays and compared all 9,555 entries. This checks every old physical
block, every structural zero and the two added controls. Both physical
2 by 2 determinants were independently checked for every generator.
The target template contains only 0,1,2 and one direct x copy, and its
saved straight-line source is empty. Zero target-assembly gates and
degree one are therefore accurate for this interface.

A separate finite-state recognizer, independent of the author's spelling
test, was compared with literal control multiplication on all 1,093
words of length at most six. This supplements the unrestricted support
proof; it is not a bound on accepted word length.

I also independently checked all 240 rewrite steps in the four saved
accepting examples. Each step was matched against every occurrence of
every actual rule, so the claimed unique enabled transition before halt
does not rely on checking only the first substring occurrence. I rebuilt
every context-copy tile and rule tile, the full correspondence equation,
the A/C/reversed-B word and its counted suffix. Exact 2 by 2 and 3 by 3
block multiplication then checked the entire resulting 7 by 7 products;
the already checked block-zero structure supplies all remaining entries.

| x | Literal rewrite steps | Tiles | Full lifted factors |
|---:|---:|---:|---:|
|0|12|83|168|
|1|44|843|1,689|
|2|76|2,371|4,746|
|3|108|4,667|9,339|

The complete coefficient ledger also agrees independently: 1,750 nonzero
entries, maximum absolute entry 4,652,051,305,867,101,902,730, maximum
magnitude bit length 72, and sum of magnitude bit lengths 54,001.
These are fixed-coefficient resources for this concrete fixture, separate
from arithmetic-gate counts.

## Fixed-program and Diophantine boundaries

The predecessor theorem supplies fixed contexts for each selected c.e.
set and the actual ordinary-input word U(W²)^x V. Context absorption
changes the fixed generator array with the selected program. The new
lift is uniform in any such array, so the note's program-specific
universality claim follows. It does not assert that the illustrative
contexts `[110` and `A0]` compile every program, or that a compiler for an
arbitrary program was executed. The four examples prove only those four
accepted concrete configurations, including the x=0 boundary example.

The comparison between three gates from already indexed Pell coordinates
and zero gates from ordinary x has different supplied-port contracts.
Here the exact index is enforced by an unbounded literal word suffix.
This is a genuine matrix-interface change, but it transfers work into
the membership witness and adds x+1 factors. No fixed-arity integer
encoding of that entire word, no paid full-product predicate and no
complete Diophantine circuit is supplied. The note states each of these
limitations explicitly and does not infer an arithmetic bound from the
195-generator count.

## Pins and replay

All five immediate dependencies authenticated successfully:

| Dependency | SHA256 |
|---|---|
| matrix193_context_absorption.py | `1304ea242ca6a5faafdb527ac3e56c6cd06b0276dca6441fc3477c7065054485` |
| matrix193_context_absorption.json | `73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436` |
| matrix193_context_absorption.md | `d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b` |
| group_directed_semigroup193.md | `75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e` |
| u15_unary_block_interface.md | `cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452` |

Fresh frozen-author receipt replays from `/` passed under normal Python
and `python3 -O`. The helper has explicit exception checks, strict byte
pins, duplicate/nonfinite JSON rejection and recursive type-exact receipt
comparison. The author's 29,524 control-word checks, 384 full block
identities and 20 rejected mutations match its literal source and receipt.
No predecessor Python or archived executable was run, and no repository
file was edited for this review.
