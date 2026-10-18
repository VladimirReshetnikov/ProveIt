# 246-state contextual-fold candidate for Con(ZFC)

This directory freezes the exact candidate from
[`8cdc55ff92`](https://github.com/VladimirReshetnikov/ProveIt/commit/8cdc55ff9281b0aaba49bf74b0b225d57f12b893).
Independent review found no mathematical blocker in the ordinary proof within
its stated scope. All nine primary checks and two additional audits pass on
fresh copies. **Its exact-machine Lean endpoint and equivalence proved inside
PA remain open.** The checked 252-state endpoint refers to a different table.

| Artifact | State conventions | Identity |
| --- | --- | --- |
| [Canonical table](zfc_prefix246.tm) | 246 working states 0–245; start 0; dispatch 88; separate halt 246 | SHA256 `89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc` |
| [Original labels](zfc_prefix246_old.tm) | Start 95; dispatch 96; separate halt 254 | SHA256 `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee` |
| [Renumbering](renumbering.json) | Exact state bijection, including halt | Both tables have 492 rows |

The machine has one two-way infinite binary tape, initially all zero, with
head at coordinate zero. Every transition writes a bit and moves left or
right, including the final transition into halt. Initialization uses the
counted working states. The intended theorem is blank-tape nonhalting iff
Con(ZFC); the report gives an ordinary argument in ZFC, while the project's
stronger PA objective remains unfinished.

Relative to the previously reviewed 247 table, it removes old state 97,
retargets `255/read 0` from `(1,L,97)` to `(1,L,255)`, and changes the blank
start from 97 to 95. A preceding write forces the symbol needed to identify
the two pulse states during runtime. The selector savings of old states
0, 1 and 3 were already present in the 247 construction and retain that credit.
The runtime argument does not transport the old blank initializer.

Its separate startup takes exactly 410,735 transitions and reaches dispatch
88 with head −5, marker −6 and header 176. The logical registers
`(N,T,W,A,D,H,X,Y,L)` are `(3,0,0,0,3,0,0,0,0)`, with 167 value-one spare
blocks and exactly 351 one-cells. Sparse and dense tape interpreters agree
on the entire tape. The unchanged original proof-search program has 6,460
leaves and 8,391 guarded instruction cases. Symbolic induction certificates
and finite regression checks retain the distinct scopes explained in the
[intake review](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162.md).

The [reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162-reproduction.md)
recover both complete reports, checkers, attribution and fresh evidence from
Git. These three machine files are unchanged copies of the delivered artifacts.
The original manuscripts remain recoverable from the committed arrival archive.

Mira-Cult designed the compact calculus and original 254-state machine;
Jeff Ketchersid supplied its verification and symbolic machinery; Andrew
James Wade supplied the compiler framework. The public 253 reduction is
credited to mira-emmy. ProveIt's permutation252, logical calibration and
earlier prefix250 research retain their respective attribution. The new
report contributes the further pulse fold and its new initialization.

The retained [delivery notice](NOTICE.txt) describes the original package;
its relative paths refer to that recoverable package. The accompanying
license notices retain their original scope and do not relicense upstream
material. This candidate and its finite audits assert neither unconditional
nonhalting, Con(ZFC), state minimality nor a completed PA equivalence.
