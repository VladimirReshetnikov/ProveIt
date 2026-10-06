# Independent review of the complete grouped-left compiler

The full handwritten proof/count challenge and the complete independent
static source audit both PASS, with no author correction requested. Root
read the entire original auditor and executed it exactly once after preflight;
its first result passed all 2,663 rows and metadata. This review resolves the
author's explicitly pending downstream audit without changing frozen bytes.

The reviewed author primary is `positive7_grouped_left_compiler_riemann.md`,
SHA256 `4987ae06163aa35dd138ce616873cc7804852273aefaa3faedac32de756f299e`.
I read all 103 lines and the complete 249-line frozen original composer
inertly, plus the full separate 321-line provenance receipt. I independently
read and challenged the complete local mathematical draft before its freeze;
its final proof pin is `a555ae04bfeb8d9ca3dbbf5bdb7551b22f7e2390d41d88050cf1cfaef4e9479f`.
The first source receipt is `f247d5f4b7f04a0fe14847b9dfe5db46c60b002c709dde71fd248e306868d8d1`.
Its source parent is the separately reviewed grouped-right receipt
`4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c`.

## 1. Independent integer-polynomial argument

Keep the parent's paid form pairs p_j, history blocks B7,B6a,B6b, tail
V=DP+S, and powers P4,P12,P24,P28,H, where H=P^(4r+52). Write
U2=1+P2, U6=1+P6 and G7=(1+P7)(1+P14). Descending expansion of the old
quartet recurrence gives P^(4r)V+U2 Q, where

    Q=sum_(j=0)^(r-1) p_j P^(4j).

The next join multiplies by P28 and adds G7 B7. The last two joins give
P24 times that higher word, plus U6(P12 B6b+B6a). Thus the complete high
left word is exactly

    H V + U6(B6a+P12 B6b) + P24(G7 B7+P28 U2 Q).

This uses the already charged power equalities, not independent free inputs
with inconsistent exponents. Once those producer definitions are substituted,
it is an integer-polynomial identity on every supplied tuple, including
P=0,1 and negative P. It requires no native zero, selector, positivity or
carry assumption. The single high-left exit is preserved; with every other
arithmetic row unchanged, the whole final polynomial is preserved.

Horner evaluation of Q has r-1 products and r-1 additions. The displayed
reconstruction has seven products and four additions. The old cut has
(2r+6)M+(r+3)A, and the new cut (r+6)M+(r+3)A. This pays all final joins
and saves exactly rM, including r=1 where Q is the existing p0 register.

For the collected-center route the existing correction is
Gamma=W P28 R_(4r). Its old position was after the seven-block join and
before both six-block shifts. Moving its one addition inside the P24
parentheses gives exactly the same correction in the final word. Add one
addition to both local cut ledgers; its existing producer remains charged.
The saved arrays are the uniform r=1,2,4 cases. No absent collected graph
or generic alias fixture is certified by pretending it was emitted.

## 2. Independent source audit specification

The new auditor was authored as a separate original metadata program, not by
running, importing or modifying the author's frozen composer or a predecessor
helper. It specifies the old deleted cone, fixture support moves and new
Horner/reconstruction records from the reviewed interface. It compares the
entire successor row list to that independently assembled literal list.
It treats arithmetic operators solely as labels for record equality,
dependency edges and operation census; it never applies them to values.

The independently checked disjoint partitions and counts are:

| r | Unmoved | Moved | Removed old | Inserted new | Certificate M/A | Full M/A | Rows |
|---:|---:|---:|---:|---:|---:|---:|---:|
|1|785|2|12|11|224/506|247/551|798|
|2|846|3|15|13|250/544|273/589|862|
|4|982|4|21|17|309/626|332/671|1003|

The whole verified partition is 2,613 unmoved literal rows, nine moved
literal rows and 41 new rows, replacing 48 old rows and giving 2,663.
The reused final name `left_six_high_join_a` is a new definition, not an
extra retained old row. Its sole external arithmetic consumer is
`left_selector_shift`; the active high-left port retains the same name.

The moved support has two, three or four products in the three fixtures.
All operands are available before the left tail, and the products retain
their former right/native consumers. The left stage gains the moves and
loses r products; the right stage loses the moves. Whole-stage totals
therefore decrease by r, despite possible growth of the isolated left stage.
The final native link remains one multiplication. The complete 64-row
native stage and the 68-row finalizer are literal inherited blocks.

The auditor also checks every stage slice, unique output names, topological
availability, final-output liveness of all computed and supplied names,
the exact fixed-role families and active port/form/lane bindings. It checks
the exact permitted metadata changes and the entire unchanged fixed recipe
and r=0 fallback. All these checks passed on the first run. The first-result
JSON records 798/862/1003 computed names, 103/109/121 supplied names including
the ordinary input, and 21/36/66 distinct linked fixed roles.

Root fully preflighted the original 278-line auditor at SHA256
`c7053af46dbe37df406cab658aefde5ac68ec3acf51404a34d8a627dc5e7a630`.
He then executed exactly those bytes once and froze them with the first
result, SHA256 `bbee86e0fe3a1c272a98524a6442845d9c931916d7ec88cd9c05a3edc91683ad`,
and first log, SHA256 `5a2713c128bd847692ab0ce0fdd3465f3697bb2b088641f46e9081e86cd9d137`.
The companion review receipt embeds the exact first-result text and its
parsed object and checks their equality. Neither checker, author composer
nor either saved source array was subsequently replayed, imported or
arithmetically evaluated. Byte hashing and metadata parsing do not execute
their recorded arithmetic operators. There was no failed auditor run.

## 3. General ledger and retained scope

Subtracting rM from the fully reviewed grouped-right grammar gives

    uniform: (219+27r+gM-A-B-D18-E24)M+(508+40r+gA-B)A;
    collected: (222+27r+gM-A-B-D18-E24-eta)M
               +(512+39r+gA-B-eta)A.

The inherited fixture corrections remain f(1)=3,f(2)=2,f(4)=1 products.
They give precisely 798/862/1003. Subtract 23M45A for each certificate.
The general pack-stage and native-link split in the primary has the same
total; the saved fixture pack/native reductions are not counted a second
time. The r=0 fallback remains 903 operations and 96 positive witnesses.

The same ordinary input, 96+6r positive witnesses, 23 comparisons and linked
6+15r fixed roles transfer because the final polynomial is unchanged.
The role `gamma` is the single fixed role used in addition; all remaining roles occur
in multiplication. The count of roles is not a count of multiplication-only
roles. Semantic positive centered forms remain semantic descriptors under
the inherited guard; no new free executable forms are introduced here.

**Remark 1 (invalid tail shortcut).** Multiplying a Horner accumulator
initialized at V by U2 also multiplies its tail by U2. At r=1,P=1,V=1,
p0=0 and zero history blocks it returns 2 instead of the required 1.
This is a local integer-cut counterexample, not a full positive native zero.

**Remark 2 (valid weaker schedule).** A separately charged P52 producer
gives a correct schedule with one extra multiplication and saving r-1.
The new nested reconstruction saves r; no general optimality follows.

**Remark 3 (historical and numerical boundaries).** The author's frozen
primary explicitly awaited independent source review. A completed downstream
audit may resolve that obligation without changing the primary's historical
status. General collected grammar remains a hand proof rather than an
unwritten saved array. No numerical universal presentation, matrix list,
source degree or arithmetic lower bound follows from the three fixtures.

No saved program was replayed or imported, no arithmetic/coefficient array
was evaluated, and no symbolic calculation, degree propagation, build or
repository mutation occurred. Root read the complete 146-line reviewer draft
and passed its mathematical identity, both center routes, every record
partition/count, supplied-name and role counts, first-run pins and general
scope without correction. Final edits record only this provenance/status.
This reviewer pair is now frozen. The audit source and first outputs remain
unchanged and must never be replayed or modified.
