# Phase21: share the native AX expression proof

**The kernel check, independent actual readback and independent evidence capture
review pass.** This continues
[phase20](../phase20/README.md) at `a113bb79e275c769c057fea7f6cc1540b0bfef32`.
The literal 215-state machine and its endpoint statements are unchanged. The
internal PA endpoint and a minimum-state theorem remain open.

[`AXWord`](../../../../../../../Lean/BusyBeaver/ZFC/AXWord.lean) supports
expressions built from an ordinary atom, an atom prefixed to a subexpression,
sequential composition and the terminal gate. A prefix may use any atom; for
`readwff`, its successor contract includes both native nodes 158 and 208. A
standalone atom excludes that special read. One structural proof composes the
existing macro contracts. The linear word routines reuse it through two private
bridges; their checks, effects and shared 148-atom suffix are unchanged.

[`L2Axioms254`](../../../../../../../Lean/BusyBeaver/ZFC/L2Axioms254.lean) supplies
a literal expression. The mandatory
`axExpr_checked` certificate checks its complete shape against literal `dag254`
at root 1 with gate 71. The native run theorem uses that certificate, so the
semantic macro sequence alone is insufficient to assert a program run. The
checked source has 247 expression constructors and 180 semantic macro effects.
Its finite shape certificate, native run and cleanliness contracts, and exact
symbolic evaluation theorem compile with zero warnings. The native module takes
1.42 seconds in the accepted run. Its semantic proof uses a scoped one-million
heartbeat budget; compiler limits remain 120 seconds and 12 GiB per invocation.

The exact public headers of `L2.f1`, `L2.l1`, `L2.c1` and `L2.ax_eval` are
preserved. Direct symbolic evaluation replaces the single-use generated `e1`
bridge in `L2.ax_eval`. That semantic theorem moves from `L2Root254` into
`L2Axioms254`, beside the expression it evaluates; its qualified name and type are
unchanged. Root callers
continue to receive it through their existing import. The old `L2AxiomsEval254`
module and 479 generated declarations are retired. The source census covers the
four maintained Lean roots and all fifteen accepted typed clients, and finds no
other maintained caller of the retired names. It makes no compatibility claim
for unused qualified generated namespaces outside this repository.

Three Lean files are edited and the old evaluation module is removed. Their
combined source shrinks from **1,755 to 670 lines**, removing **1,085 Lean lines /
104,946 bytes**.
Four obsolete native writers and arithmetic text-port templates are retired with
their original bytes preserved:
[`generate_l2_axioms.py`](retired/generate_l2_axioms.py),
[`generate_l2_axioms_eval.py`](retired/generate_l2_axioms_eval.py),
[`port_l2_axioms.py`](retired/rotation240_pa/port_l2_axioms.py) and
[`port_l2_eval.py`](retired/rotation240_pa/port_l2_eval.py).
The four writers total 568 lines / 21,499 bytes, bringing active maintenance
savings to **1,653 lines / 126,445 bytes**. Together with the old evaluation module,
all five retired snapshots retain their original bytes. No supplied writer or
parser was executed. The independent `ArithmeticL2` sources are unchanged. Historical
audit scripts, receipts and old input bytes retain their original meanings; the
[retirement note](retired/README.md) identifies their archival inputs.

Savings cover the selected compatibility sources. The primary 215 endpoint
retains **179 modules** and grows from 1,768,653 to **1,771,267 source bytes**
(+2,614 bytes). The large native generated proof scaffold was outside that primary
closure. Physical source savings and endpoint closure size measure different
scopes. The [source measures](integration/metrics.json) bind these exact comparisons.

The accepted check covers **226 providers**: 211 project modules and fifteen
unchanged typed clients. Eighteen providers compile fresh and 208 reuse exact accepted
source/object/dependency/log bindings; both endpoint audits compile fresh. The
two affected existing clients, `WFModelCompat12` and `ZFNativeCompat12`, are among
the eighteen fresh providers. All fifteen clients' 93 reports, `WFTheory`'s five
provider reports and the two endpoint audits' ten reports retain their exact
accepted assumption profiles. All fresh providers and both audits have zero
warnings; fifteen inherited warning occurrences retain their accepted meanings.
All sixteen canonical absences are checked. The 215 source-forward
and site batches retain their accepted identities. This check does not establish
a new endpoint result for another machine variant.

All eleven rejected computed-expression attempts through v11 retain their sources,
records and raw logs as unaccepted history. They include reserved case-label
parsing and failures or resource exhaustion during decoder normalization and
symbolic evaluation. Only v6 reaches the 120-second wall timeout. The literal
candidate avoids the decoder normalization
step while retaining the separate finite certificate and shared run proof. No
rejected attempt counts as accepted validation of the literal candidate.

The accepted result is
`a2e1a93317cac5531d20fcf6724628004dff7d5fe67fb9ebd16b16cba9fbdd57`.
The [independent actual readback](lean/result-review.json) checks 1,168 owner
inputs, 55 mandatory present pins and sixteen absences, with 195 adjacent raw
provider records. Thirty-one inherited providers retain the accepted aggregate
boundary for absent original raw records. The later upstream `ConstructibleAbs`
normalization remains separate from this frozen checkpoint; no integration check
is claimed here.

The [independent capture review](integration/capture-review.json)
checks all 585 archive blobs, 3,053 logical entries, 3,038 source aliases and 2,861
raw evidence rows, including all eleven rejected compiler prefixes and the exact
five retired snapshots. It checks every hash-pinned provider log; optional
structured reports also compare after strict normalization of their historical
string/list formats. The earlier reader schema failure and its repair remain
separate preserved history. No compiled object is shipped, no archive is extracted,
and the capture reader executes no captured code.

The [Lean evidence](lean/README.md) records every fresh receipt and reused
dependency. The eleven phase20 Lean evidence leaf files remain exact historical
boundaries; this page does not revise their records.
