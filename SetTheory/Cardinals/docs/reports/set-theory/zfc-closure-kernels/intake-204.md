# Batch 204: proof simplification, GC–ZC215 and an SB return correction

Source 167 continues the existing K215 correctness-proof work. It contributes a
useful zero-offset certificate proposal, an ordinary argument for a distinct
GC–ZC215 construction, and an explicit rejection of two SB215 variants. Its
older symmetry proposal has already been implemented in the maintained proof.
No delivered executable was run in this intake and no delivered prototype or
alternative machine gains a new kernel-checked status through placement.

Placement **`ec445a5246`** accounts for all **82 outer members** of
`Proof_Simplification_and_GC-ZC215_2026-10-21.zip`, received in
`05d063acef885d47be5a2ce6645b046f98f7ea02`: 61 new exact-byte ancillary files,
14 existing exact copies, four duplicates within the delivery and three
archive-only manuscript files. The [placement note](intake204-placement.md)
and [complete recovery map](data/intake204-placement.json) preserve every
original name. The nested correction ZIP retains its
[18 members](data/intake204-nested-correction.json). Only this ZIP was retired;
other incoming archives and the Source 165/166 follow-up work remain outside
this intake's scope. No unified LaTeX article or PDF is needed for this
reconciliation-note continuation.

## The proof proposal against the current checkpoint

The delivery's snapshot is commit `c9dc79323429112c698100f3226a6e4d56c8b782`.
Its main recommendation is to prove offset-bisimulation symmetry once and use
one forward certificate for both halting directions. That recommendation is
already realized in the maintained
[phase-two symmetry proof](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase2/source-symmetry/README.md):
16 reverse-check modules and their mirrored data are unnecessary. The two
programs, arbitrary-register theorem and exact K215 endpoint are preserved.
The latest completed
[phase-four Lean checkpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase4/README.md)
checks the 185-module closure and both typed endpoint clients. The separately
checked Rocq endpoint is unchanged by this intake. A phase-five rebuild is in
progress; no result from it is asserted here.

The [delivered refactor report](167-proofgc-ref-REPORT.md) attributes
1,118.7394 seconds to the old 16 backward modules, out of 4,485.4087 summed
204-module compiler seconds: about 24.94%. Those are historical sums, not
wall-clock time or a measured speedup of a rebuilt proposal. Its
[compact Rocq data prototype](code/167-proofgc-ref-Cert215Compact.v) represents
the same 2,240 rows with positive-integer path encodings and reduces data text
from 1,499,170 to 190,411 bytes. The submission explicitly says that prototype,
its Lean symmetry files and its 107-line `PrefixCredit.v` were **uncompiled**.
Smaller source and a Python reconstruction receipt do not change that status.

The substantive next proposal is the
[four-field zero-offset certificate](167-proofgc-ref-ZERO_OFFSET_STAGE.md).
All 2,240 offsets are zero. Ordinary bisimulation can therefore avoid the unused
integer-offset layer, but its existing 128-fuel decoder cannot simply replace
the offset checker's 512-fuel decoder: 622 pairs have a path longer than 128 bits,
with maximum 176. The proposal parameterizes the ordinary checker uniformly by
its decoder, retains the 128 instance for old clients and explicitly chooses
512 here. It preserves tree cuts and successor indices, then either proves
zero-guarded erasure transport or directly rechecks the four-field data in the
kernel. This is a precise new simplification target; placement is not evidence
that the implementation or full dependent closure has passed.

A further proposed optimization shares certified decoder trace prefixes.
It correctly keeps physical entry state, continuation/break ancestry,
predecessor markers and exit contracts in the sharing key. The 202 source
subtrees do not justify replacing all 4,751 occurrence checks by 202 checks.
No implemented context-sharing speedup or smaller machine is supplied here.

The [pinned-reference comparison](data/intake204-pinned-references.json)
records the delivered upstream material without normalizing it. The large Rocq
certificate matches the claimed commit exactly; the other 23 snapshots append
one terminal LF. Two are renamed compiler logs from
`lean/actual/audit/axiom-components/compiler.log` and
`lean/actual/audit/independent/compiler.log`. Delivered snapshots remain
research references and do not replace original raw build evidence.

There is one terminology correction. The manuscript and an inherited compiler
note speak of “undecodable” formula codes. The maintained
[Code254 decoder](../../../../../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean)
is total on naturals: positive-tag children are smaller, and zero has its
explicit truth interpretation. Raw codes can be **noncanonical**, outside the
literal encoder image, and proof candidates can be invalid; no natural formula
code fails this decoder. The all-natural proof should retain that generality,
without an added encoder-image premise. The submitted prose is preserved
unchanged; this correction belongs to the reconciliation.

## GC–ZC215: compiler and scheduler arguments

The [completed hybrid argument](167-proofgc-proof-GC_ZC_COMPILER.md) combines
exhaustive DROP0/NIP1/MP2/AX≥3 enumeration with command-tag generalization.
Only source register operands 46 and 51 change from 4 to 3, replacing AX's ninth
head `Q_U(old h)` by `Q_C(old h)`. Addresses, primitive kinds, other AX outputs,
freshness gates and dominated-row parameters remain fixed. The resulting
source has 4,752 leaves and 203 distinct subtrees.

For a strong block `B_X` returning `(X,w,0,0)`, the shorter GEN block is

```text
B_X; DROP; NIP; AX(i;0,0); NIP^9; DROP; NIP; NIP.
```

The old `J(i)` counter load disappears. The proof checks the important change:
the saved top gate `G(0,X,i)` may be enabled, so it need not be zero. It is zero
or implication-coded and therefore never falsity 1; the final NIP can discard
it safely. The other inherited compiler blocks arrange `C=U` where required,
or discard a quantifier head using its tag rather than its binder. GEN remains
theorem-only. These facts support the stated all-natural strong-block argument,
including early halting and numerical aliases.

The [tag-lowering injection](167-proofgc-zc-proofs-tag_lowering_credit.md)
is the main reusable scheduler lemma. Replace one NIP tag 1 by same-arity
DROP tag 0 at the same command position. Strict monotonicity of the nested
Cantor encoding gives a smaller candidate; raising that position recovers the
unique source occurrence. Every reached NIP thus has a distinct DROP in an
earlier completed candidate. Including the imminent pop proves strict
pre-pop credit. An explicit list of theorem heads above an arbitrary numerical
tail handles zero aliases; numerical stack magnitude is not an invariant.
AX and MP can be assigned zero credit in this argument.

The hypotheses matter: exhaustive increasing enumeration starts at raw zero,
parsing is unique, DROP/NIP arities agree, and stack history is preserved
between candidates. The lemma does not justify a positive cutoff, skipped
candidates or an incorrect source return. The
[finite-list Rocq prototype](code/167-proofgc-credit-PrefixCredit.v) states those
interfaces separately. Its recorded 100,000-candidate regression has 19,566
NIP images, 49,275 DROP commands and minimum prefix balance zero; this is a
finite diagnostic, not the all-natural proof or a kernel compilation.

## Exact binary evidence and its limits

The [construction receipt](data/167-proofgc-hy-COMPOSITION_AUDIT.json) reconstructs
an unmerged 216-state table and identifies role 303 with 129. Its unique incoming
edges force opposite predecessor markers: `211/1` writes 1 then enters 129
moving right; `135/0` writes 0 then enters 303 moving right. The modified
`129/1` route via 216 has four local whole-tape cases of lengths 1, 3, 1 and 5.
This is a conditional merge relative to that explicit unmerged table; matching
rows alone are not an equivalence with a prior accepted 215 table. Primitive
simulation and initialization remain separate obligations.

The submission's [runtime receipt](data/167-proofgc-hy-GC_ZC215_RUNTIME.json)
reports 6,177 cases, 1,698,909 symbolic rules, positive minimum duration 9 and
all 430 rows. Its [corrected native table](data/167-proofgc-hy-gc_zc215_start74.native.tm)
has start 74, halt 254 and 215 working states, with SHA-256
`4122c18a347028ee6643428b70a8d5c81218d4937d672be3626981d7b50bf503`.
The dense relabeling starts at zero. The preserved runtime input incorrectly
declares start zero in its comment; the
[header-only transport](data/167-proofgc-hy-HEADER_TRANSPORT.json) records
unchanged transition rows and the corrected start 74.

The [reported complete blank root](data/167-proofgc-hy-GC_ZC215_BLANK_ROOT.json)
is reached after 117,004 transitions: dispatcher 84, head −4, PC `000`, logical
registers `[1,0,5,0,0,0,0,0,0]`, gap 20 and a nonempty mixed spare list, with the
entire finite tape and zero exterior specified. The 69,143-step receipt is
intermediate, not this calibration root. The arbitrary stack tail 5 is exactly
what the injection protects.

The written source compiler and scheduler argument, inherited numerical
calibration, exact primitive simulation and complete startup together give the
submitted ordinary ZFC consistency equivalence. This intake read the argument
and preserved its evidence; it did **not** freshly replay that runtime or blank
trace or compile a GC–ZC215 endpoint. It changes neither the selected formalized
K215 table nor its status. The earlier “prospective hybrid” passages in
[PROOF_COMPARISON](167-proofgc-proof-PROOF_COMPARISON.md) are superseded within the
same delivery by the later completed hybrid argument and records, and remain
historical context. Scratch names such as `GC_ZC_PRICE.json` and
`GC_ZC_MERGE.json` are not extra delivered members; the complete map identifies
the files actually supplied.

## SB correction and negative experiments

The [SB reconciliation](167-proofgc-fix-REVIEW.md) and its nested archive
retain two rejected SB215 variants. Both put CC3 at ordinal 4697/address
`100111`, returning to ordinal 23 rather than scheduler root zero. AX exit 4589
reaches 4696 (CI6) and then that return. Under the inherited AX-exit invariant,
the suffix forces cache 1 and reaches CH4718 in `15+2T` source steps. The AB
variant changes four rho6 operands and two native rows while retaining this
faulty control graph.

The ordinary clear-loop proof is all-natural; its six finite probes merely
illustrate it. The recorded 69,744-step common binary prefix is not a literal
execution of the entire large AX arithmetic. The binary blank-halting conclusion
also uses the inherited terminating AX contract and source-to-binary simulation.
A runtime PASS or abstract fairness theorem cannot repair the wrong source
return. The separate FT215 construction is expressly unaffected.

Other failures remain bounded: a binder-`Q_A` trial reached 205 source nodes
across 42 associations, but its three selected allocations failed primitive
prefix checks; a state-301 deletion failed tested FT blank screens. No
214-state construction, state lower bound, unconditional nonhalting, internal-PA
endpoint or shorter complete formal proof of the hybrid follows.

## Preservation and recovery

All delivered bytes, notices and attribution remain unchanged. The main README,
LaTeX manuscript and PDF are recoverable from the arrival Git archive. The
[recovery helper](code/recover-intake204.py) reconstructs the original 82-file
layout from the placement map and arrival object:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake204.py --repo . --out /tmp/recovered-source167
```

Only this newly authored recovery helper was executed; its
[control record](data/intake204-recovery-control.json) passes all 82 members.
It checks Git blob identities and executes no delivered code. The redundant
temporary extraction was removed after placement and recovery verification;
records, immutable archive history and all proof caches were preserved.

The delivered top-level verifier includes a manifest suite and was not run.
Any future validation should select reviewed leaves on a disposable recovered
copy: data compression, codec regression, source/marker composition, complete
startup/relabeling, then the full runtime if needed. The composition script
needs explicit `--source hybrid215/source.sites.json`; its default old scratch
filename is absent. Kernel adoption requires the maintained toolchain and
exact endpoint/assumption checks. None of these possible follow-ups is counted
as completed here.
