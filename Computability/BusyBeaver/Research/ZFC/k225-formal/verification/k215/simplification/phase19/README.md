# Phase19: inline root projections and infer transfer results

**The combined Lean check, independent result readbacks and evidence capture pass.**
This continues phase18 at
`a5ed3a9c9cd41feb2bd23363e1504558fee45c3f`. The 215-state machine and endpoint
statements are unchanged. The internal PA endpoint and a minimum-state theorem
remain open.

`L2Perm` and `L2Dom` infer the results of 22 normal-run transfer aliases apiece
from the same typed arguments and annotated transfer calls. Both finite closure
proofs, the equality contract, sequencing helpers and explicit existential
halting contract remain. All 33 names in each transfer module are retained.
The source producer is synchronized; it has not been executed.

The five root modules inline the `root_step` rewrites supplied to
`RMDag.iter_halts_iff`. Eight modern projection lemmas had one caller each.
The native reference root now uses that existing iteration theorem, replacing its
duplicated induction and making its two projection wrappers single-use as well.
The ten `root_some` / `root_none` names are intentionally retired. A lexical
census of all 32,415 Lean files in the four maintained roots found no caller
outside these five modules. In the root modules, every other declaration and proof
body remains exact, apart from the native root's necessary import of the existing
iteration theorem.
No data definition or mathematical premise changes.

Seven edited Lean files remove **169 lines / 6,449 bytes**. The producer adds
two lines / 208 bytes, giving **167 lines / 6,241 bytes** of net maintenance
savings. The 215 endpoint retains 178 modules; its source closure falls from
1,767,300 to **1,765,109 bytes**, saving 2,191 bytes. The other five edited Lean
files are checked compatibility sources outside that endpoint closure.
See the [exact source measures](integration/source-metrics.json).

The frozen check covers **226 providers**: 211 project modules and fifteen
unchanged typed clients. A passing old-source baseline compiles twelve added
compatibility providers and reuses the 214 accepted phase18 providers. The
combined candidate then compiles sixteen providers, reuses 210 and checks both
endpoint audits fresh. The selected import closure checks all five changed roots
and both transfer libraries. Source-forward and site certificate batches retain
their checked phase18 source, object, dependency and log bindings; no fresh
certificate-batch check is claimed here.

All 93 typed-client reports, five `WFTheory` reports and ten endpoint audit
reports match their exact baseline profiles. Provider records have 18 warning
occurrences: one fresh and seventeen reused. The fresh warning is the native
root's preexisting unused `h` simp argument. All fifteen clients and both audits
have zero warnings.

The first old-source run stopped on a zero-warning policy for unchanged
`L2Control219`: its compiler returned PASS/0 with two unused simp-argument warnings,
while the outer runner returned FAIL/1 and emitted no result. Its ten raw compiler
attempts and nine accepted fresh records are preserved; the last object is
excluded. The accepted replacement starts fresh against phase18 and permits
only that unchanged module's observed warnings. A first owned baseline reader
also failed on historical aggregate records lacking direct exit metadata; its
source and failure are retained. The corrected reader preserves that historical
boundary and checks every fresh record explicitly.

The [Lean evidence](lean/README.md) preserves both accepted runs, their independent
readbacks, source/log/record evidence and exact source snapshots. Eleven phase18
leaf files remain exact external boundaries; prior compiler history is not
copied again. Before-source identities resolve to verified frozen workspace or
proposal snapshots after canonical paths change. No object files are shipped.
Capture stores 396 distinct blobs, 713 logical entries and 712 source aliases.
The [independent capture review](integration/capture-peer/actual-review.json) checks
the archive, index and required evidence coverage.
