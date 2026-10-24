# Attribution and scope

This contribution was prepared for Vladimir Reshetnikov's ProveIt project on
23 October 2026. New work: the adaptive `q^2 Y` carrier with its gcd-cofactor
proof, centered Pell-gap elimination, explicit circuits, report, and checks.

The complete fixed coefficient tuple, transition table, compiler recipe, and
retained mathematical dependencies come from ProveIt at commit
`a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`. Source 61 supplies the immediate
positive-variable kernel and baseline. Source 44 supplies the complete compact
tuple. Sources 36 and 58 supply retained proof interfaces. The exact file ledger
and upstream license/notice files are preserved in `upstream/`.
Source 62 supplies prior two-root norm and root-centering ideas; sources 64--65
supply prior adaptive and successive-congruence recovery ideas. The present
contribution uses a different strong-root center and their measured combination
with the source-61 carrier. These generic techniques are not claimed as new.

The adaptive13 builder is derived from source 61's builder and retains its DAG
helper with attribution in `positive13/NOTICE.md`. The centered12 builder was
written for this contribution using the same explicit arithmetic source.

Retain `LICENSE`, all files named `LICENSE*` or `NOTICE*`, and source attribution
when redistributing. No claim of global mathematical priority or external peer
review is made. All finite verification boundaries are stated in the report.
