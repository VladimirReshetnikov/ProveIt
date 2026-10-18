# Pending incomplete delivery: zfc-state-reduction-research.zip

Status: **PENDING — partial review only; not an accepted batch-158 source.** The ZIP must remain in `docs/incoming/`. A complete replacement delivery is needed before the advertised verification suites or full intended payload can be accepted. The scratch name `run55` is a temporary assignment only; it does not reserve host source number 55.

Provenance: manuscript pin `43026ff42f0939f09b9e95495248cfadcad38e38`, stated at `report.tex:69` and the delivery README's Fixed input section. Recovered source is `/tmp/zfc-intake-158/zfc-state-reduction-research-partial/zfc-state-reduction-research`; execution copy is `/tmp/zfc-intake-158/run55`. Recovery evidence is `/tmp/zfc-intake-158/partial-recovery.json`.

The archive lacks its ZIP central directory. Root recovered **327 complete local members** by reading local headers and complete deflate payloads to EOF. None of those individual members is incomplete. That fact does **not** mean the intended package is complete: its tail omits essential independently referenced files. No checksum manifest was inspected or verified for this assessment. Missing-file conclusions come from executable references, prose promises, recovered file existence, and the archived partition-audit domain list.

## Precisely missing material

- The entire recovered `work/theory_audit/` directory is absent. At minimum the promised `check_affine_certificate.py`, `check_affine_mutations.py`, `direct_negation.py`, and `shifted_negation.py` are missing (`README.md:114–117`). These contain the independent invariant checker, adversarial controls and constructor rewrite generators/correspondence checkers.
- `verify.py:59` immediately imports missing `check_affine_certificate.py`; `verify.py:85–96` later invokes it and missing mutation checker. Therefore the advertised quick audit (`README.md:61–70`) cannot run, even when the manifest step is intentionally bypassed.
- The archive contains **33** `work/state_reduction/two_action_*_gap.json` result summaries, although `verify.py:105–110` requires 36 and `README.md:79–82` promises all 36 journal domains.
- The archived `degree2_partition_gzip_audit.json` names 36 domains; result files for deleted states **89, 92, and 98** are absent.
- Only **32** corresponding `.jsonl.gz` journals were recovered. `two_action_82_gap.json` exists but its required `two_action_82_gap.jsonl.gz` does not. The three absent result domains' journals are also absent.
- Consequently the claimed complete 36-domain fresh partition and combined 46-domain/46,738,944-recipe closure cannot be independently replayed from this delivery. The missing partition data are substantive, not a ZIP reader cosmetic issue.

This is not a checksum or line-ending complaint. Reconstructing a central directory would not recreate the absent verifier sources or journals.

## Partial source review

The complete recovered `report.tex`, all three included TeX files, delivery README and status were read. The paper correctly disclaims a sub-252 result. Its best new implementation has **255 working states and 510 rows**, larger than the existing 252-state baseline.

The identity at `report.tex:149–162`, `P(x,1)=P(0,x)+2`, is correct for the repository's dual Cantor pairing. Thus `Not(x)=4P(0,x)+8`. The clean macro proof at `report.tex:168–196` correctly composes pairing and scale-by-four under scratch1=scratch2=0, frames the entire remaining file, and permits the alternative preadd-two implementation because pairing's scratch2 accumulator is additive. Our maintained Pair and Scale4 results offer exactly the arithmetic components this ordinary proof uses. However the missing generators prevent this review from checking the claimed matching of *every actual optimized occurrence* and the original source's clean-call premise. A valid algebraic identity alone is not a certificate for the rewritten control program.

The invariant method at `report.tex:228–334` is standard exact affine abstraction with a homogeneous coordinate and a separate three-category natural mask. Initial inclusion plus all successor inclusions would prove the stated invariant. It correctly distinguishes rational exactness from exact reachability, states that the extra equations exclude **no new guard**, and explains why a full-dimensional site prevents this certificate from eliminating a fixed register globally. The natural-number lemma at lines 272–277 is sound. The absent independent checker and corruption controls mean the reported 8,384 affine postfix obligations, 1,433 enriched sites and 27 extra canonical equation rows remain **unreplayed supplied claims**, not newly accepted proof evidence.

The context-sensitive decoder warning at `report.tex:346–352` is particularly relevant: equal subtree fingerprints do not justify reusing entries that inspect surrounding tape bits. It agrees with the maintained negative macro-structure diagnostic. The source-only 203-node/maximum-zero-run-six layout is not a proved smaller binary artifact.

The transfer theorem at `report.tex:422–438` is mathematically sound as an ordinary statement with its explicit positive-length, no-intermediate-halt, total-coverage and complete-frame hypotheses. The ranked silent-step discussion at `report.tex:366–377` correctly requires a decreasing rank and warns that phase-specific masks cannot simply be applied to arbitrary quotient representatives. Neither paragraph establishes its unprovided concrete certificates.

## Request/status corrections

- `report.tex:78,92–97,401–403` again describes the user goal as provability in ZFC and explicitly treats PA internalization as beyond the task. This conflicts with the original user request, which explicitly requires equivalence provable in PA. Any eventual reconciliation must preserve the delivered text but correct that characterization.
- The paper's account of the current external Choice endpoints at `report.tex:395–399` is appropriately updated: ChoiceCalibration254/BinaryZFC252 exist, while no new object-level serialization is supplied. Unlike the geometric-counter manuscript, this delivery does not falsely leave the external Choice comparison open.
- The recommendation at `README.md` Repository integration to place this under the formal project's Research subtree is an external-document suggestion. It does not override the repository's intake destination rule. If redelivered, this belongs with the existing closure-kernel report spine.

## Modest fresh checks of recoverable artifacts

All drivers and helpers actually executed were read before execution. The independent machine auditor's strict-affine helper is byte-identical to the previously read geometric-counter copy. All commands ran on `/tmp/zfc-intake-158/run55` with `timeout 120s uv run --no-project --offline python -B`; no network, third-party package, compiler, version query, dependency build, git mutation or maintained edit occurred.

1. `verify.py --skip-manifest` returned **exit 1**, exactly at line 59 with `FileNotFoundError` for `work/theory_audit/check_affine_certificate.py`. No manifest was checked. Full log: `review-logs/quick-audit.log`. This failure is preserved rather than bypassed and described as a full-suite PASS.
2. The available `work/state_reduction/audit_modified_source.py --repo source/ProveIt --source experiments/direct-negation255/source.json --table experiments/direct-negation255/machine_255_oldlabels.tm --output review-logs/machine255.json` returned **exit 0** in 6.074 seconds. It reconstructs 5,650 leaves/7,311 guarded cases; all 7,311 conditional affine cases pass; all 55 protected box rows are unchanged; the exact 82,552-step whole-tape blank bootstrap matches; all **21,933** complete-frame literal trials pass over **11,257,202** microsteps, covering all 510 rows with boot. The regenerated record matches the delivered independent audit in every field except `elapsed_seconds`. This validates those finite table/frame facts under the stated inherited box contracts. It does not prove the changed source's semantics or provide a new kernel theorem.
3. Author-written `review-logs/recovered-checks.py` returned **exit 0**. It independently parses the baseline literal program and checks all 6,460 leaves against the supplied 203-node decoder; reconstructs the exact six stored fold recipes from 261 to 255 states; verifies the full old-label/normalized table correspondence, start 0 and halt 255; and checks the negation identity for x=0,…,10000. The small identity sample supplements the ordinary algebraic proof; it is not its justification. Driver, log and JSON are preserved alongside the other logs.

No partial journal replay was started: even success on 32 available journals would not close the promised 36-domain census. No missing proof source was reconstructed or silently substituted. No Lean/Coq/compiler or PDF build was attempted. Review stopped after these modest checks, as root directed.

## Useful ideas retained for later work

The pairing-shift negation identity is a concrete, sound simplification to revisit if complete occurrence/call-condition evidence is redelivered. It fits the maintained generic Pair plus Scale4 interfaces. The context-sensitive code-generation issue should be addressed before trusting rotated-DAG fingerprints. Phase-dependent affine representations could guide optimization, but their comparisons/restoration loops must be charged; the reported invariant alone removes no state. None of these partial observations changes the pending disposition or supports a new state record.
