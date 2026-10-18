"""Own scratch-only write proposal; no maintained writes or supplied execution."""
from pathlib import Path
import hashlib,json,difflib,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc-intake-165-planning');O=W/'write-final';O.mkdir(exist_ok=False)
H=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
place=subprocess.check_output(['git','-C',str(R),'rev-parse','500381f8f1']).decode().strip()
for name in ['intake-165.md','intake-165-reproduction.md']:
 s=(W/name).read_text().replace('@PLACEMENT_COMMIT@',place).replace('../../../../../../../Computability/','../../../../../../Computability/')
 if name=='intake-165.md':
  s=s.replace('No new smaller consistency machine.','No new smaller consistency machine.')
  s=s.replace('The new ordinary proofs and their assumptions are detailed', 'The finite invariant starts with all nine root fields arbitrary in its broad form. The narrower cutoff-4 root masks also admit any positive N with A = X = Y = 0 and the other fields arbitrary; this is an execution invariant, not a replacement for the safe formula/cache/stack premises of logical calibration. All 472 rows directly inspected by the original symbolic instruction traces still occur after the six exclusions. The separate register-box contracts remain necessary.\n\nTwo origin-prioritized greedy congruence orders additionally reduce rotation 42 from 254 to 249 initialized runtime states, preserving all 42 macro-used rows and passing the delivered guarded replay. These results have no verified blank initialization. The shortened-detector screens require 25,173 finite frames, at most 2,500 transitions and 16 dispatcher visits, within a 512-cell tape window; their completed finite rejection is not unrestricted semantic impossibility.\n\nThe new ordinary proofs and their assumptions are detailed')
  s=s.replace('Attribution follows the unchanged', 'The report also retains its incompleteness caveat: for a correctly calibrated machine, Con(ZFC) gives nonhalting and ZFC-unprovability of that nonhalting statement. Bare consistency alone does not exclude a ZFC proof of the false existential halting statement; a suitable Σ₁-soundness assumption gives the stronger two-sided conclusion. No two-sided independence claim from consistency alone is added here.\n\nAttribution follows the unchanged')
  s=s.replace('A useful next formalization is the positive finite-block simulation theorem with a whole-frame workspace relation.', 'The existing `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimePerm252.lean` already proves positive-segment halting equivalence through `PositiveSimulation.step` and `halts_iff`, with exactly one source instruction per segment; `RuntimeInstanceRouting245` reuses that contract. A useful next formalization is the report\'s positive **multi-instruction** source-block extension with a whole-frame workspace relation.')
 (O/name).write_text(s)
old=(R/H/'README.md').read_text();s=old.replace('Intake findings, 17 October 2026. This report now reconciles sixty-eight manuscripts.','Intake findings through 18 October 2026. This report now reconciles sixty-nine manuscripts.')
s=s.replace('The maintained 246-state machine closes\nthe external Lean comparison with Con(ZFC), improving the earlier checked\n252-state endpoint; its internal PA comparison remains open. Several deliveries discuss provability in ZFC instead, and retain that', 'The maintained [routed 245-state machine](../../../../../../Computability/BusyBeaver/Research/ZFC/routing245_binary.md) closes\nthe external Lean comparison with Con(ZFC), improving the earlier checked\n246- and 252-state endpoints; its internal PA comparison remains open. Several deliveries discuss provability in ZFC instead, and retain that')
s=s.replace('The candidate\nhas no new exact-table Lean endpoint or internal PA proof; the closed 246-state\nexternal theorem remains the checked baseline.', 'At that intake checkpoint, the candidate\nhad no new exact-table Lean endpoint or internal PA proof, and the closed 246-state\nexternal theorem was the checked baseline. The exact routed 245-state external\nendpoint has since closed; its PA internalization remains open.')
s=s.replace('See [recovery and execution scope](intake-164-reproduction.md). Six older queued\narchives remain pending; their scratch source numbers were provisional.', 'See [recovery and execution scope](intake-164-reproduction.md). Six older archives\nremained queued at that checkpoint; their scratch source numbers were provisional.')
insert='''Batch 165 adds [source blocks, workspace freedom and exact obstructions](intake-165.md)
as source 69. Positive source blocks may contain several instructions, while
all nine primary values and the clean tape relation remain protected. The
finite invariants, block controls and two rejected 245 tables provide research
methods and counterexamples, not a smaller calibrated machine. All 14 main
jobs and eight supplemental checks pass on disposable copies; the recorded
large searches remain distinct from fresh verification. See the [recovery and
replay instructions](intake-165-reproduction.md).

| Source | Delivered archive | Reviewed contribution |
| --- | --- | --- |
| 69 | `zfc-sub246-research-20261018.zip` | Positive multi-instruction source blocks, numeric invariants, workspace relations, exact rejection witnesses and scoped runtime experiments. |

Placement `PLACE` preserves 454 ancillary files unchanged; 12 article,
PDF, TeX and delivery files remain recoverable from the committed archive.
It also retires a byte-identical reintroduction of source 68, with all 273
original ancillary bindings checked in their original placement tree; that
repeat receives no new number. The source 69 report studies an older 246
reference. Its two rejected 245 tables are different from the now verified
routed 245 machine. This intake adds no PA theorem or stronger theory.
The base article remains unchanged, and the collection remains 290 reports.

'''.replace('PLACE',place[:10])
assert s.count('## Sources, overlap and base')==1
s=s.replace('## Sources, overlap and base',insert+'## Sources, overlap and base')
assert s!=old
(O/'README.md').write_text(s)
(O/'host-readme.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=str(H/'README.md'),tofile=str(H/'README.md'))))
meta={'status':'SOURCE_ONLY_WRITE_READY_FOR_FIDELITY_REVIEW','placement':place,'host_sources':69,'collection_reports':290,'base_article':{'path':str(H/'article.tex'),'sha256':sha(R/H/'article.tex')},'host_readme_before':sha(R/H/'README.md'),'files':[{ 'path':str(p),'sha256':sha(p)} for p in sorted(O.iterdir()) if p.is_file()],'no_build_or_supplied_execution':True,'old_write_drafts_preserved':True}
(O/'readiness.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
