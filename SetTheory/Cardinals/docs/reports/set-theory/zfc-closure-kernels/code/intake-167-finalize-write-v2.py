from pathlib import Path
import re,difflib,json,hashlib
W=Path(__file__).resolve().parent;D=W/'write-v2';D.mkdir(exist_ok=True);R=Path('/home/codex/.codex/worktrees/ec20/Proofs');H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md'
for f in ['intake-167.md','intake-167-reproduction.md','intake-167-source-71.md']:
 s=(W/'write-v1'/f).read_text()
 # Prose spacing only; never modify code spans or link destinations.
 for token in ['all','with','has','old','state','start','dispatcher','halt','including','source','through','plus','span','header','marker','head','after','by','only','remaining','exactly','of','in','their','its','totaling','since','for','to','from','than','and','the','Each','each','contains','supplies','has','total','uses','width','at','Source']:
  s=re.sub(r'\b'+token+r'(?=\d)',token+' ',s)
 for token in ['states','rows','steps','transitions','seconds','spare','one-cells','source','guarded','outside','cases','symbolic','finite','retained','ancillary','archive-only','logical','working','nodes','fields','representatives','source-instruction','proposals','productions','controls','is']:
  s=re.sub(r'(?<=\d)(?='+token+r'\b)',' ',s)
 s=s.replace('QC 244','QC244').replace('report\'s earlier expanded','report\'s earlier expanded')
 if f=='intake-167.md':
  a="A separate root invocation of `formalism_verify.py` passes the supplied propositional certificates and finite matrices in0.064 seconds. The larger optional auxiliary campaign is tracked separately; no planned job is counted as executed here."
  if a not in s:a=a.replace('in0.064','in 0.064')
  b="Root additionally completes **16 non-search auxiliary jobs**: the separately run logical-certificate check plus15 direct checks/family regenerations. The [auxiliary execution](data/intake-167-auxiliary-execution.json) and [independent output review](data/intake-167-auxiliary-review.json) bind all outcomes. All1,044 original files in that disposable copy remain byte-identical to delivery; the regenerated families and four public-backend tables match delivered bytes. Three newly named joint-family outputs match their delivered counterparts exactly. The other three newly created dirty/pruned outputs satisfy the recorded postconditions. The retained grammar audit covers11 selected witnesses. Each of the15 new jobs takes less than one second in the measured environment; the logical check takes0.064 seconds. The two optional selected seed regenerations and every discovery search remain unrun. These16 jobs are separate from the seven primary machine jobs."
  assert a in s;s=s.replace(a,b)
  s=s.replace('Separately developed ordinary transfer and quick replay; complete expanded/kernel claims require their own records','Subsequent ordinary transfer, complete expanded replay and relative Lean comparison; complete consistency endpoint open')
  old="Any later expanded replay or Lean theorem is published as additional evidence rather than retroactively attributed to this manuscript."
  new="The subsequent [complete expanded243 record](data/intake-167-combined243-expanded-verification.json) now passes8,390 cases and2,314,868 symbolic rules in509.285 seconds, covering485 rows with only `(27,1)` unused; its [independent output review](data/intake-167-combined243-expanded-review.json) remains separate. The [relative Lean comparison](../../../../../../Computability/BusyBeaver/Research/ZFC/combined243_simulation.md), published in8778a52515, checks five units with83 probes and39 typed callers, all zero warnings, and proves243↔QT244 halting for blank and arbitrary finite Core tapes from the shared start. This relative theorem does not close the rotated machine's source-calibration bridge. The complete243 Lean consistency endpoint and internal PA comparison remain open. These later results are not attributed to the incoming manuscript."
  assert old in s;s=s.replace(old,new)
 elif f=='intake-167-reproduction.md':
  s=s.replace('Those proposed caps are unmeasured safety limits. Planned jobs are not represented as actual executions.','Those proposed caps are safety limits, not expected runtimes. Root has since completed all16 direct checks/family regenerations, counting the separate logical check once; the two optional selected seeds remain unrun. See the [actual auxiliary record](data/intake-167-auxiliary-execution.json) and [independent output review](data/intake-167-auxiliary-review.json). All15 later jobs finish in less than one second each, and their exact regenerated outputs match delivery where counterparts exist.')
  s=s.replace('Expanded or Lean results for that machine require their own exact sources and records.','Its separate [expanded record](data/intake-167-combined243-expanded-verification.json) now passes8,390 cases/2,314,868 rules in509.285 seconds. Its [relative Lean comparison](../../../../../../Computability/BusyBeaver/Research/ZFC/combined243_simulation.md) proves243↔QT244 halting; it is not a complete consistency endpoint. These results have their own sources and records and are not reproduced by the unmodified QT commands.')
 else:
  s=s.replace('the larger optional auxiliary campaign is tracked separately','the larger optional auxiliary campaign is tracked separately')
  s=s.replace('proposed further auxiliary jobs remain outside this frozen primary review.','the further15 auxiliary jobs have their own [existing-output review](data/intake-167-auxiliary-review.json), SHA256 `7a249ef4eb69faa62e51493d371d1fc4f29ef23575b8c8f7a02b42f3a0a0b6ad`, with2,341 comparisons. That separate review preserves all1,044 original run-copy files and checks the newly created outputs; the two selected seed jobs remain unrun.')
  s=s.replace('Root\'s subsequent combined243 quick replay is separately linked and retains its narrower blank/affine/finite-literal scope. A filename or code draft does not supply a completed final theorem.','Root\'s subsequent combined243 quick replay retains its narrower blank/affine/finite-literal scope. The distinct expanded record later passes8,390 cases and2,314,868 rules; its independent receipt is `bc5b9abe15d562c5dda221d7f505247a1c54e95f6add9f51ef8dd403bd343dae`. Five new Lean units check83 probes/39 callers, proving the relative243↔QT244 theorem on finite Core tapes and blank input. The complete243 consistency endpoint and PA bridge remain open. A relative endpoint must not be promoted to an absolute calibration.')
 # Apply spacing to newly inserted prose too, with explicit common tokens.
 for word in ['all','plus','these','These','of','with','in','passes','takes','covers','proves','the','further','own','check','complete','relative','separate']:
  s=re.sub(r'\b'+word+r'(?=\d)',word+' ',s)
 s=s.replace('further15','further 15').replace('all16','all 16').replace('and2,','and 2,').replace('and39','and 39').replace('covering485','covering 485').replace('takes0.','takes 0.').replace('with2,','with 2,')
 (D/f).write_text(s);(D/(f+'.diff')).write_text(''.join(difflib.unified_diff((W/'write-v1'/f).read_text().splitlines(True),s.splitlines(True),fromfile='preserved-v1/'+f,tofile='selected-v2/'+f)))
s=H.read_text();old=s;assert s.count('This report now reconciles seventy manuscripts.')==1;s=s.replace('This report now reconciles seventy manuscripts.','This report now reconciles seventy-one manuscripts.',1)
a='The maintained [routed 245-state machine](../../../../../../Computability/BusyBeaver/Research/ZFC/routing245_binary.md) closes\nthe external Lean comparison with Con(ZFC), improving the earlier checked\n246- and 252-state endpoints; its internal PA comparison remains open.'
b='The maintained [compensated 244-state machine](../../../../../../Computability/BusyBeaver/Research/ZFC/compensated244_binary.md) closes\nthe external Lean comparison with Con(ZFC), improving the earlier checked\n245-, 246- and 252-state endpoints; its internal PA comparison remains open.'
assert a in s;s=s.replace(a,b,1)
block='''Batch 167 adds [loop-rotation244 and its companion source research](intake-167.md)
as source 71. Its exact source loop saves old state 26, independently of the
compensated fold's old state 122. All seven primary checks pass, including the
407,931-step blank prefix and 8,390-case expanded replay with 2,312,438 rules.
Sixteen separate non-search auxiliary jobs also pass; the two optional selected
seed regenerations and discovery searches remain unrun. Source/grammar and
propositional negative results keep their stated scopes.

| Source | Delivered archive | Reviewed contribution |
| --- | --- | --- |
| 71 | `zfc244-loop-rotation-20261018.zip` | Universal source loop rotation, exact244 table and full runtime, fixed-width AX bridges, alternative bases, fusion/split controls, grammar research and scoped NIP reductions. |

Placement `5513e77ff1` preserves 1,007 ancillary files unchanged, with 37
archive-only members and all 1,044 recoverable. See [recovery and reproduction](intake-167-reproduction.md).
The separately developed [combined243 candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-combined243/README.md)
combines both changes after checking the full compensation hypotheses. Its
fresh 407,967-step startup, 8,390-case expanded replay and
[relative Lean243↔QT244 theorem](../../../../../../Computability/BusyBeaver/Research/ZFC/combined243_simulation.md)
are subsequent repository results, not a243 table delivered in this ZIP.
The ordinary consistency calibration is supported, but the complete243 Lean
consistency endpoint and internal PA theorem remain open. The already closed
compensated244 external endpoint concerns a different machine. The delivered
base article remains unchanged; the collection still has290 reports.

'''
assert s.count('## Sources, overlap and base')==1;s=s.replace('## Sources, overlap and base',block+'## Sources, overlap and base',1)
s=s.replace('exact244','exact 244').replace('not a243','not a 243').replace('complete243','complete 243').replace('has290','has 290')
(D/'host-README.md').write_text(s);(D/'host-README.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='maintained/README.md',tofile='proposed/README.md')))
(W/'write-draft-status.json').write_text(json.dumps({'status':'FINAL_PROSE_FOR_ROOT_READ','version':'write-v2','host_before_sha256':hashlib.sha256(H.read_bytes()).hexdigest(),'paths':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in D.glob('*.md')},'no_maintained_mutations':True,'scope':'Root-owned catalogue and Research/ZFC README untouched.'},indent=2)+'\n')
print(json.dumps({'files':[str(p) for p in D.glob('*.md')]}))
