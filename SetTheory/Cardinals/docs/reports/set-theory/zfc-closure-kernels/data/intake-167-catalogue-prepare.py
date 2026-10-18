from pathlib import Path
import argparse, json, hashlib, difflib

ap=argparse.ArgumentParser();ap.add_argument('--write',required=True);a=ap.parse_args()
assert len(a.write)==10 and all(c in '0123456789abcdef' for c in a.write)
root=Path('/home/codex/.codex/worktrees/ec20/Proofs')
out=Path('/tmp/zfc167-catalogue-proposal');assert not out.exists();out.mkdir()
files={}
def replace(text,old,new):
    assert text.count(old)==1,old
    return text.replace(old,new)
path='SetTheory/Cardinals/docs/reports/manifest.tex';old=(root/path).read_text();new=old
new=replace(new,'{\\normalsize 17 October 2026}','{\\normalsize 18 October 2026}')
new=replace(new,"reconciles seventy sources after batch~166's compensated 244-state reduction,\nfollowing batch~165's source-block methods and batch~164's routed 245-state\ncandidate; the collection remains 290 reports.","reconciles seventy-one sources after batch~167's loop-rotation 244-state\nconstruction, following batch~166's different compensated fold. Combining\nthe two gives a subsequent 243-state candidate; the collection remains\n290 reports.")
new=replace(new,'batch~166: zfc244-compensated-routing-20261018.zip (\\texttt{248bc05936})}', 'batch~166: zfc244-compensated-routing-20261018.zip (\\texttt{248bc05936}); batch~167: zfc244-loop-rotation-20261018.zip (\\texttt{d91a27b462})}')
new=replace(new,'{Seventy manuscripts reconciled without rewriting the seeded base article.','{Seventy-one manuscripts reconciled without rewriting the seeded base article.')
addition=r'''
Batch~167 adds source~71: a different 244-state construction by rotating one
source loop. For arbitrary natural register values, transfer-then-increment
and increment-then-test both finish after $3X+2$ source instructions with
$N$ increased by $X+1$, $X=0$, and the other registers unchanged. The context
check covers 8385 outside edges and excludes interior entry. The decoder
deletes old state~26 and changes three retained rows, leaving 6459 source
leaves and 8390 guarded cases. All seven primary replay jobs pass, including
2312438 expanded symbolic rules and the exact 407931-step whole-tape blank
prefix. Only read-one at old state~27 is unused; that state remains counted.
The separate sixteen finite research checks and source-family regenerations
also pass. They preserve the K/B/Peirce and fixed-falsity certificates,
equality fusion, split-bundle controls, conjunction/DNE families, retained
grammar witnesses, joint source interfaces and rejected NIP shortcuts.
Optional seed regeneration and discovery campaigns remain unexecuted and
scoped; the unused auxiliary whole-frame wrapper has a preserved indentation
defect, while the primary expanded entrypoint is valid.

The two reductions can be combined after checking every compensation
invariant and local block hypothesis against the rotated table. The resulting
243-state candidate deletes both old states~26 and~122. Its separate fresh
replay passes 8390 cases and 2314868 symbolic rules, with a 407967-step blank
prefix and positive progress. Five new Lean units check the exact tables and
their relative halting equivalence: 83 probes and 39 typed callers pass with
zero warnings. The ordinary argument supports the ZFC consistency calibration;
the rotation's complete source/runtime connection remains open in Lean, as
does the internal PA proof. The different compensated 244-state machine
retains the smallest closed external Lean consistency endpoint. No absolute
consistency, unconditional nonhalting, minimality or independence from bare
consistency alone is inferred.

Placement \texttt{5513e77ff1} and write \texttt{WRITE167} preserve 1007 ancillary
files and 37 archive-only members, all 1044 recoverable. Eighteen archives
remained queued at placement; a later arrival adds one more. The source is
pinned to \texttt{fd1adfa19f8}; incoming and subsequent repository work are
credited separately. The base article and delivered files remain unchanged.

'''.replace('WRITE167',a.write)
new=replace(new,'Machine engineering credits Mira-Cult, Jeff, Wade and mira-emmy\'s prior',addition+'Machine engineering credits Mira-Cult, Jeff, Wade and mira-emmy\'s prior')
files[path]=(old,new)
path='SetTheory/Cardinals/docs/reports/README.md';old=(root/path).read_text();new=old+f'''

Batch 167 adds source 71 from `d91a27b462` to
[ZFC closure kernels](set-theory/zfc-closure-kernels/intake-167.md), now 71
manuscripts and still 290 reports. Placement `5513e77ff1` preserves 1,007
ancillary files and 37 archive-only members; write `{a.write}` records the
loop rotation, complete ordinary proof and broader source-formalism research.
Seven primary jobs and sixteen separate finite research checks pass on copies.
The new 244-state table deletes old state 26; it has 6,459 source leaves,
8,390 guarded cases, 2,312,438 expanded symbolic rules and an exact
407,931-step blank prefix. The delivered auxiliary indentation defect is
preserved; the primary expanded entrypoint is valid. Optional seed generation
and discovery campaigns remain scoped and unexecuted.

The different compensated fold deletes old state 122. Checking its complete
local hypotheses against the rotated table permits a subsequent
[243-state candidate](../../../../Computability/BusyBeaver/Research/ZFC/candidate-combined243/README.md).
Its fresh expanded replay passes 8,390 cases and 2,314,868 rules, and its own
blank prefix takes 407,967 transitions. Five Lean units prove its relative
halting equivalence with rotation244, with 83 probes and 39 typed callers,
all without warnings. The ordinary proof supports the same ZFC consistency
calibration; the rotated source/runtime connection still needs a complete
Lean proof. Compensated244 remains the smallest closed external Lean
consistency endpoint, and internal PA calibration remains open. Neither
incoming package supplied the combined table. The base article and all
delivered files remain unchanged. Eighteen archives remained queued at
placement; a later arrival brings the queue to nineteen.
''';files[path]=(old,new)
path='docs/incoming/README.md';old=(root/path).read_text()
row=f'| 167 | One loop-rotation manuscript from `d91a27b462`: placement `5513e77ff1` adds source 71 to `set-theory/zfc-closure-kernels`, now 71 sources and still 290 reports. All 1,007 ancillary files preserved; 37 originals archive-only; 1,044 recoverable. Only this ZIP retired. | `{a.write}`: exact source rotation, complete runtime/startup, alternative formalisms and grammar research; full recovery and independent scoped reviews. Delivered files unchanged. | this commit | Seven primary jobs and sixteen finite research checks pass; 8,390 expanded cases, 2,312,438 rules and 407,931-step startup. The different 244 reductions combine into a subsequent 243 table: fresh 8,390-case/2,314,868-rule replay and 407,967-step startup; five Lean units prove relative halting equivalence (83 probes/39 callers, zero warnings). Full rotated/combined Lean consistency and internal PA endpoints remain open; compensated244 remains the closed external baseline. Catalogue rebuilt and affected pages visually reviewed separately. |\n'
lines=old.splitlines(True);index=next(i for i,s in enumerate(lines) if s.startswith('| 166 |'));lines.insert(index+1,row);new=''.join(lines);files[path]=(old,new)
rows=[]
for path,(old,new) in files.items():
    dst=out/'files'/path;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(new)
    rows.append(dict(path=path,source=str(dst),before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest()))
(out/'map.json').write_text(json.dumps(rows,indent=2)+'\n')
(out/'catalogue.diff').write_text(''.join(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=path,tofile=path)) for path,(old,new) in files.items()))
print(out/'map.json')
