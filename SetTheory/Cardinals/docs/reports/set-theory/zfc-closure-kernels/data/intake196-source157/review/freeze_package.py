#!/usr/bin/env python3
"""Freeze reviewed Source157 evidence; no proof execution or repo mutation."""
from pathlib import Path
import hashlib,json,shutil,ast
P=Path('/tmp/zfc-intake196/scanner/extracted/ZFC_217_Scanner_Source_Research_2026-10-21')
R=Path('/tmp/zfc-intake196/source157-review');A=Path('/tmp/zfc-intake196/source157-execution/run1');B=Path('/tmp/zfc-intake196/source157-publication')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
full=['README.md','STATUS.json','report.tex','sections/results.tex','sections/scanner.tex','sections/source.tex','sections/search.tex','sections/formalism.tex','sections/reproduction.tex','source-layout/source-results.tex','source-layout/README.txt','formalism/formalism-results.tex','formalism/seed/seed_calibration.tex','formalism/README.md','formalism/seed/README.md','experiments/discovery/README.md']
plan=json.loads((R/'replay-plan.json').read_text());full+=[r['path']for r in plan['inspected_closure']]
full+=['code/audit_runtime_premise.py','code/symbolic_premise.py','code/verify_candidate_runtime.py','vendor/runtime/symbolic_runtime.py','vendor/runtime/independent_runtime.py']
assert len(set(full))==len(full)
for f in R.glob('*.py'):ast.parse(f.read_text())
actual=json.loads((R/'actual-review.json').read_text());assert actual['status']=='ACTUAL_ARTIFACT_REVIEW_PASS'
review=dict(status='SOURCE_MATHEMATICS_AND_SELECTED_REPLAY_REVIEW_COMPLETE',author='drop_contract',role='Full ordinary proof/source review; author and executor of selected replay; separate own read-only artifact audit, no second-agent peer claim.',source=157,repository_checkpoint='704b87442afbd571833a628cd558f1d207fd8b2f',full_read=[dict(path=x,sha256=sha(P/x))for x in full],inventory=dict(path='inventory.json',sha256=sha(R/'inventory.json'),members=116,bytes=9599354),dossier=dict(path='dossier.md',sha256=sha(R/'dossier.md')),actual=actual['actual'],actual_review=dict(path='actual-review.json',sha256=sha(R/'actual-review.json'),checks=55),scope=['All main mathematical narrative and proof appendices read.','All seven local files in six selected job closure read; optional full runtime instrumentation and imported engine/helper read for premise scope.','Discovery drivers retained but not all independently reviewed or executed.','No scanner saving integrated; no new physical candidate accepted; no proof-assistant or full-calculus negative claim.'],known_preparation_failure='history/runner-draft1: AST-only missing-space error, before any execution. All six supplied selected jobs passed first execution.')
(R/'review.json').write_text(json.dumps(review,indent=2)+'\n')
B.mkdir(exist_ok=False);dest=B/'files'/'data'/'intake196-source157';(dest/'review').mkdir(parents=True)
for f in R.rglob('*'):
 if f.is_file():shutil.copy2(f,dest/'review'/f.relative_to(R))if (dest/'review'/f.relative_to(R)).parent.exists()else None
# Copy nested histories explicitly, preserving original bytes.
if (dest/'review'/'history').exists():shutil.rmtree(dest/'review'/'history')
shutil.copytree(R/'history',dest/'review'/'history')
for folder in ['logs','output','history']:shutil.copytree(A/folder,dest/'execution'/folder)
shutil.copy2(A/'actual.json',dest/'execution'/'actual.json')
for n in ['source157-integration.md','source157-reproduction.md']:shutil.copy2(R.parent/n,dest/n)
(dest/'README.md').write_text('''# Source157 fresh evidence\n\nSix selected ordinary checks passed. Start with source157-integration.md and source157-reproduction.md; full source review is review/dossier.md. Exact commands and raw outcomes are execution/actual.json, logs/ and output/. The original runner and source-only plan are preserved, including the one narrow manifest-loop adapter and the own AST-only draft failure. No rejected machine is promoted and no old full runtime was repeated. Recover original source/data from Source157 before using review/prepare_replay.py and review/run_selected.py.\n\nThe reviewer also authored/executed these checks. The separate 55-check artifact audit is not represented as a second-agent peer.\n''')
files=[dict(source=str(p),destination=str(p.relative_to(B/'files')),bytes=p.stat().st_size,sha256=sha(p))for p in sorted((B/'files').rglob('*'))if p.is_file()]
(B/'copy-map.json').write_text(json.dumps(dict(status='FROZEN_SCRATCH_COPY_BUNDLE',source=157,files=files,total_bytes=sum(x['bytes']for x in files),note='Destinations relative to the existing zfc-closure-kernels host. No canonical or Git writes performed.'),indent=2)+'\n')
print(json.dumps(dict(files=len(files),bytes=sum(x['bytes']for x in files),copy_map_sha256=sha(B/'copy-map.json'),review_sha256=sha(R/'review.json')),indent=2))
