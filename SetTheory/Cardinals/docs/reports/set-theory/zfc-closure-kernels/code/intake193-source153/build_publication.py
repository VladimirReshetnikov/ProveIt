#!/usr/bin/env python3
"""Own scratch-only evidence packager; no supplied execution or canonical writes."""
from pathlib import Path
import gzip,hashlib,json,shutil,difflib,ast
W=Path('/tmp/zfc-intake193/small');E=Path('/tmp/zfc-intake193/source153-execution')
B=Path('/tmp/zfc-intake193/source153-publication-v2');B.mkdir(exist_ok=False)
H=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
D=H/'data/intake193-source153';C=H/'code/intake193-source153'
F=B/'files'; records=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(src,rel,compress=False):
 raw=src.read_bytes();target=F/rel
 if compress:target=target.with_name(target.name+'.gz')
 target.parent.mkdir(parents=True,exist_ok=True)
 target.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0) if compress else raw)
 if compress:assert gzip.decompress(target.read_bytes())==raw
 records.append({'destination':str(target.relative_to(F)),'source':str(src),'bytes':target.stat().st_size,'sha256':sha(target),'encoding':'gzip exact original bytes'if compress else'identity','original_bytes':len(raw),'original_sha256':hashlib.sha256(raw).hexdigest()})
def write(rel,text):
 p=F/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
 records.append({'destination':str(rel),'source':'authored in build_publication.py','bytes':p.stat().st_size,'sha256':sha(p),'encoding':'identity'})
for name in ['dossier.md','review.json','reviewed-inputs.json','replay-plan.json','inventory.json','inventory-roles.json','current-exact-matches.json','zero-guard-comparison.json']:
 put(W/name,D/'review'/name)
put(W/'actual-review.json',D/'actual-review.json');put(E/'actual.json',D/'actual.json')
for section in ['outputs','logs']:
 for p in sorted((E/section).rglob('*')):
  if p.is_file():put(p,D/section/p.relative_to(E/section),p.stat().st_size>=64000)
for name in ['audit_actual.py','run_selected.py']:
 ast.parse((W/name).read_text());put(W/name,C/name)
put(E/'run.py',C/'history/original-root-runner.py')
put(W/'write_review_metadata.py',C/'history/original-metadata-writer.py')
put(W/'history/portable-draft1/run_selected.py',C/'history/portable-draft1/run_selected.py')
put(W/'build_publication_v2.py',C/'build_publication.py')
diff=''.join(difflib.unified_diff((E/'run.py').read_text().splitlines(True),(W/'run_selected.py').read_text().splitlines(True),fromfile='original-root-runner.py',tofile='run_selected.py'))
write(C/'runner-portability.diff',diff)
write(D/'README.md','''# Source153: six selected fresh checks

All six root-executed leaves pass their semantic result gates. The independent
[actual review](actual-review.json) records92 input/command/output/trace-metadata
checks; it did not rerun the algebra, source programs or machines. The preserved
[root aggregate](actual.json) intentionally retains its original
`SIX_SELECTED_PROCESSES_EXIT_ZERO_PENDING_RESULT_AUDIT` status. Read it together
with the separate actual review rather than rewriting historical evidence.

The jobs cover the two new Peirce matrices, residual-parameter compiler blocks,
exact208-DAG source plus arithmetic/command-tree audits, the different two-adic
helper/cost experiment, three literal table/source reconstructions, and two weak
caller counterexamples. Both counterexamples reproduce cached/result1 instead
of0. Their blank reachability is not asserted.

No optional checker, full symbolic primitive runtime, ancestor wrapper, manifest
suite, search or proof assistant ran. The three table counts218/219/223 are
reconstruction results, not three newly accepted machines. The residual source
has an ordinary all-natural calibration argument; its223-state binary startup
is still open. This intake supplies no new<=216 candidate.

The [full dossier](review/dossier.md), [initial source review](review/review.json)
and [input pins](review/reviewed-inputs.json) remain frozen as pre-execution
records. In particular, the compound fourth-term obstruction is subsumed by
Sources145/146; the two Peirce models have different K scopes. The dossier's
explicit cofinal START_U argument is a reviewer elaboration, not a new test.

All raw stdout/stderr and generated outputs are retained below. Files ending
`.gz` decompress to exact original bytes; publication-map.json records both
hashes and original lengths. Large generated sources and the four complete CSV
traces are compressed. The pristine/execution packet and unchanged ancestor
ZIP are not duplicated: recover Source153 from its arrival archive. No delivered
source was edited for the fresh run. Use the separately documented
[portable path adapter](../../code/intake193-source153/README.md) for a fresh run.

Attribution: submission authors supplied the mathematical/code artifacts;
root selected and executed the six jobs; drop_contract performed the source
and actual-record reviews and authored the packaging/portable path adapter.
The portable adapter was syntax/source-read only, never substituted into the
recorded actual run.
''')
write(C/'README.md','''# Reproduce the selected Source153 leaves

Recover Source153 from batch193, preserving its internal
`ZFC_218_Research_2026-10-20` layout. The two unchanged baseline files are already
retained under the host data directory; no ancestor script needs to run.
From the repository root, using a nonexistent scratch output path:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake193-source153/run_selected.py \\
  --packet /tmp/recovered153/ZFC_218_Research_2026-10-20 \\
  --plan SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review/replay-plan.json \\
  --reviewed-inputs SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review/reviewed-inputs.json \\
  --baseline-table SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-k219.native.tm \\
  --baseline-source SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-sites219.json \\
  --output /tmp/source153-fresh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake193-source153/audit_actual.py \\
  --execution /tmp/source153-fresh \\
  --review SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review \\
  --output /tmp/source153-fresh/actual-review.json
```

Replace only the recovered packet and scratch output locations. Python assertions
must be enabled; no `-O`/`-OO`. The adapter preserves the exact six selected argv
leaves, fresh disposable packet copy, inherited environment with optimization
removed,120-second per-process cap, separate streams and stop-on-first-failure.
It adds portable explicit paths and preflight checks of reviewed code/baseline
bytes, and saves its exact runner in the fresh output for the audit. An unexecuted
first adapter draft omitted that runner copy; it remains in history/portable-draft1.
The corrected adapter was source-reviewed and AST-parsed but not executed. The original
executed root runner is retained in `history/`; `runner-portability.diff` discloses
all changes. None changes delivered code or mathematical checks.

The own audit reads records only: no delivered imports, tests, simulator or
compiler. On a new execution directory it verifies both process and semantic
result gates and records new hashes/timing. It can also read the preserved
original execution directory while present. Published compressed evidence is a
storage format; it is not itself the expected live execution layout.

The actual run and independent record audit are under
[the evidence directory](../../data/intake193-source153/README.md). Original
absolute scratch paths inside historical plans/results remain provenance, not
instructions to reuse or overwrite those locations.
''')
# Publication map avoids a self hash; the root map and installed copy are identical.
mapdata={'status':'SCRATCH_PUBLICATION_READY','source':153,'files':records,'excluded':'No duplicate pristine/execution package, baseline files or embedded predecessor archive. Original outputs/logs and own review code are complete.','root_actual_sha256':sha(E/'actual.json'),'actual_review_sha256':sha(W/'actual-review.json'),'portable_adapter_status':'Source-read and AST-parsed only; not invoked.'}
raw=(json.dumps(mapdata,indent=2)+'\n').encode();(B/'publication-map.json').write_bytes(raw)
p=F/D/'publication-map.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
summary={'status':'READY','mapped_files':len(records),'total_install_files':len(records)+1,'installed_bytes':sum(p.stat().st_size for p in F.rglob('*')if p.is_file()),'map_sha256':sha(B/'publication-map.json'),'all_gzip_roundtrips_checked':True}
(B/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
