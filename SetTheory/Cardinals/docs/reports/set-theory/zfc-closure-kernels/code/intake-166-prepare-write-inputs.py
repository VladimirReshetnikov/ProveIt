"""Own static scratch writer: map already reviewed prose and existing evidence.
No supplied code or staging helper is imported/executed; no repository writes.
"""
from pathlib import Path
import hashlib, json, difflib, ast

W = Path('/tmp/zfc244-248bc05936-inspection/intake')
V = W / 'write-v2'
P = W.parent / 'zfc244-compensated-routing-20261018'
R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
H = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
C = 'Computability/BusyBeaver/Research/ZFC/candidate-compensated244'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p): return {'path': str(p), 'sha256': sha(p), 'bytes': Path(p).stat().st_size}
files = []
targets = set()
def add(src, dest, role, before=None):
    src = Path(src)
    assert src.is_file() and dest not in targets
    row = {'source': str(src), 'target': dest, 'sha256': sha(src), 'bytes': src.stat().st_size, 'role': role}
    if before is not None: row['replace_before_sha256'] = before
    else: assert not (R / dest).exists(), dest
    files.append(row); targets.add(dest)
def evidence(src, name, role='immutable existing intake/replay evidence; no new execution'):
    add(src, H + '/data/intake-166-' + name, role)
def code(src, name): add(src, H + '/code/' + name, 'exact own author/root/reviewer support source; invocation status remains in records')

before = R / H / 'README.md'
old = before.read_text()
assert old.count('This report now reconciles sixty-nine manuscripts.') == 1
new = old.replace('This report now reconciles sixty-nine manuscripts.', 'This report now reconciles seventy manuscripts.')
paragraph = '''Batch 166 adds the [compensated 244-state reduction](intake-166.md) as source 70.
The ordinary proof deletes old state 122 and changes four retained Routing245
rows, preserving halting from the shared start on every binary tape. Both local
checkers, the exact 407,951-step blank startup and the separate complete 8,391-case
runtime replay pass; the latter checks 2,315,075 symbolic rules and all 488 rows.
The existing 245-state external Lean endpoint remains the checked baseline at
this intake checkpoint; a complete 244-state Lean endpoint and internal PA
calibration remain open. The accompanying equational conversion has a complete
2,324-bit packet but no compiled binary machine. Search scopes and supplemental
variants remain distinct from the principal direct proof.

| Source | Delivered archive | Reviewed contribution |
| --- | --- | --- |
| 70 | `zfc244-compensated-routing-20261018.zip` | Compensated one-state fold, direct all-tape halting proof, complete principal replay, exact startup and a separate equational backend. |

Placement `6619bd0002` preserves 170 ancillary files unchanged; 21 originals
remain archive-only, with all 191 members recoverable. See [recovery and replay](intake-166-reproduction.md)
and the separate [maintained candidate inputs](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-compensated244/README.md).
The report keeps the original theory and attribution. It adds no unconditional
consistency/nonhalting or minimality claim. The base article is unchanged and
the collection remains 290 reports; eighteen other archives remain queued.

'''
assert new.count('## Sources, overlap and base\n') == 1
new = new.replace('## Sources, overlap and base\n', paragraph + '## Sources, overlap and base\n')
with (V / 'host-README.md').open('x') as f: f.write(new)
with (V / 'host-README.diff').open('x') as f:
    f.write(''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=H+'/README.md', tofile=H+'/README.md')))
add(V/'host-README.md', H+'/README.md', 'authored reconciliation insertion and source count; historical text retained', sha(before))
for n in ['intake-166.md', 'intake-166-reproduction.md']:
    add(V/n, H+'/'+n, 'authored final reconciliation/reproduction; actual terminal evidence')
add(V/'source70-dossier.md', H+'/intake-166-source-70.md', 'terminal successor source dossier; v1 retained separately')
code(W/'recover_166.py', 'recover_166.py')
code(W/'place_166.py', 'intake-166-place.py')
code(W/'write_166.py', 'intake-166-write-helper.py')
code(Path(__file__), 'intake-166-prepare-write-inputs.py')
code(W.parent/'inventory_intake.py', 'intake-166-inventory.py')
code(W/'prepare_placement.py', 'intake-166-prepare-placement.py')
code(W/'review_full_runtime.py', 'intake-166-review-full-runtime.py')
for name, dest in [('placement-proposal.json','placement.json'),('inventory.json','inventory.json'),
                   ('literal-identity.json','literal-identity.json'),('find-object-output.txt','history-find-object.txt'),
                   ('find-object-stderr.txt','history-find-object-stderr.txt'),('full-runtime-evidence-review.json','full-runtime-review.json'),
                   ('dossier-freeze.json','dossier-v1-freeze.json'),('candidate-publication-map.json','candidate-v1-proposal.json')]:
    evidence(W/name,dest)
for name in ['source70-dossier.md','candidate-README.md','candidate-publication-plan.md']:
    evidence(W/name,'historical-v1-'+name,'immutable pre-terminal prose/proposal; superseded pending-status clause retained')
for name in ['source70-dossier.md.diff','candidate-README.md.diff','terminal-successor.json','host-README.diff']:
    evidence(V/name,name)

for name in ['placement.json','staged-review.json','commit-message.txt','stage-paths.txt','retire-paths.txt']:
    evidence(Path('/tmp/zfc-intake-166-placement')/name,'root-'+name)
evidence(Path('/tmp/zfc-intake-166-recovery-check/recovery.json'),'recovery.json')
review = Path('/tmp/zfc244-ordinary-proof-review')
for src,dest in [('review.json','ordinary-review.json'),('portable-evidence-review.json','portable-review.json')]: evidence(review/src,dest)
code(review/'review_source.py','intake-166-review-ordinary.py')
code(review/'review_portable.py','intake-166-review-portable.py')
for f in sorted((review/'reviewer-history').rglob('*')):
    if f.is_file(): evidence(f,'ordinary-reviewer-history-'+str(f.relative_to(review/'reviewer-history')).replace('/','-'))

replay = Path('/tmp/zfc244-root-replays')
evidence(replay/'root-source-review.json','root-source-review.json')
code(replay/'run_replays.py','intake-166-root-run-replays.py')
code(replay/'retain_local_replay.py','intake-166-root-retain-local.py')
for mode in ['portable','full-runtime']:
    for name in ['execution.json','verification.json','stdout.log','stderr.log']:
        evidence(replay/mode/name,mode+'-'+name+('.txt' if name.endswith('.log') else ''))
for f in sorted((replay/'retained-local').iterdir()):
    if f.is_file(): evidence(f,'retained-local-'+f.name+('.txt' if f.suffix=='.log' else ''))
rt = replay/'retained-local/package/runtime'
for name in ['contextual_fold_proof.json','retained-independent.json','retained-boot.json','rebuild_manifest.json']:
    evidence(rt/name,'retained-local-'+name)

candidate = json.loads((W/'candidate-publication-map.json').read_text())
for row in candidate['files']:
    if row['mode']=='unchanged_delivered_input': add(row['source']['path'], row['target'], row['mode'])
add(V/'candidate-README.md', C+'/README.md', 'authored candidate status/attribution; complete fresh replay but whole244 endpoint open')
provenance = {
    'status':'EXACT_CANDIDATE_INPUTS_AND_ORDINARY_PROOF', 'arrival':candidate['arrival'],
    'collection_placement':candidate['placement_commit'], 'repository_pin':'cb7984df14aed713269d5a596a27d33321cc2c19',
    'inherited_upstream':'c132d7eae8158cd3a9850ea3eb7251158c3dd821',
    'exact_inputs':[r for r in files if r['target'].startswith(C+'/') and r['role']=='unchanged_delivered_input'],
    'ordinary_review':d(review/'review.json'), 'portable_review':d(review/'portable-evidence-review.json'),
    'full_runtime_review':d(W/'full-runtime-evidence-review.json'),
    'full_runtime_execution':d(replay/'full-runtime/execution.json'),
    'fresh_complete_counts':{'cases':8391,'symbolic_rules':2315075,'binary_rows':488,'minimum_steps':13},
    'scope':'Ordinary direct halting proof plus fresh executable premises; no complete244 Lean or internalPA endpoint claimed by this publication.',
    'attribution':'Mira-Cult original calculus/program; Jeff Ketchersid verification; Andrew James Wade compiler framework; ProveIt Routing245; incoming18Oct2026 compensated fold/proof/checks/equational experiment prepared for Vladimir Reshetnikov. No additional author identity inferred.',
    'licenses_and_complete_delivery':H,
}
with (V/'candidate-provenance.json').open('x') as f: f.write(json.dumps(provenance,indent=2)+'\n')
add(V/'candidate-provenance.json',C+'/provenance.json','exact input/review identity and attribution, not a kernel record')

manifest = {
    'status':'READY_FOR_ROOT_SOURCE_REVIEW', 'batch':166, 'host_source':70,
    'placement':'6619bd0002a0771284cfda26d0e734f76cffaaa4', 'collection_reports':290,
    'base_article':{'path':H+'/article.tex','sha256':sha(R/H/'article.tex')},
    'placement_map':d(W/'placement-proposal.json'), 'files':files,
    'full_runtime':{'execution':str(replay/'full-runtime/execution.json'),'result':str(replay/'full-runtime/verification.json')},
    'status_boundaries':['Complete ordinary proof reviewed; complete principal executable replay passed.',
                         'Current245 externalLean baseline preserved; whole244 endpoint and PA remain separate.',
                         'Original delivery and basearticle unchanged; no new articlePDF; cataloguePDF still required separately.',
                         'v1 pending-status prose and both existing-source reviewer draft histories retained.'],
    'builder_execution':'Not invoked; root alone reads/stages/installs/commits.',
}
ast.parse((W/'write_166.py').read_text())
with (W/'write-inputs.json').open('x') as f: f.write(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files':len(files),'plus_self_manifest':len(files)+1,'inputs_sha256':sha(W/'write-inputs.json'),'helper_sha256':sha(W/'write_166.py'),'host_before_sha256':sha(before)},indent=2))
