#!/usr/bin/env python3
"""Read-only declared-source and retained-base provenance survey; no Lean."""
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tomllib
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
ROOT = HERE.parents[3]
BASE = Path('/tmp/current14-standard-fresh-build-20261104')
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
PINS = {
    'base_state': (BASE/'state.json', 'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'),
    'base_manifest': (PROJECT/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json', '1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'),
    'base_auditor': (PROJECT/'reviews/current14-fresh-base-independent/audit.py', '896d3ec17a86eaac845ed5857ae651c1b2de92fab15850ad39e7ab71a68b239c'),
    'base_receipt': (PROJECT/'reviews/current14-fresh-base-independent/receipt.json', '933a86784ad8d3d006e9915bcfb7dd2fa8726df504676f7c3bd7dab466f64754'),
    'base_outer': (PROJECT/'research/current14-standard-fresh-rebuild-preflight/terminal-observation.json', 'b930ff9d1015fa5834fe62c042566070032feaab50da4ae031aba3b2b82f2bb6'),
    'graph_draft': (PROJECT/'research/ordinary13-p73-share91-lean-draft/P73Shared91.lean', '6fca39ca8af4743a9be256594cd87b2628d6b8c8e87107b08d604556e43bf364'),
    'model_draft': (PROJECT/'research/ordinary13-p73-share91-lean-draft/P73Shared91Model.lean', 'c2aa3ec2a50c714f59bd4c61589e5fd460af2d641ed67111cbaabf2d97ddcdd5'),
    'endpoint_draft': (PROJECT/'research/ordinary13-p73-share91-lean-draft/P73Shared91Endpoint.lean', '7314625ae4cb2a4fb99c607be47f252444c5304d2bfc2c73c75160df820c3746'),
    'p72_progress': (P72/'progress.json', 'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a'),
    'p72_snapshot': (P72/'source-snapshot.json', '4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8'),
    'p72_survey': (PROJECT/'research/p72-current-base-source-survey/result.json', '29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954'),
    'p72_outer': (PROJECT/'research/p72-current-base-extension-build-attempt02/terminal/outer-terminal.json', 'a0cad18c8a85f74f1d69f57b7c510fa56a488726c66cbfc96421f88476acfa07'),
    'p72_archive': (PROJECT/'research/p72-current-base-extension-build-attempt02/terminal/stage-evidence.tar.gz', '884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541'),
    'p72_auditor': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/check.py', 'b33ae7fa683212592da52d7fc041a1b76381e7c6681f58f8ebcd53240642bd0f'),
    'p72_audit_result': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/result.json', 'a8eb52729db2c06ef98cb0b906efed0f63ab492f04a32d0cf40d1c4f6dd5b595'),
    'p72_base_audit': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/check_base.py', '138b6be1007d4e33fa85aaaa4e92785393111988cb3eafea8983dc1aa68bdc4e'),
    'p72_base_result': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/base-result.json', '8d414e5536ccde400665d868a7dbcbe91389c426ccf1ec58974de1ed69250910'),
    'p72_archive_audit': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/check_archive.py', 'ebaf066026b6801e62a51e4a1bd55f3d6f1e020953196833ee0f73d9a97cca14'),
    'p72_archive_result': (PROJECT/'reviews/p72-current-base-extension-attempt02-independent/archive-result.json', '3b11452849ea68cde0ceeced09973e97b220fd1ce34b3663cb8445c4d425b85d'),
    'failed03_state': (PROJECT/'research/current14-coherent-extension-refactor-retry03-runner/attempt01/state.json', '0095c4ea495ae04d0f74f80b841679a6d6d28763ae9334390cf0683ac51ebfa5'),
    'failed04_state': (PROJECT/'research/current14-coherent-extension-refactor-retry04-runner/attempt01/state.json', '990e53eff736586f58d5ad7bc5164da1a02f44a235804fc9631a443e4f32d679'),
    'failed03_auditor': (PROJECT/'reviews/current14-coherent-extension-refactor-retry03-failure-independent/check.py', '27938fc22747ce678419e18e5bc172e5658f22899c93ae0999fcf5426b17a444'),
    'failed03_result': (PROJECT/'reviews/current14-coherent-extension-refactor-retry03-failure-independent/result.json', 'cd465be14ba07b6d91fb87e0a1281ba51b6b5872aae169085a864cb8e3a0d3d2'),
    'failed04_auditor': (PROJECT/'reviews/current14-coherent-extension-refactor-retry04-failure-independent/check.py', '0a2105946a0a2131b19564ee8beee6d2184c2304d58def673f86405709397254'),
    'failed04_result': (PROJECT/'reviews/current14-coherent-extension-refactor-retry04-failure-independent/result.json', 'd134a7f2e4238d20b74ba29684ba0939e66e4a8516ab293e97db852da1edd12b'),
}
cache = {}
def sha(path):
    path = Path(path)
    if path not in cache:
        with path.open('rb') as f:
            cache[path] = hashlib.file_digest(f, 'sha256').hexdigest()
    return cache[path]
for label, (path, digest) in PINS.items():
    if not path.is_file() or sha(path) != digest:
        raise RuntimeError('missing or changed pin: ' + label)
state = json.loads((BASE/'state.json').read_text())
manifest = json.loads(PINS['base_manifest'][0].read_text())
receipt = json.loads(PINS['base_receipt'][0].read_text())
outer = json.loads(PINS['base_outer'][0].read_text())
assert state['status'] == 'PASS' and len(state['records']) == 1000
assert receipt['status'] == 'PASS_SINGLE_SOURCE_CURRENT_ARTIFACT_AUDIT'
assert receipt['base_state_sha256'] == PINS['base_state'][1]
assert outer['observed_session_exit'] == 0 and outer['build_state_sha256'] == PINS['base_state'][1]
base = {r['module']: r for r in state['records']}
assert len(base) == 1000 and set(base) == set(manifest['order'])
p72state = json.loads(PINS['p72_progress'][0].read_text())
p72snapshot = json.loads(PINS['p72_snapshot'][0].read_text())
p72survey = json.loads(PINS['p72_survey'][0].read_text())
p72outer = json.loads(PINS['p72_outer'][0].read_text())
p72result = json.loads(PINS['p72_audit_result'][0].read_text())
p72base = json.loads(PINS['p72_base_result'][0].read_text())
p72archive = json.loads(PINS['p72_archive_result'][0].read_text())
assert p72state['status'] == 'PASS' and p72state['phase'] == 'complete' and p72state['completed'] == 681
assert p72state['source_snapshot_sha256'] == PINS['p72_snapshot'][1]
assert p72outer['exit_code'] == 0 and p72result['status'] == 'PASS_RETAINED_STAGE_AUDIT'
assert p72result['progress_sha256'] == PINS['p72_progress'][1]
assert p72base['status'] == 'PASS_SHARED_BASE_RECHECK' and p72base['base_state_sha256'] == PINS['base_state'][1]
assert p72archive['status'] == 'PASS_RETAINED_ARCHIVE_COMPARISON'
assert p72archive['archive_sha256'] == PINS['p72_archive'][1] and p72archive['progress_sha256'] == PINS['p72_progress'][1]
assert p72archive['outer_receipt_sha256'] == PINS['p72_outer'][1] and p72archive['recorded_exit_code'] == 0
p72order = p72survey['extension_order']
assert len(p72order) == len(p72snapshot) == 681 and set(p72order) == set(p72snapshot)
assert not (set(p72order) & set(base))
assert set(p72survey['project_sources']) <= (set(p72order) | set(base))
p72index = {name:i for i,name in enumerate(p72order)}
archive_sha = {}
with tarfile.open(PINS['p72_archive'][0], 'r:gz') as archive:
    for member in archive:
        if member.isfile():
            f = archive.extractfile(member)
            archive_sha[member.name] = hashlib.sha256(f.read()).hexdigest()
p72rows = {}
for name, index in p72index.items():
    row = P72/'rows'/f'{index:04d}.json'
    key = f'rows/{index:04d}.json'
    if not row.is_file() or sha(row) != archive_sha.get(key):
        raise RuntimeError('P72 row absent or differs from audited archive: '+name)
    rec = json.loads(row.read_text())
    assert rec['module'] == name and rec['index'] == index and rec['source_sha256'] == p72snapshot[name]
    p72rows[name] = rec
libs = {r['name']: ROOT/r.get('srcDir', '.') for r in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']}
line_import = re.compile(r'^(?:public\s+)?import\s+([^\n-]+)')
issues = []
def source(name):
    root = libs.get(name.split('.')[0])
    return root/(name.replace('.', '/')+'.lean') if root else None
def closure(roots, include_p72):
    work = list(roots); project = {}; frontier = {}; p72frontier = {}; external = {}; unresolved = []; order = []
    active = set(); done = set()
    def visit(name):
        if name in done: return
        if name in active: raise RuntimeError('declared import cycle: '+name)
        active.add(name)
        p = source(name)
        if include_p72 and name in p72rows:
            rec = p72rows[name]
            if p is None or not p.is_file() or sha(p) != p72snapshot[name]:
                unresolved.append({'module':name,'reason':'P72 workspace source missing or differs from recorded source'})
            else:
                p72frontier[name] = {'source':str(p.relative_to(ROOT)), 'source_sha256':sha(p), 'object_sha256':rec['object_sha256']}
        elif name in base:
            rec = base[name]
            if p is None or not p.is_file():
                unresolved.append({'module':name,'reason':'base workspace source missing'})
            elif sha(p) != rec['source_sha256']:
                unresolved.append({'module':name,'reason':'base workspace source differs from recorded source'})
            else:
                frontier[name] = {'source':str(p.relative_to(ROOT)), 'source_sha256':sha(p), 'object_sha256':rec['object_sha256']}
        elif p is not None and p.is_file():
            imports = []
            for line in p.read_text().splitlines():
                m = line_import.match(line)
                if m: imports.extend(m.group(1).split())
            project[name] = {'source':str(p.relative_to(ROOT)), 'source_sha256':sha(p), 'imports':imports}
            for dep in imports: visit(dep)
            order.append(name)
        else:
            candidates = [r/Path(name.replace('.', '/')+'.olean') for r in (PKG, TOOL)]
            found = [q for q in candidates if q.is_file()]
            if found:
                q = found[0]
                external[name] = {'path':str(q), 'realpath':str(q.resolve()), 'sha256':sha(q),
                                  'qualification':'observed object, full package ancestry not authenticated'}
            else:
                unresolved.append({'module':name,'reason':'neither mapped workspace source nor observed package object'})
        active.remove(name); done.add(name)
    for n in work: visit(n)
    return {'roots':list(roots),'project':project,'base_frontier':frontier,'p72_frontier':p72frontier,'external':external,
            'unresolved':unresolved,'topological_order':order}

graph_base_only = closure(['DiophantineConsistency.Compact44.P73Graph'], False)
endpoint_base_only = closure(['DiophantineConsistency.Compact44.P73Graph','DiophantineConsistency.Compact44.IPRAPositive73'], False)
graph = closure(['DiophantineConsistency.Compact44.P73Graph'], True)
endpoint = closure(['DiophantineConsistency.Compact44.P73Graph','DiophantineConsistency.Compact44.IPRAPositive73'], True)
direct_sketch = closure(['DiophantineConsistency.Compact44.P73Graph',
                         'DiophantineConsistency.Compact44.P73Halt',
                         'DiophantineConsistency.Compact44.P73Converse',
                         'DiophantineConsistency.Compact44.IPRAOrdinary12Chain'], True)

# Recheck the P72 frontier's archived stage records and recursively captured
# project routes. Parent status is PASS; this does not recompile any object.
p72todo = list(endpoint['p72_frontier']); p72checked = set(); p72edges = 0; p72guards = 0
base_roots = set(endpoint['base_frontier'])
while p72todo:
    name = p72todo.pop()
    if name in p72checked: continue
    p72checked.add(name)
    rec = p72rows[name]; index = p72index[name]
    if rec.get('status') != 'PASS' or len(rec.get('runs', [])) != 2:
        issues.append({'module':name,'reason':'P72 stage not a two-run PASS'})
    captured_imports = set(p72survey['project_sources'][name]['imports']) - {'Init'}
    if set(rec['dependencies']) - {'Init'} != captured_imports:
        issues.append({'module':name,'reason':'P72 recorded dependency names differ from source survey'})
    src = source(name); snap = P72/'src'/Path(name.replace('.', '/')+'.lean')
    archived_src = 'src/'+name.replace('.', '/')+'.lean'
    if (src is None or not src.is_file() or sha(src) != p72snapshot[name] or
        not snap.is_file() or sha(snap) != p72snapshot[name] or
        archive_sha.get(archived_src) != p72snapshot[name]):
        issues.append({'module':name,'reason':'P72 workspace/snapshot/archive source mismatch'})
    obj = P72/'lib'/Path(name.replace('.', '/')+'.olean')
    if not obj.is_file() or sha(obj) != rec['object_sha256']:
        issues.append({'module':name,'reason':'P72 object missing or hash drift'})
    for typ, run in zip(('deps','compile'), rec.get('runs', [])):
        log = Path(run['log']); archived_log = f'logs/{index:04d}-{typ}.txt'
        if (run['exit'] != 0 or run.get('stop_reason') is not None or run.get('monitor_errors') or
            run.get('observed_descendant_pids') or not log.is_file() or
            sha(log) != run['log_sha256'] or archive_sha.get(archived_log) != run['log_sha256']):
            issues.append({'module':name,'reason':'P72 '+typ+' run/log mismatch'})
    for dep, entry in rec['dependencies'].items():
        p72edges += 1; path = Path(entry['path'])
        if (not path.is_file() or str(path.resolve()) != entry['realpath'] or sha(path) != entry['sha256']):
            issues.append({'module':name,'dependency':dep,'reason':'P72 captured input route mismatch'})
        if dep in p72rows:
            if p72rows[dep]['object_sha256'] != entry['sha256']:
                issues.append({'module':name,'dependency':dep,'reason':'P72 producer hash mismatch'})
            else: p72todo.append(dep)
        elif dep in base:
            if base[dep]['object_sha256'] != entry['sha256']:
                issues.append({'module':name,'dependency':dep,'reason':'P72/base producer hash mismatch'})
            else: base_roots.add(dep)
    for raw, expected in rec['direct_guard'].items():
        p72guards += 1; path = Path(raw)
        if expected is None:
            if os.path.lexists(path): issues.append({'module':name,'path':raw,'reason':'unexpected P72 direct companion'})
        elif not path.is_file() or str(path.resolve()) != expected['realpath'] or sha(path) != expected['sha256']:
            issues.append({'module':name,'path':raw,'reason':'P72 direct companion drift'})

# Compare one observed collision across independently audited FAILED parents;
# this is not an authentication or promotion of those parent runs.
collision_name = 'DiophantineConsistency.ModelDifferenceRing'
assert collision_name in p72checked
collision_source = p72snapshot[collision_name]
collision = {'source_sha256':collision_source, 'p72_object_sha256':p72rows[collision_name]['object_sha256'],
             'failed_parent_children':{}}
for label in ('03','04'):
    failed = json.loads(PINS['failed'+label+'_state'][0].read_text())
    audit = json.loads(PINS['failed'+label+'_result'][0].read_text())
    assert failed['status'] == 'FAILED' and audit['status'] == 'PASS_INDEPENDENT_FAILURE_AUDIT'
    rows = [r for r in failed['rows'] if r.get('module') == collision_name]
    assert len(rows) == 1
    row = rows[0]
    assert row['source_sha256'] == collision_source
    for typ in ('deps','compile'):
        run = row[typ]; log = Path(run['log'])
        assert run['exit'] == 0 and run.get('stop_reason') is None
        assert log.is_file() and sha(log) == run['log_sha256']
    obj = Path(row['compile']['log']).parents[1]/'lib'/Path(collision_name.replace('.', '/')+'.olean')
    assert obj.is_file() and sha(obj) == row['object_sha256']
    collision['failed_parent_children'][label] = {'parent_status':'FAILED',
        'object':str(obj), 'object_sha256':row['object_sha256'], 'compile_exit':row['compile']['exit']}
assert len({collision['p72_object_sha256']} | {v['object_sha256'] for v in collision['failed_parent_children'].values()}) == 3

# Recheck the retained base's recorded project edges recursively from the
# endpoint/P72 frontier, inputs and output companions. This is still a
# point-in-time replay of recorded routes, not a fresh or dynamic trace.
todo = list(base_roots); checked = set(); edge_count = 0; guard_count = 0
package_pins = collections.defaultdict(set)
for rec in state['records']:
    for name, item in rec['direct_inputs'].items():
        if item['kind'] == 'package': package_pins[name].add(item['sha256'])
while todo:
    name = todo.pop()
    if name in checked: continue
    checked.add(name)
    rec = base[name]
    if rec['exit'] != 0: issues.append({'module':name,'reason':'nonzero base stage'})
    obj = BASE/'lib'/Path(name.replace('.', '/')+'.olean')
    if not obj.is_file() or sha(obj) != rec['object_sha256']:
        issues.append({'module':name,'reason':'base object missing or hash drift'})
    source_row = manifest['sources'][name]
    src = ROOT/source_row['workspace_path']
    if not src.is_file() or sha(src) != rec['source_sha256'] or rec['source_sha256'] != source_row['sha256']:
        issues.append({'module':name,'reason':'base source missing or hash drift'})
    log = Path(rec['log'])
    if not log.is_file() or sha(log) != rec['log_sha256']:
        issues.append({'module':name,'reason':'base stage log missing or hash drift'})
    for dep, entry in rec['direct_inputs'].items():
        edge_count += 1
        path = Path(entry['path'])
        if not path.is_file() or sha(path) != entry['sha256']:
            issues.append({'module':name,'dependency':dep,'reason':'recorded direct input missing or drift'})
        if entry['kind'] == 'project':
            if dep not in base or base[dep]['object_sha256'] != entry['sha256']:
                issues.append({'module':name,'dependency':dep,'reason':'project edge has no matching base producer'})
            else: todo.append(dep)
    for raw, expected in state['outputs'][name].items():
        guard_count += 1; path = Path(raw)
        if expected is None:
            if os.path.lexists(path): issues.append({'module':name,'path':raw,'reason':'unexpected companion'})
        elif not path.is_file() or str(path.resolve()) != expected['realpath'] or sha(path) != expected['sha256']:
            issues.append({'module':name,'path':raw,'reason':'base output/companion drift'})
for path, expected in state['guarded_companions'].items():
    guard_count += 1; p = Path(path)
    if expected is None:
        if os.path.lexists(p): issues.append({'path':path,'reason':'unexpected guarded companion'})
    elif not p.is_file() or str(p.resolve()) != expected['realpath'] or sha(p) != expected['sha256']:
        issues.append({'path':path,'reason':'guarded companion drift'})

def route_counts(frontier):
    pqueue = list(frontier); pseen = set(); bqueue = []; bseen = set()
    while pqueue:
        n = pqueue.pop()
        if n in pseen: continue
        pseen.add(n)
        for dep in p72rows[n]['dependencies']:
            if dep in p72rows: pqueue.append(dep)
            elif dep in base: bqueue.append(dep)
    while bqueue:
        n = bqueue.pop()
        if n in bseen: continue
        bseen.add(n)
        for dep, entry in base[n]['direct_inputs'].items():
            if entry['kind'] == 'project' and dep in base: bqueue.append(dep)
    return {'p72_objects':len(pseen), 'base_objects':len(bseen)}
for group in (graph, endpoint):
    for name, entry in group['external'].items():
        entry['base_direct_hash_match'] = entry['sha256'] in package_pins.get(name, set())

# Compare relevant workspace sources to HEAD blobs. A single source match is
# not a build or provider authentication, and HEAD can move during survey.
def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30).stdout
head_before = git('rev-parse','HEAD').decode().strip()
paths = sorted({x['source'] for x in endpoint['project'].values()} |
               {x['source'] for x in endpoint['base_frontier'].values()} |
               {x['source'] for x in endpoint['p72_frontier'].values()} |
               {str(source(n).relative_to(ROOT)) for n in p72checked if source(n) is not None and source(n).is_file()} |
               {manifest['sources'][n]['workspace_path'] for n in checked})
entries = git('ls-tree','-r','-z',head_before,'--',*paths).split(b'\0')
head_blobs = {}
for entry in entries:
    if not entry: continue
    header, path = entry.split(b'\t',1); mode, kind, digest = header.split(b' ')
    if kind == b'blob': head_blobs[path.decode()] = digest.decode()
source_head_issues = []
for rel in paths:
    raw = (ROOT/rel).read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    if head_blobs.get(rel) != blob: source_head_issues.append(rel)
head_after = git('rev-parse','HEAD').decode().strip()

def summary(c):
    return {'project_source_count':len(c['project']), 'base_frontier_count':len(c['base_frontier']),
            'p72_frontier_count':len(c['p72_frontier']),
            'external_object_count':len(c['external']), 'unresolved_count':len(c['unresolved'])}
print(json.dumps({
    'status':'READ_ONLY_OBSERVATION_NOT_BUILD_READINESS',
    'inspector_sha256':sha(HERE/'inspect.py'),
    'pins':{k:v[1] for k,v in PINS.items()},
    'head_before':head_before,'head_after':head_after,'head_changed':head_before!=head_after,
    'source_head_checked_count':len(paths),'source_head_issues':source_head_issues,'graph':graph,'graph_summary':summary(graph),
    'endpoint':endpoint,'endpoint_summary':summary(endpoint),
    'direct_model_sketch':direct_sketch,'direct_model_sketch_summary':summary(direct_sketch),
    'base_only_graph_summary':summary(graph_base_only),
    'base_only_endpoint_summary':summary(endpoint_base_only),
    'recorded_p72_trace':{'unique_project_objects':len(p72checked), 'direct_edges_checked':p72edges,
                          'direct_companion_guards_checked':p72guards},
    'graph_recorded_route_counts':route_counts(graph['p72_frontier']),
    'failed_parent_object_collision':collision,
    'recorded_base_trace':{'unique_project_objects':len(checked), 'direct_edges_checked':edge_count,
                           'companion_guards_checked':guard_count},
    'recorded_route_issues':issues,
    'tmp_free_bytes':shutil.disk_usage('/tmp').free,'disk_stop_bytes':5100000000,
    'scope':'Line-parsed declared source imports plus recorded base routes at this observation; package-transitive/dynamic ancestry, between-sample changes, build compatibility, and full source/JSON/PDF semantics remain open. No Lean run.'
}, indent=2, sort_keys=True))
