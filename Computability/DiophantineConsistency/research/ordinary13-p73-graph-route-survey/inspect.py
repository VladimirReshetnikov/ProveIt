#!/usr/bin/env python3
"""Point-in-time graph-only provider/collision survey; no Lean or build tree."""
import collections
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
ROOT = HERE.parents[3]
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105')
BASE = Path('/tmp/current14-standard-fresh-build-20261104')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
ROOTS = [('p72', P72/'lib'), ('package', PKG), ('toolchain', TOOL)]
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean',
            '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash',
            '.so','.dll','.dylib')
pins = {
    'prior_inspector': (PROJECT/'research/ordinary13-p73-provider-preflight/inspect.py', '67ab841e465f8923c8f3c65e07d93fa055dbfea8e6f1f745ad79442786c097b7'),
    'prior_observation': (PROJECT/'research/ordinary13-p73-provider-preflight/observation.json', 'f37f6add7288d06a4e1ba60b97bc0ea5c00eeac13c5372bdceea4174c88bdae5'),
    'prior_auditor': (PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/check.py', 'e7cc82dccb993320b72af7a5665013c8e96ff45ef649d5b5ee74150295fbcf5a'),
    'prior_audit_result': (PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/result.json', 'fc29d005ab3597cad866219fb8bdfe8f4495743ad3215cd02732c8933140480c'),
    'graph_client': (PROJECT/'research/ordinary13-p73-share91-lean-draft/P73Shared91.lean', '6fca39ca8af4743a9be256594cd87b2628d6b8c8e87107b08d604556e43bf364'),
    'p72_source_survey': (PROJECT/'research/p72-current-base-source-survey/result.json', '29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954'),
    'p72_stage_archive': (PROJECT/'research/p72-current-base-extension-build-attempt02/terminal/stage-evidence.tar.gz', '884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541'),
    'base_state': (BASE/'state.json', 'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'),
}
cache = {}
def sha(path):
    path = Path(path)
    if path not in cache:
        with path.open('rb') as f: cache[path] = hashlib.file_digest(f, 'sha256').hexdigest()
    return cache[path]
for label, (path, expected) in pins.items():
    if not path.is_file() or sha(path) != expected: raise RuntimeError('pin drift: '+label)
audit = json.loads(pins['prior_audit_result'][0].read_text())
assert audit['status'] == 'PASS_READ_ONLY_INDEPENDENT_REVIEW'

# Revalidate the complete prior retained-route survey. This subprocess performs
# no Lean calls and has its own bounded Git queries; no new tree is created.
run = subprocess.run([sys.executable, '-I', '-S', '-B', str(pins['prior_inspector'][0])],
                     cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
if run.returncode != 0 or run.stderr: raise RuntimeError('prior read-only inspector failed: '+run.stderr.decode(errors='replace')[-2000:])
survey = json.loads(run.stdout)
frozen = json.loads(pins['prior_observation'][0].read_text())
assert survey['status'] == 'READ_ONLY_OBSERVATION_NOT_BUILD_READINESS'
assert not survey['recorded_route_issues'] and not survey['source_head_issues'] and not survey['head_changed']
assert survey['graph'] == frozen['graph'] and survey['graph_summary'] == frozen['graph_summary']
assert survey['graph_recorded_route_counts'] == {'p72_objects':13,'base_objects':17}

order = json.loads(pins['p72_source_survey'][0].read_text())['extension_order']
p72index = {n:i for i,n in enumerate(order)}
base_state = json.loads(pins['base_state'][0].read_text())
base = {r['module']:r for r in base_state['records']}
archive_rows = {}
with tarfile.open(pins['p72_stage_archive'][0], 'r:gz') as archive:
    for member in archive:
        if member.isfile() and member.name.startswith('rows/'):
            archive_rows[member.name] = hashlib.sha256(archive.extractfile(member).read()).hexdigest()
def row(name):
    key = f'rows/{p72index[name]:04d}.json'; path = P72/key
    if not path.is_file() or sha(path) != archive_rows.get(key):
        raise RuntimeError('P72 row differs from frozen stage archive: '+name)
    return json.loads(path.read_text())

# Reconstruct the graph frontier's captured project ancestry and record every
# direct input used by those stages. Paths are historical producer routes;
# merely observing alternatives below does not authenticate their ancestry.
pq = list(survey['graph']['p72_frontier']); bq = []; ps = set(); bs = set(); issues = []
expected = collections.defaultdict(set); edge_records = []
def add_expected(owner, name, path, real, digest):
    p = Path(path)
    if not p.is_file() or str(p.resolve()) != real or sha(p) != digest:
        issues.append({'owner':owner,'module':name,'reason':'recorded input/producer route drift'})
    expected[name].add((real, digest))
    edge_records.append({'owner':owner,'dependency':name,'path':path,'realpath':real,'sha256':digest})
def check_guard(owner, guard):
    for raw, expected_guard in guard.items():
        p = Path(raw)
        if expected_guard is None:
            if os.path.lexists(p): issues.append({'owner':owner,'path':raw,'reason':'unexpected recorded companion'})
        elif (not p.is_file() or str(p.resolve()) != expected_guard['realpath'] or
              sha(p) != expected_guard['sha256']):
            issues.append({'owner':owner,'path':raw,'reason':'recorded companion drift'})
while pq:
    name = pq.pop()
    if name in ps: continue
    ps.add(name); rec = row(name)
    obj = P72/'lib'/Path(name.replace('.', '/')+'.olean')
    add_expected('P72 producer', name, str(obj), str(obj.resolve()), rec['object_sha256'])
    check_guard(name, rec['direct_guard'])
    for dep, item in rec['dependencies'].items():
        add_expected(name,dep,item['path'],item['realpath'],item['sha256'])
        if dep in p72index: pq.append(dep)
        elif dep in base: bq.append(dep)
while bq:
    name = bq.pop()
    if name in bs: continue
    bs.add(name); rec = base[name]
    obj = BASE/'lib'/Path(name.replace('.', '/')+'.olean')
    add_expected('base producer',name,str(obj),str(obj.resolve()),rec['object_sha256'])
    check_guard(name, base_state['outputs'][name])
    for dep, item in rec['direct_inputs'].items():
        p = Path(item['path'])
        add_expected(name,dep,item['path'],str(p.resolve()),item['sha256'])
        if item['kind'] == 'project':
            if dep not in base: raise RuntimeError('unmapped captured base producer: '+dep)
            bq.append(dep)
assert len(ps)==13 and len(bs)==17

for name, item in survey['graph']['external'].items():
    add_expected('declared graph source',name,item['path'],item['realpath'],item['sha256'])
for name, item in survey['graph']['p72_frontier'].items():
    p = P72/'lib'/Path(name.replace('.', '/')+'.olean')
    add_expected('declared graph source',name,str(p),str(p.resolve()),item['object_sha256'])

# Also check name/suffix intersections for the entire retained P72 overlay,
# not merely the recorded graph ancestry. This is a filesystem observation,
# not evidence that every overlay object is loaded or transitively audited.
overlay_files = sorted((P72/'lib').rglob('*.olean'))
overlay_names = {str(p.relative_to(P72/'lib'))[:-6].replace('/', '.') for p in overlay_files}
expected_overlay = set(p72index) | set(base)
overlay_inventory_issues = []
invalid_overlay = [str(p) for p in overlay_files if not p.is_file()]
if invalid_overlay:
    overlay_inventory_issues.append({'invalid_or_broken_olean_paths':invalid_overlay})
if overlay_names != expected_overlay:
    overlay_inventory_issues.append({'missing':sorted(expected_overlay-overlay_names),
                                     'unexpected':sorted(overlay_names-expected_overlay)})
overlay_cross_root = []
for name in sorted(overlay_names):
    stem = Path(name.replace('.', '/'))
    for suffix in SUFFIXES:
        local = P72/'lib'/Path(str(stem)+suffix)
        if not os.path.lexists(local): continue
        for label, root in ROOTS[1:]:
            other = root/Path(str(stem)+suffix)
            if os.path.lexists(other):
                overlay_cross_root.append({'module':name,'suffix':suffix,
                                           'p72':str(local),'other_root':label,'other':str(other)})

targets = ['DiophantineConsistency.Compact44.FreeJ13',
           'DiophantineConsistency.Compact44.P73Graph', 'P73Shared91']
excluded_target_roots = [('base',BASE/'lib'), ('project_build',ROOT/'.lake/build/lib/lean')]
excluded_targets = []
provider_source_targets = []
for name in targets:
    stem = Path(name.replace('.', '/'))
    source_path = P72/'src'/Path(str(stem)+'.lean')
    if os.path.lexists(source_path): provider_source_targets.append({'module':name,'path':str(source_path)})
    for suffix in SUFFIXES:
        for label, root in excluded_target_roots:
            p = root/Path(str(stem)+suffix)
            if os.path.lexists(p): excluded_targets.append({'module':name,'suffix':suffix,'root':label,'path':str(p)})
names = sorted(set(expected) | set(targets) | {'Init'})
inventory = {}; shadows = []
for name in names:
    stem = Path(name.replace('.', '/')); files = {}
    for suffix in SUFFIXES:
        candidates = []
        for label, root in ROOTS:
            p = root/Path(str(stem)+suffix)
            if not os.path.lexists(p): continue
            if not p.is_file():
                issues.append({'module':name,'suffix':suffix,'root':label,'reason':'broken or non-file candidate'})
                candidates.append({'root':label,'path':str(p),'invalid':True}); continue
            candidates.append({'root':label,'path':str(p),'realpath':str(p.resolve()),'sha256':sha(p)})
        if candidates:
            files[suffix] = candidates
            valid = [x for x in candidates if 'sha256' in x]
            if len({x['sha256'] for x in valid}) > 1:
                shadows.append({'module':name,'suffix':suffix,'candidates':valid})
    present = files.get('.olean', [])
    routes = sorted(expected.get(name, set()))
    if name in targets and present:
        issues.append({'module':name,'reason':'future output name exists in an observed lower root'})
    if routes:
        if len(routes) != 1:
            issues.append({'module':name,'reason':'captured routes disagree','routes':routes})
        elif not present or 'sha256' not in present[0] or (present[0]['realpath'],present[0]['sha256']) != routes[0]:
            issues.append({'module':name,'reason':'first observed object candidate differs from captured route','routes':routes})
    inventory[name] = {'historical_routes':[{'realpath':a,'sha256':b} for a,b in routes], 'observed':files}

print(json.dumps({
    'status':'READ_ONLY_OBSERVATION_NOT_BUILD_READINESS',
    'inspector_sha256':sha(HERE/'inspect.py'), 'prior_inspector_sha256':pins['prior_inspector'][1],
    'head':survey['head_before'], 'head_changed_during_prior_survey':survey['head_changed'],
    'proposed_lower_root_order':[{'label':n,'path':str(p)} for n,p in ROOTS],
    'future_output_root':'hypothetical; not created or surveyed',
    'future_output_modules':targets, 'declared_project_sources':survey['graph']['project'],
    'p72_project_producers':sorted(ps), 'base_project_producers':sorted(bs),
    'overlay_inventory':{'observed_olean_names':len(overlay_names),'expected_names':len(expected_overlay),
                         'inventory_issues':overlay_inventory_issues,
                         'cross_root_companion_intersections':overlay_cross_root},
    'excluded_target_roots':[{'label':n,'path':str(p)} for n,p in excluded_target_roots],
    'excluded_target_artifacts':excluded_targets,
    'provider_snapshot_target_sources':provider_source_targets,
    'captured_edges':edge_records, 'module_inventory':inventory,
    'different_hash_candidates':shadows, 'route_issues':issues,
    'counts':{'p72_producers':len(ps),'base_producers':len(bs),'recorded_edges_and_producers':len(edge_records),
              'p72_direct_guard_slots':sum(len(row(n)['direct_guard']) for n in ps),
              'base_output_guard_slots':sum(len(base_state['outputs'][n]) for n in bs),
              'observed_module_names':len(names),'different_hash_candidates':len(shadows),'route_issues':len(issues)},
    'tmp_free_bytes':shutil.disk_usage('/tmp').free,'disk_stop_bytes':5100000000,
    'scope':'Only line-declared graph sources and retained recorded direct ancestry across the three named existing roots; no build tree, Lean deps, Lean execution, future-root observation, complete package/dynamic ancestry or compatibility proof.'
},indent=2,sort_keys=True))
