"""Independent read-only audit of the frozen hierarchy plan; no Lean invocation."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tomllib

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
PLAN = D / 'research/arithmetic-current-hierarchy2011-cache-plan.json'
MF = D / 'research/arithmetic-current-hierarchy2011-plan-FILES.json'
OUT = D / 'reviews/arithmetic-current-hierarchy2011-plan-peer-audit.json'
EXPECTED_PLAN = 'b5170702be3f9d00916436b1fe26af3edc1db2defe02303d6c0bf1e671ac1c3f'
EXPECTED_MF = '09406e1e120e1f986cef50d44cfe0304c2e4583d2dd36cfcbac1ff2ea7b34fcc'
observations = []
live_drift = {}


def require(p, reason):
    if not p:
        raise RuntimeError(reason)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def file_record(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': digest(b), 'bytes': len(b)}


def verify(pin, drift_allowed=False):
    actual = file_record(pin['path'])
    observations.append(actual)
    matches = actual['sha256'] == pin['sha256']
    matches = matches and ('bytes' not in pin or pin['bytes'] == actual['bytes'])
    if not matches:
        require(drift_allowed, 'unexpected changed pin: ' + actual['path'])
        live_drift[actual['path']] = {'expected': pin, 'actual': actual}
    return actual


def load(pin):
    verify(pin)
    return json.loads(Path(pin['path']).read_text())


def git_bytes(commit, relative):
    return subprocess.check_output(['git', 'show', commit + ':' + str(relative)], cwd=R)


def header(raw):
    # Independent nested-comment removal, then parse only module header commands.
    s = raw.decode()
    out = []
    i = depth = 0
    while i < len(s):
        if s[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and s[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            out.append('\n' if s[i] == '\n' else ' ')
            i += 1
        elif s[i:i+2] == '--':
            end = s.find('\n', i)
            i = len(s) if end < 0 else end
        else:
            out.append(s[i])
            i += 1
    require(depth == 0, 'unclosed block comment')
    prelude = False
    imports = []
    for line in ''.join(out).splitlines():
        line = line.strip()
        if not line or line == 'module':
            continue
        if line == 'prelude':
            prelude = True
            continue
        m = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if m:
            names = m.group(1).split()
            require(all(re.fullmatch(r'[A-Za-z0-9_\u0080-\uffff.]+', n) for n in names), 'import token')
            imports.extend(names)
            continue
        break
    return list(dict.fromkeys(([] if prelude else ['Init']) + imports))


require(not OUT.exists(), 'preserve existing independent output')
head_before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
plan = load({'path': str(PLAN), 'sha256': EXPECTED_PLAN})
manifest = load({'path': str(MF), 'sha256': EXPECTED_MF})
for pin in manifest['files']:
    verify(pin)
require(len(manifest['files']) == 17, 'manifest size')
parent = load(plan['parent'])
peer = load(plan['historical_peer'])
require(peer['status'] == 'PASS', 'historical peer status')
for key in ['parent_manifest', 'historical_peer_manifest']:
    mf = load(plan[key])
    for row in mf['files']:
        p = Path(row['path'])
        if not p.is_absolute():
            p = Path(plan[key]['path']).parent / p
        verify(dict(row, path=str(p)))

frozen = plan['snapshot_head']
require(frozen == plan['final_head'], 'snapshot changed during author audit')
mods = {m['module']: m for m in plan['modules']}
old = {m['module']: m for m in parent['modules']}
ext = {m['module']: m for m in plan['external']}
old_ext = {m['module']: m for m in parent['external']}
require(len(mods) == len(plan['modules']) == 430, 'module uniqueness/count')
roots = {x['name']: R / x.get('srcDir', '.') for x in tomllib.loads(git_bytes(frozen, 'lakefile.toml').decode())['lean_lib']}
roots['Foundation'] = Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
edges = {}
for name, m in mods.items():
    p = roots[name.split('.')[0]] / Path(*name.split('.')).with_suffix('.lean')
    require(str(p) == m['source']['path'], 'independent source resolution: ' + name)
    raw = git_bytes(frozen, p.relative_to(R)) if p.is_relative_to(R) else p.read_bytes()
    require(digest(raw) == m['source']['sha256'], 'frozen source: ' + name)
    require(len(raw) == m['source']['bytes'], 'frozen source size: ' + name)
    verify(m['source'], drift_allowed=True)
    edges[name] = header(raw)
    require(edges[name] == m['imports'], 'independent import header: ' + name)

ordered, active, seen, boundaries = [], set(), set(), set()
def visit(name):
    if name in seen:
        return
    if name not in mods:
        require(name in ext, 'missing module/boundary: ' + name)
        boundaries.add(name)
        return
    require(name not in active, 'cycle: ' + name)
    active.add(name)
    for child in edges[name]:
        visit(child)
    active.remove(name)
    seen.add(name)
    ordered.append(name)
for n in plan['direct_imports']:
    visit(n)
require(ordered == plan['topological_order'] and seen == set(mods), 'exact DAG/order')
require(boundaries == set(ext) and len(ext) == 57, 'exact boundary')

changed, new, affected, reused = [], [], [], []
for n in ordered:
    m, historic = mods[n], old.get(n)
    if historic is None:
        new.append(n)
    elif historic['source_sha256'] != m['source']['sha256'] or historic['imports'] != edges[n]:
        changed.append(n)
    causes = [d for d in edges[n] if d in affected]
    if n in changed or n in new or causes:
        affected.append(n)
        require(m['objects'] == [] and m['affected_dependencies'] == causes, 'refresh closure: ' + n)
        require(m['mode'] == 'FRESH_CURRENT_SOURCE_REQUIRED', 'refresh mode')
        if historic is not None:
            require(m['historical_excluded_record'] == historic, 'excluded source provenance')
    else:
        reused.append(n)
        require(m['historical_record'] == historic, 'cache source provenance: ' + n)
        require(m['objects'] == historic['objects'], 'cache artifact provenance: ' + n)
        require(m['mode'] == 'REUSE_UNCHANGED_SOURCE_AND_ALL_DEPENDENCIES', 'reuse mode')
        for pin in m['objects']:
            verify(pin)
for key, values in [('changed_modules', changed), ('new_modules', new), ('fresh_prerequisites', affected), ('reused_modules', reused)]:
    require(plan[key] == values, 'partition ' + key)
require((len(changed), len(new), len(affected), len(reused)) == (14, 1, 92, 338), 'partition counts')
require(new == ['PAHF.PACore'], 'only new prerequisite')
require(sum(n.startswith('Foundation.') for n in mods) == 139, 'Foundation count')
require(not any(n.startswith('Foundation.') for n in affected), 'no Foundation refresh')
for n, row in ext.items():
    require(row == old_ext[n], 'unchanged inherited boundary: ' + n)
    verify(row['source'])
    for pin in row['objects']:
        verify(pin)

expected_rel = {}
for name in reused + sorted(ext):
    row = mods[name] if name in mods else ext[name]
    search = plan['audited_existing_search'] if name in mods else plan['boundary_search']
    for pin in row['objects']:
        rel = str(Path(*name.split('.')[:-1]) / Path(pin['path']).name)
        require(rel not in expected_rel, 'unique artifact relative path')
        first = next((Path(root) / rel for root in search if (Path(root) / rel).is_file()), None)
        require(first is not None, 'first provider missing')
        actual = verify(dict(pin, path=str(first)))
        expected_rel[rel] = (name, pin, actual)
for row in plan['first_providers']:
    name, expected, actual = expected_rel.pop(row['relative'])
    require((name, expected, actual) == (row['module'], row['expected'], row['actual']), 'provider mapping')
require(not expected_rel and len(plan['first_providers']) == 983, 'all provider mappings')
for pin in plan['pins']:
    verify(pin, drift_allowed=pin['path'] in {m['source']['path'] for m in mods.values()})
verify(plan['compiler'])
verify(plan['candidate_not_selected'])
candidate = json.loads(Path(plan['candidate_not_selected']['path']).read_text())
require(not {r['module'] for r in candidate if r['status'] == 0}.intersection(affected), 'excluded shortcut')
require(shutil.disk_usage('/tmp').free >= 512 * 1024**2, 'disk reserve')
head_after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
result = dict(status='FROZEN_SNAPSHOT_PASS_CURRENT_SOURCE_REVALIDATION_REQUIRED' if live_drift else 'FROZEN_AND_CURRENT_PASS',
    plan=file_record(PLAN), manifest=file_record(MF), driver=file_record(__file__), frozen_snapshot=frozen,
    head_before=head_before, head_after=head_after, comparisons=len(observations), unique_paths=len({p['path'] for p in observations}),
    counts=plan['counts'], all_fresh_prerequisites=affected, live_source_drift=list(live_drift.values()),
    disk_free_bytes=shutil.disk_usage('/tmp').free, scope='Independent source/header/provider plan audit only; no overlay/compiler or prerequisite proof replay.',
    observations=observations)
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['observations', 'all_fresh_prerequisites']}, indent=2))
