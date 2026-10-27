"""Read-only current-source cache inventory. No Lean invocation or provider mutation."""
from pathlib import Path
from collections import Counter
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REV = HERE.parent
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'


HASH_CACHE = {}

def sha(path):
    path = Path(path)
    stat = path.stat()
    key = (str(path), stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
    if key not in HASH_CACHE:
        HASH_CACHE[key] = hashlib.sha256(path.read_bytes()).hexdigest()
    return HASH_CACHE[key]

def listed(value):
    if isinstance(value, dict):
        return list(value.values())
    return value if isinstance(value, list) else []


def read(path):
    return json.loads(Path(path).read_text())


def pin(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}


closure = read(HERE / 'closure.json')
modules = {r['module']: r for r in closure['modules']}
candidates = {m: [] for m in modules}
rejected = []
metadata = {}


def add(module, source_sha, objects, provenance, category, extra=None):
    if module not in modules:
        return
    reason = None
    if source_sha != modules[module]['source_sha256']:
        reason = 'current_source_mismatch'
    elif not objects:
        reason = 'no_object_record'
    else:
        for obj in objects:
            p = Path(obj['path'])
            if not p.is_file():
                reason = 'object_missing'
                break
            if sha(p) != obj['sha256']:
                reason = 'object_hash_mismatch'
                break
    if reason:
        rejected.append({'module': module, 'reason': reason,
                         'provenance': provenance, 'objects': objects})
        return
    row = {'module': module, 'source_sha256': source_sha, 'objects': objects,
           'provenance': provenance, 'category': category}
    if extra:
        row.update(extra)
    candidates[module].append(row)


# Selected accepted current source/object inventories, with fresh outputs where present.
accepted = [
    REV / 'foundation-ha-current-transfer-dependency-replay.json',
    REV / 'foundation-pahf-nat-semantics-dependency-replay.json',
    REV / 'arithmetic-machine215-replay/dependencies-current.json',
    REV / 'validator-seed-closure222-replay.json',
]
for path in accepted:
    doc = read(path)
    metadata[str(path)] = pin(path)
    body = doc.get('inputs', doc)
    compiler = body.get('compiler')
    csha = compiler.get('sha256') if isinstance(compiler, dict) else body.get('compiler_sha256')
    if csha != COMPILER_SHA:
        raise RuntimeError(f'Unexpected compiler in {path}: {csha}')
    for row in body.get('modules', []):
        objects = row.get('objects', [])
        if not objects and isinstance(row.get('object'), str) and row.get('object_sha256'):
            objects = [{'path': row['object'], 'sha256': row['object_sha256']}]
        add(row['module'], row['source_sha256'], objects,
            pin(path), 'accepted_current_inventory', {'prior_record': row})
    for row in doc.get('fresh_modules', []):
        if row.get('exit_code') == 0:
            add(row['module'], row['source_sha256'],
                [{'path': row['object'], 'sha256': row['object_sha256']}],
                pin(path), 'accepted_current_fresh', {'prior_record': row})

plan_path = REV / 'current-equation-narrow-native-root-replay/plan.json'
state_path = REV / 'current-equation-narrow-native-root-replay/state.json'
plan, state = read(plan_path), read(state_path)
metadata[str(plan_path)], metadata[str(state_path)] = pin(plan_path), pin(state_path)
if state['status'] != 'PASS' or state['plan_sha256'] != sha(plan_path):
    raise RuntimeError('Native accepted replay no longer matches its plan')
fresh = {r['module']: r for r in state['completed']}
for row in plan['modules']:
    r = fresh.get(row['module'], row)
    obj = r['object']
    if isinstance(obj, str):
        obj = {'path': obj, 'sha256': r['object_sha256']}
    add(row['module'], r['source']['sha256'], [obj], pin(state_path),
        'accepted_native_fresh' if row['module'] in fresh else 'accepted_native_reuse',
        {'prior_record': r})

# New read-only Foundation authentication: these manifests retain exact provenance limits.
for name, category in [('extra-foundation-trace-auth.json', 'new_source_four_artifact_lake_trace'),
                       ('private-set-theory-auth.json', 'historical_executed_private_foundation')]:
    path = HERE / name
    doc = read(path)
    metadata[str(path)] = pin(path)
    for row in doc['modules']:
        if 'files' in row:
            src = next(r for r in row['files'] if r['path'].endswith('.lean'))
            objs = [r for r in row['files'] if not r['path'].endswith('.lean')]
            ssha = src['sha256']
        else:
            ssha, objs = row['source_sha256'], row['objects']
        add(row['module'], ssha, objs, pin(path), category, {'prior_record': row})

# Historical candidates: inspect records, never execute their drivers. Only fresh recorded
# successful source commands count as historical executed pairs. Reused pairs are reported
# separately and never silently upgraded to a fresh source build.
old_path = Path('/tmp/zfc-r2-provider-inventory/inventory.json')
old = read(old_path)
metadata[str(old_path)] = pin(old_path)
record_paths = {Path(r['path']) for r in old['actual_records_scanned']}
for parent in Path('/tmp').glob('zfc*'):
    if parent.is_dir():
        record_paths.update(parent.rglob('verification.json'))
record_errors = []
scanned = 0
for path in sorted(record_paths):
    try:
        d = read(path)
    except (OSError, ValueError) as err:
        record_errors.append({'path': str(path), 'error': str(err)})
        continue
    if not isinstance(d, dict) or d.get('status') != 'PASS':
        continue
    compiler = d.get('compiler', {})
    if not isinstance(compiler, dict):
        continue
    compiler = dict(compiler)
    if not compiler.get('sha256') and compiler.get('path'):
        compiler['sha256'] = d.get('before', {}).get(compiler['path'])
    if compiler.get('sha256') != COMPILER_SHA:
        continue
    if '4.32.0' not in compiler.get('version', ''):
        continue
    standard = d.get('only_standard_axioms') is True
    audits = d.get('audits', [])
    if isinstance(audits, list) and audits:
        standard = standard or all(isinstance(a, dict) and a.get('only_standard_axioms') is True for a in audits)
    if not standard:
        continue
    fresh_rows = [r for r in listed(d.get('fresh_modules', [])) if isinstance(r, dict) and r.get('module') in modules]
    # Two older executed schemas record a single module_object or a named modules map.
    # Match the entire module suffix and still require its successful command below.
    older_rows = []
    if isinstance(d.get('module_object'), dict) and isinstance(d.get('source'), dict):
        older_rows.append({**d['module_object'], 'source_sha256': d['source'].get('sha256')})
    if isinstance(d.get('modules'), dict):
        older_rows += [r for r in d['modules'].values() if isinstance(r, dict)]
    for r in older_rows:
        op = r.get('object', r.get('path', ''))
        matches = [m for m in modules if op.endswith('/' + m.replace('.', '/') + '.olean')]
        if len(matches) == 1:
            fresh_rows.append({**r, 'module': matches[0]})
    reused_rows = [r for r in listed(d.get('reused_modules', [])) if isinstance(r, dict) and r.get('module') in modules]
    if not fresh_rows and not reused_rows:
        continue
    scanned += 1
    provenance = pin(path)
    metadata[str(path)] = provenance
    for row in fresh_rows:
        op = row.get('path', row.get('object'))
        oh = row.get('sha256', row.get('object_sha256'))
        sh = row.get('source_sha256')
        if not (op and oh and sh):
            continue
        commands = [c for c in d.get('commands', []) if isinstance(c.get('command'), list)
                    and '-o' in c['command']
                    and c['command'][c['command'].index('-o') + 1] == op]
        if len(commands) != 1 or commands[0].get('exit_code') != 0:
            continue
        c = commands[0]
        if c['command'][0] != compiler['path']:
            continue
        srcs = [s for s in c['command'] if s.endswith('.lean')]
        if len(srcs) != 1 or not Path(srcs[0]).is_file() or sha(srcs[0]) != sh:
            continue
        if 'log' in c:
            if not Path(c['log']).is_file() or sha(c['log']) != c.get('log_sha256'):
                continue
        elif 'output' not in c:
            continue
        add(row['module'], sh, [{'path': op, 'sha256': oh}], provenance,
            'historical_executed_source_pair',
            {'source_command': c, 'compiler': compiler, 'snapshot': pin(srcs[0]),
             'axiom_audit_reported_standard_only': standard,
             'scope': 'Source/object/compiler/captured successful source command checked; no fresh replay or full historical dependency revalidation.'})
    for row in reused_rows:
        if all(k in row for k in ['source_sha256', 'object', 'object_sha256']):
            add(row['module'], row['source_sha256'],
                [{'path': row['object'], 'sha256': row['object_sha256']}], provenance,
                'historical_reuse_only_candidate', {'prior_record': row})

priority = {k: i for i, k in enumerate([
    'accepted_current_fresh', 'accepted_native_fresh', 'accepted_current_inventory',
    'accepted_native_reuse', 'new_source_four_artifact_lake_trace',
    'historical_executed_private_foundation', 'historical_executed_source_pair',
    'historical_reuse_only_candidate'])}
rows, missing, provisional = [], [], []
for m, source in modules.items():
    if sha(source['source']) != source['source_sha256']:
        raise RuntimeError(f'Source drift during audit: {m}')
    cs = sorted(candidates[m], key=lambda x: priority[x['category']])
    selected = cs[0] if cs else None
    status = ('available_source_attested' if selected and
              selected['category'] != 'historical_reuse_only_candidate' else
              'historical_reuse_candidate_only' if selected else 'no_matching_attested_pair_found')
    if status != 'available_source_attested':
        missing.append(m)
    if status == 'historical_reuse_candidate_only':
        provisional.append(m)
    rows.append({**source, 'status': status, 'selected': selected,
                 'candidate_count': len(cs)})
# This order is already dependency-first. Propagate refresh through every importing client,
# distinguishing minimum missing-object builds from source-identical dependent refreshes.
needs = set(missing)
affected = []
for m, source in modules.items():
    if m in needs or any(i in needs for i in source['imports']):
        needs.add(m)
        affected.append(m)
result = {
    'status': 'READ_ONLY_SOURCE_AND_CACHE_INVENTORY_NO_FIXED_TARGET_BUILD',
    'scope': '409 selected custom modules. Available means per-module source/object provenance, not a single freshly checked combined closure. Historical reused-only candidates remain excluded from authenticated availability. No Foundation or fixed-target source compiled/copied.',
    'driver': pin(__file__), 'closure': pin(HERE / 'closure.json'),
    'metadata': list(metadata.values()), 'modules': rows,
    'counts': {'custom': len(rows), 'foundation': sum(m.startswith('Foundation.') for m in modules),
               'available': len(rows)-len(missing), 'unavailable_or_reuse_only': len(missing),
               'reuse_only': len(provisional), 'affected_refresh': len(affected),
               'categories': dict(Counter(r['selected']['category'] if r['selected'] else 'none' for r in rows))},
    'minimal_missing_source_builds_dependency_order': missing,
    'conservative_affected_refresh_dependency_order': affected,
    'missing_foundation': [m for m in missing if m.startswith('Foundation.')],
    'historical_records_scanned_with_relevant_candidates': scanned,
    'historical_record_errors': record_errors,
    'rejected_candidates': rejected,
    'external_import_boundaries': closure['external'],
}
(HERE / 'inventory.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result['counts'], indent=2))
print('Missing Foundation:', result['missing_foundation'])
print('Missing/reuse-only:', '\n'.join(missing))
