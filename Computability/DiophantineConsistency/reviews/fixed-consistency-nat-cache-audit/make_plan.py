"""Freeze a dependency-ordered proposal. This is not a build driver."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = HERE.parent


def pin(path):
    path = Path(path)
    return {'path': str(path.resolve()), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def require(test, message):
    if not test:
        raise RuntimeError(message)


inventory = json.loads((HERE / 'inventory.json').read_text())
fresh = set(inventory['conservative_affected_refresh_dependency_order'])
seeds = set(inventory['minimal_missing_source_builds_dependency_order'])
rows = []
seen = set()
cache_imports_fresh = []
for row in inventory['modules']:
    module = row['module']
    source = pin(row['source'])
    require(source['sha256'] == row['source_sha256'], 'Current source drift: ' + module)
    custom_imports = [m for m in row['imports'] if m in {r['module'] for r in inventory['modules']}]
    require(all(m in seen for m in custom_imports), 'Not dependency-ordered: ' + module)
    seen.add(module)
    action = 'fresh' if module in fresh else 'reuse'
    item = {'module': module, 'source': source, 'imports': row['imports'], 'action': action,
            'reason': 'missing_or_unattested_pair' if module in seeds else
                      'imports_refreshed_dependency' if module in fresh else
                      'current_source_attested_cache',
            'old_status': row['status']}
    if action == 'reuse':
        require(row['status'] == 'available_source_attested', 'Unattested reuse: ' + module)
        bad = [m for m in custom_imports if m in fresh]
        cache_imports_fresh.extend((module, m) for m in bad)
        chosen = row['selected']
        primary = next(o for o in chosen['objects'] if o['path'].endswith('.olean'))
        require(pin(primary['path'])['sha256'] == primary['sha256'], 'Object drift: ' + module)
        objects = []
        stem = primary['path'][:-len('.olean')]
        recorded = {o['path']: o['sha256'] for o in chosen['objects']}
        absent = []
        for suffix in ['.olean', '.olean.server', '.olean.private', '.ir']:
            path = Path(stem + suffix)
            if path.is_file():
                obj = pin(path)
                if str(path) in recorded:
                    require(obj['sha256'] == recorded[str(path)], 'Companion drift: ' + module)
                obj['prior_hash_in_selected_record'] = str(path) in recorded
                objects.append(obj)
            else:
                absent.append(str(path))
        item.update({'cache_category': chosen['category'], 'objects': objects,
                     'absent_companions': absent, 'provenance': chosen['provenance'],
                     'companion_scope': 'Prior recorded hashes retained where available; other companion hashes are observations now, not retroactive compilation attestations.'})
    rows.append(item)
require(not cache_imports_fresh, 'A reused client imports a fresh dependency')
require(not any(r['action'] == 'fresh' and r['module'].startswith('Foundation.') for r in rows),
        'Unplanned Foundation source build')
# The newly completed generic leaf joins this pre-existing409-module closure.
generic = json.loads((REV / 'foundation-pahf-nat-semantics-dependency-replay.json').read_text())
g = next(r for r in generic['fresh_modules'] if r['module'].endswith('.FoundationPAHFNatSemantics'))
require(pin(g['source'])['sha256'] == g['source_sha256'], 'Generic source drift')
require(pin(g['object'])['sha256'] == g['object_sha256'], 'Generic object drift')
result = {
    'status': 'PROPOSED_READ_ONLY_73_MODULE_REFRESH_NOT_EXECUTED',
    'source_snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'scope': '73 proposed fresh custom modules and336 reused members of the409 selected closure. All139 Foundation members reused; no broad Foundation or package rebuild. The existing generic Nat-semantics leaf is an additional authenticated cache member, bringing prerequisites to410 before a future fixed-target leaf/check. No fixed-target proof is authored or executed here.',
    'driver': pin(__file__), 'inventory': pin(HERE / 'inventory.json'),
    'external_boundaries': pin(HERE / 'external-boundaries.json'),
    'modules': rows,
    'fresh_seed_order': [r['module'] for r in rows if r['module'] in seeds],
    'fresh_additional_client_order': [r['module'] for r in rows if r['module'] in fresh-seeds],
    'fresh_order': [r['module'] for r in rows if r['module'] in fresh],
    'reused_client_imports_fresh': cache_imports_fresh,
    'counts': {'custom': len(rows), 'fresh_seed': len(seeds), 'fresh_total': len(fresh),
               'reuse': len(rows)-len(fresh), 'foundation_reuse':139,
               'reuse_categories': dict(Counter(r['cache_category'] for r in rows if r['action']=='reuse'))},
    'additional_generic_leaf': {'module': g['module'], 'source': pin(g['source']),
                                'object': pin(g['object']),
                                'provenance': pin(REV / 'foundation-pahf-nat-semantics-dependency-replay.json')},
    'future_fixed_leaf': 'Not written; intended Nat semantic comparison only, not HA ordinary-checker normalization or actual215 PA equivalence.',
}
(HERE / 'refresh-plan.json').write_text(json.dumps(result, indent=2) + '\n')
(HERE / 'fresh-order.txt').write_text('\n'.join(result['fresh_order']) + '\n')
print(result['counts'])
print('No reused client imports a fresh node; no Foundation rebuild planned.')
