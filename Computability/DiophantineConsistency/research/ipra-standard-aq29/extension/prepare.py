#!/usr/bin/env python3
"""Prepare a strict source extension from a completed matched fresh pair.

This is not a proof replay. Every parent source and import must be unchanged;
all additions are rebuilt against copies of their own sibling's seeds. Parent
source, direct-import, companion, provider and output checks must pass again.
Package-transitive and dynamic ancestry remain inherited.
"""
import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PAIR_TOOLS = HERE.parents[1] / 'fresh-project-closure'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash',
            '.ir.hash', '.ilean.hash')
MIN_FREE = 4 * 1024**3
POLICY_REL = 'Computability/DiophantineConsistency/research/ipra-standard-aq29/extension/task-policy.json'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def validate_graph(manifest):
    names, sources = manifest['order'], manifest['sources']
    if (len(names) != manifest['project_modules'] or len(set(names)) != len(names)
            or set(names) != set(sources) or not names or names[-1] != manifest['target']):
        raise ValueError('invalid graph coverage')
    seen = set()
    for name in names:
        row = sources[name]
        pattern=r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
        if (not isinstance(name,str) or not re.fullmatch(pattern,name) or
                not isinstance(row['imports'],list) or len(row['imports'])!=len(set(row['imports'])) or
                any(not isinstance(dep,str) or not re.fullmatch(pattern,dep) for dep in row['imports'])):
            raise ValueError(('malformed module or imports',name))
        if any(dep in sources and dep not in seen for dep in row['imports']):
            raise ValueError(('non-topological project import', name))
        seen.add(name)

def expected_names(manifest):
    names=manifest.get('expected_axiom_names')
    if (not isinstance(names,list) or not names or len(set(names))!=len(names) or
            any(not isinstance(n,str) or not n or not all(
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*",part) for part in n.split('.')) for n in names)):
        raise ValueError('missing or malformed target-specific axiom names')
    return names

def verify_policy(manifest):
    path=Path(manifest['root'])/POLICY_REL
    if path.is_symlink() or not path.is_file() or digest(path)!=manifest.get('target_policy_sha256'):
        raise ValueError('extension target policy mismatch')
    policy=json.loads(path.read_text())
    if policy != {'target':manifest['target'],'expected_axiom_names':expected_names(manifest)}:
        raise ValueError('extension target policy content mismatch')

def verify_freezer_identity(manifest):
    paths={'freezer_sha256':HERE/'freeze.py','preparer_sha256':HERE/'prepare.py',
           'planner_sha256':HERE.parent/'plan.py'}
    if any(digest(path)!=manifest.get(key) for key,path in paths.items()):
        raise ValueError('extension freezer tool provenance mismatch')

def check_freezer_observation(observation, snapshot_hash, snapshot_path, expected_rows):
    output=observation.get('observed_stdout')
    if (observation.get('observed_exit_code')!=0 or not isinstance(output,str) or
            not output.splitlines() or output.splitlines()[-1]!=f'FROZEN_NOT_COMPILED {expected_rows} sources {snapshot_hash}' or
            observation.get('snapshot_manifest_sha256')!=snapshot_hash or
            observation.get('snapshot_path')!=str(snapshot_path)):
        raise ValueError('freezer terminal observation does not match')

def select(old, new, records):
    """Accept only an unchanged ordered parent followed by new project modules."""
    validate_graph(old); validate_graph(new)
    expected_names(new)
    if (new['order'][:len(old['order'])] != old['order'] or
            len(new['order']) <= len(old['order']) or new['target'] in old['sources']):
        raise ValueError('extension requires unchanged ordered parent and a new target')
    if [r['module'] for r in records] != old['order']:
        raise ValueError('parent records do not cover the graph in order')
    old_src, new_src = old['sources'], new['sources']
    for record in records:
        name = record['module']
        direct = record['direct_inputs']
        declared = set(old_src[name]['imports'])
        actual = set(direct)
        if not declared <= actual or actual - declared - {'Init'}:
            raise ValueError(('parent actual/declaration mismatch', name))
        for dep, detail in direct.items():
            if (dep in old_src) != (detail['kind'] == 'project'):
                raise ValueError(('parent project dependency classification', name, dep))
            if dep in new_src and dep not in old_src:
                raise ValueError(('new project module shadows parent dependency', name, dep))
    changed = {n for n in old['order'] if any(old_src[n][k] != new_src[n][k]
                                               for k in ('sha256', 'imports', 'workspace_path'))}
    if changed:raise ValueError(('parent source drift; fresh successor required',sorted(changed)))
    affected=set(new['order'][len(old['order']):]);unaffected=set(old['order'])
    # Topological ordering and an unchanged parent prevent a copied object from
    # inheriting an added module or changed parent ancestor.
    ancestors = {}
    for name in new['order']:
        direct = {d for d in new_src[name]['imports'] if d in new_src}
        ancestry = set(direct)
        for dep in direct:
            ancestry.update(ancestors[dep])
        ancestors[name] = ancestry
        if name in unaffected and (ancestry & affected or any(
                old_src[d]['sha256'] != new_src[d]['sha256'] or
                old_src[d]['imports'] != new_src[d]['imports'] for d in ancestry)):
            raise ValueError(('unsafe reused transitive ancestry', name))
    return {'changed': [n for n in new['order'] if n in changed],
            'affected': [n for n in new['order'] if n in affected],
            'unaffected': [n for n in new['order'] if n in unaffected],
            'project_ancestor_counts': {n: len(ancestors[n]) for n in new['order']}}

def verify_snapshot(snapshot, manifest, current):
    root = Path(manifest['root']).resolve(strict=True)
    if digest(root/'lakefile.toml') != manifest['lakefile_sha256'] or digest(root/'lean-toolchain') != manifest['lean_toolchain_sha256']:
        raise ValueError('workspace Lake configuration changed')
    for name in manifest['order']:
        row = manifest['sources'][name]
        workspace_rel=Path(row['workspace_path'])
        if workspace_rel.is_absolute() or '..' in workspace_rel.parts or not workspace_rel.parts:
            raise ValueError(('unsafe workspace source path',name))
        q = snapshot/row['snapshot_path']
        expected = snapshot/'src'/(name.replace('.', '/') + '.lean')
        if q != expected or q.is_symlink() or not q.is_file() or digest(q) != row['sha256']:
            raise ValueError(('snapshot source mismatch', name))
        if any((snapshot/'src'/part).is_symlink() for part in q.relative_to(snapshot/'src').parents):
            raise ValueError(('snapshot parent symlink', name))
        if current and (not (root/row['workspace_path']).is_file() or digest(root/row['workspace_path']) != row['sha256']):
            raise ValueError(('workspace source drift', name))

def verify_current_git(manifest):
    root = Path(manifest['root']).resolve(strict=True)
    paths = sorted({row['workspace_path'] for row in manifest['sources'].values()})
    if 'target_policy_sha256' in manifest:paths=sorted(set(paths)|{POLICY_REL})
    def git(*args):
        return subprocess.check_output(['git', '-C', str(root), *args, '--', *paths]).split(b'\0')
    tracked = {p.decode() for p in git('ls-files', '-z') if p}
    changed = {p.decode() for p in git('diff', '--name-only', '-z', 'HEAD') if p}
    if tracked != set(paths) or changed:
        raise ValueError(('current sources not tracked and clean', sorted(set(paths)-tracked), sorted(changed)))
    return subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()

def copy_seeds(parent_lib, destination, names, outputs):
    """Copy one sibling's own unaffected artifacts; never link or cross providers."""
    destination.mkdir(parents=True, exist_ok=False)
    copied = {}
    for name in names:
        if shutil.disk_usage(destination).free < MIN_FREE:
            raise ValueError('disk reserve exhausted during seed copy')
        stem = parent_lib.joinpath(*name.split('.'))
        group = outputs[name]
        for suffix in SUFFIXES:
            original = Path(str(stem) + suffix)
            if str(original) not in group:
                raise ValueError(('parent companion record missing', str(original)))
            record = group[str(original)]
            if record is None:
                if os.path.lexists(original):
                    raise ValueError(('unexpected parent companion', str(original)))
                continue
            if (not original.is_file() or original.is_symlink() or
                    str(original.resolve()) != record['realpath'] or digest(original) != record['sha256']):
                raise ValueError(('parent companion drift', str(original)))
            dest = destination.joinpath(*name.split('.'))
            dest = Path(str(dest) + suffix)
            dest.parent.mkdir(parents=True, exist_ok=True)
            with original.open('rb') as src, dest.open('xb') as dst:
                shutil.copyfileobj(src, dst)
            if digest(dest) != record['sha256']:
                raise ValueError(('copy mismatch', str(dest)))
            copied[str(dest.relative_to(destination))] = record['sha256']
        if name.replace('.', '/') + '.olean' not in copied:
            raise ValueError(('parent object absent', name))
    return copied

def verify_seeds(lib, copied):
    actual = set()
    for path in lib.rglob('*'):
        if path.is_symlink():
            raise ValueError(('symlink in seed tree', str(path)))
        if path.is_file():
            rel = str(path.relative_to(lib)); actual.add(rel)
            if rel not in copied or digest(path) != copied[rel]:
                raise ValueError(('seed artifact drift', str(path)))
    if actual != set(copied):
        raise ValueError('seed inventory mismatch')

def check_parent_observation(observation, pair_hash, pair_path, expected_rows):
    output = observation.get('observed_stdout')
    if (observation.get('observed_exit_code') != 0 or not isinstance(output, str)
            or not output.splitlines() or output.splitlines()[-1] != f'MATCHED_PASS {expected_rows} rows'
            or observation.get('pair_state_sha256') != pair_hash
            or observation.get('pair_state_path') != str(pair_path)):
        raise ValueError('parent coordinator terminal observation does not match')

def run():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent', type=Path, required=True)
    parser.add_argument('--old-snapshot', type=Path, required=True)
    parser.add_argument('--new-snapshot', type=Path, required=True)
    parser.add_argument('--old-sha256', required=True)
    parser.add_argument('--new-sha256', required=True)
    parser.add_argument('--parent-pair-sha256', required=True)
    parser.add_argument('--parent-observation', type=Path, required=True)
    parser.add_argument('--parent-observation-sha256', required=True)
    parser.add_argument('--freezer-observation',type=Path,required=True)
    parser.add_argument('--freezer-observation-sha256',required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    parent = args.parent.resolve(strict=True)
    old_snap = args.old_snapshot.resolve(strict=True); new_snap = args.new_snapshot.resolve(strict=True)
    old_manifest, new_manifest = old_snap/'manifest.json', new_snap/'manifest.json'
    if digest(old_manifest) != args.old_sha256 or digest(new_manifest) != args.new_sha256:
        raise ValueError('snapshot manifest pin mismatch')
    old, new = json.loads(old_manifest.read_text()), json.loads(new_manifest.read_text())
    if old['status'] != 'FROZEN_NOT_COMPILED' or new['status'] != 'FROZEN_NOT_COMPILED':
        raise ValueError('invalid snapshot state')
    if (new.get('parent_manifest_sha256')!=args.old_sha256 or
            new.get('parent_pair_sha256')!=args.parent_pair_sha256 or
            new.get('parent_observation_sha256')!=args.parent_observation_sha256):
        raise ValueError('extension snapshot parent evidence mismatch')
    for key in ('root', 'lakefile_sha256', 'lean_toolchain_sha256'):
        if old[key] != new[key]:
            raise ValueError(('snapshot configuration changed; full rebuild required', key))
    verify_policy(new);verify_freezer_identity(new)
    freezer_observation=args.freezer_observation.resolve(strict=True)
    if digest(freezer_observation)!=args.freezer_observation_sha256:
        raise ValueError('freezer observation pin mismatch')
    check_freezer_observation(json.loads(freezer_observation.read_text()),args.new_sha256,new_snap,len(new['order']))
    verify_snapshot(old_snap, old, False); verify_snapshot(new_snap, new, True)
    head_before = verify_current_git(new)
    pair_path = parent/'pair-state.json'; pair = json.loads(pair_path.read_text())
    observation_path = args.parent_observation.resolve(strict=True)
    if digest(pair_path) != args.parent_pair_sha256 or digest(observation_path) != args.parent_observation_sha256:
        raise ValueError('parent pair or observation pin mismatch')
    check_parent_observation(json.loads(observation_path.read_text()), args.parent_pair_sha256,
                             pair_path, len(old['order']))
    if pair['status'] != 'MATCHED_PASS' or pair['snapshot_sha256'] != args.old_sha256:
        raise ValueError('parent matched fresh pair required')
    if [(r['label'], r['exit']) for r in pair['runs']] != [('author', 0), ('peer', 0)]:
        raise ValueError('parent actual process exits not both zero')
    for row in pair['runs']:
        if (digest(row['process_log']) != row['process_log_sha256'] or
                digest(parent/row['label']/'state.json') != row['builder_state_sha256']):
            raise ValueError(('parent process evidence drift', row['label']))
    for file, key in (('rebuild.py', 'driver_sha256'), ('compare.py', 'comparator_sha256'), ('run_pair.py', 'coordinator_sha256')):
        if digest(PAIR_TOOLS/file) != pair[key]:
            raise ValueError(('parent driver mismatch', file))
    spec = importlib.util.spec_from_file_location('matched_parent_compare', PAIR_TOOLS/'compare.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    comparison = module.compare(parent/'author/state.json', parent/'peer/state.json')
    if comparison != pair['comparison'] or comparison['status'] != 'MATCHED_PASS':
        raise ValueError('parent comparison does not reproduce')
    states = {label: json.loads((parent/label/'state.json').read_text()) for label in ('author', 'peer')}
    plan = select(old, new, states['author']['records'])
    if plan != select(old, new, states['peer']['records']):
        raise ValueError('sibling dependency plans differ')
    output = args.output.absolute()
    if output.exists() or output.is_symlink():
        raise ValueError('refusing to overwrite output')
    for prohibited in (parent, old_snap, new_snap, Path(states['author']['package_overlay']).resolve()):
        candidate = output.resolve()
        if candidate.is_relative_to(prohibited) or prohibited.is_relative_to(candidate):
            raise ValueError(('output overlaps protected root', str(prohibited)))
    if not output.parent.is_dir():
        raise ValueError('output parent directory must already exist')
    estimated_bytes = sum(
        Path(path).stat().st_size for label in ('author', 'peer') for name in plan['unaffected']
        for path, record in states[label]['outputs'][name].items() if record is not None)
    if shutil.disk_usage(output.parent).free < estimated_bytes + MIN_FREE:
        raise ValueError('insufficient disk for isolated seeds and reserve')
    output.mkdir(parents=True, exist_ok=False)
    start_pair_hash = digest(pair_path)
    seeds = {}
    for label in ('author', 'peer'):
        seeds[label] = copy_seeds(parent/label/'lib', output/label/'lib',
                                  plan['unaffected'], states[label]['outputs'])
    if seeds['author'] != seeds['peer']:
        raise ValueError('author and peer seed companions differ')
    for label in ('author', 'peer'):
        verify_seeds(output/label/'lib', seeds[label])
    verify_snapshot(new_snap, new, True)
    head_after = verify_current_git(new)
    if (digest(pair_path) != start_pair_hash or digest(old_manifest) != args.old_sha256 or
            digest(new_manifest) != args.new_sha256 or digest(observation_path) != args.parent_observation_sha256 or
            digest(freezer_observation)!=args.freezer_observation_sha256):
        raise ValueError('fixed inputs changed during preparation')
    # Authenticate original pair once more after copying before recording seeds.
    if module.compare(parent/'author/state.json', parent/'peer/state.json') != comparison:
        raise ValueError('parent pair changed during preparation')
    result = {'status': 'PREPARED_NOT_REBUILT', 'parent_pair': str(parent),
              'parent_pair_sha256': start_pair_hash, 'old_snapshot_sha256': args.old_sha256,
              'parent_observation': str(observation_path),
              'parent_observation_sha256': args.parent_observation_sha256,
              'freezer_observation':str(freezer_observation),
              'freezer_observation_sha256':args.freezer_observation_sha256,
              'new_snapshot_sha256': args.new_sha256, 'output': str(output),
              'workspace_head_before': head_before, 'workspace_head_after': head_after,
              'estimated_seed_bytes': estimated_bytes,
              'preparer_sha256': digest(Path(__file__)), 'plan': plan, 'seeds': seeds,
              'scope': 'Copied each matched parent sibling separately after direct-import and complete project-ancestry checks; affected modules have not been rebuilt. Package-transitive, dynamic and transient-mutation ancestry remains inherited.'}
    (output/'preparation.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print('PREPARED_NOT_REBUILT', len(plan['affected']), 'affected', len(plan['unaffected']), 'reused', flush=True)

if __name__ == '__main__':
    run()
