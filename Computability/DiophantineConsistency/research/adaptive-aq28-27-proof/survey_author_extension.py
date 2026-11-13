#!/usr/bin/env python3
"""Provisional AQ28/27/26 extension graph; no Lean replay or parent audit.

The parent manifest is read without rehashing its source or object files.  The
24 draft sources are checked against tracked Git blobs and their declared
imports are traversed by the existing conservative source-line planner.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PARENT_SHA = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
PLANNER = ROOT / 'Computability/DiophantineConsistency/research/reference-coherent-replay/plan.py'
PREFIX = 'DiophantineConsistency.'
KINDS = ('Literal', 'Zeros', 'Maps', 'Transport', '', 'Checks')
NAMES = [f'AdaptiveAQ{n}{kind}' for n in (28, 27, 26) for kind in KINDS]
NAMES += [f'IPRAAQ{n}Native{kind}' for n in (28, 27, 26) for kind in ('', 'Checks')]
TARGETS = [PREFIX + f'AdaptiveAQ{n}Checks' for n in (28, 27, 26)]
TARGETS += [PREFIX + f'IPRAAQ{n}NativeChecks' for n in (28, 27, 26)]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--manifest-output', type=Path, required=True)
    args = ap.parse_args()
    if (args.output.exists() or args.output.is_symlink() or
            args.manifest_output.exists() or args.manifest_output.is_symlink()):
        raise ValueError('refusing to overwrite output')
    raw = (PARENT / 'manifest.json').read_bytes()
    if sha(raw) != PARENT_SHA:
        raise ValueError('parent manifest pin differs')
    parent = json.loads(raw)
    spec = importlib.util.spec_from_file_location('reference_plan', PLANNER)
    planner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(planner)
    cfg = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    libs = {x['name']: ROOT / x.get('srcDir', '.') for x in cfg['lean_lib']}
    libs.pop('Foundation', None)
    drafts = {PREFIX + name: HERE / 'draft-src' / (name + '.lean') for name in NAMES}
    result = planner.plan(ROOT, PARENT, parent, libs, TARGETS, drafts, 'historical', True)
    additions = result['additional_project_modules']
    if set(additions) != set(drafts) or len(additions) != 24:
        raise ValueError(('unexpected draft closure', additions))
    head = git('rev-parse', 'HEAD').decode().strip()
    reports = {}
    for name in additions:
        row = result['sources'][name]
        path = row['workspace_path']
        raw_source = (ROOT / path).read_bytes()
        if git('show', f'{head}:{path}') != raw_source:
            raise ValueError(('draft differs from tracked commit', path))
        source = raw_source.decode()
        printed = re.findall(r'^#print axioms\s+(\S+)\s*$', source, re.M)
        if printed:
            # Non-check modules print names relative to their explicitly
            # declared namespace; check modules use fully qualified names.
            if any('.' not in item for item in printed):
                ns = re.findall(r'^namespace\s+(\S+)\s*$', source, re.M)
                if ns != [name]:
                    raise ValueError(('unexpected report namespace', name, ns))
            reports[name] = [name + '.' + item if '.' not in item else item for item in printed]
            if len(set(reports[name])) != len(reports[name]):
                raise ValueError(('duplicate axiom declaration', name, reports[name]))
        if name.endswith('Checks'):
            expected = 4 if 'NativeChecks' in name else 9
            if len(reports.get(name, [])) != expected:
                raise ValueError(('unexpected check declarations', name, reports.get(name)))
    if len(reports) != 21 or sum(map(len, reports.values())) != 75:
        raise ValueError(('unexpected total axiom reports', len(reports), sum(map(len, reports.values()))))
    used = result.pop('parent_source_modules_used')
    result['parent_modules_used'] = len(used)
    result['parent_module_order_sha256'] = sha(('\n'.join(used) + '\n').encode())
    result['parent_modules_not_used'] = sorted(set(parent['order']) - set(used))
    result['direct_external_not_in_parent'] = sorted(set(result['external_modules']) - set(parent['external_modules']))
    result['sources'] = {name: result['sources'][name] for name in additions}
    result['order'] = additions
    result.update(parent_manifest_sha256=PARENT_SHA,
                  author_state_sha256='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153',
                  independent_author_audit_sha256='d21db65b29de29614976a3f32e42a1f44d8ddad60b30e5894abb473cfb5e9bcf',
                  planner_sha256=sha(PLANNER.read_bytes()), survey_sha256=sha(Path(__file__).read_bytes()),
                  workspace_head=head, expected_axiom_reports=reports,
                  scope='Provisional source-declared author-only extension graph; parent bytes, '
                        'drift, Lean import resolution and all draft proofs are unchecked by this survey.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write('\n')
    # The author-only replay driver must independently verify the tracked Git
    # blobs and copy them to its own frozen tree before any Lean invocation.
    manifest = {
        'status': 'FROZEN_ADDITIONS', 'source_commit': head,
        'parent_manifest_sha256': PARENT_SHA,
        'order': additions,
        'sources': {name: {'workspace_path': result['sources'][name]['workspace_path'],
                           'sha256': result['sources'][name]['source_sha256'],
                           'imports': result['sources'][name]['imports']} for name in additions},
        'axiom_reports': reports,
        'scope': 'Tracked draft source identities only; no Lean elaboration, '
                 'parent authentication, paired replay or proof claim.'}
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    with args.manifest_output.open('x') as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
        f.write('\n')
    print(result['status'], result['parent_modules_used'], 'parent modules;', len(additions),
          'draft modules;', len(reports), 'reporting modules;', sha(args.output.read_bytes()),
          'manifest', sha(args.manifest_output.read_bytes()))

if __name__ == '__main__':
    main()
