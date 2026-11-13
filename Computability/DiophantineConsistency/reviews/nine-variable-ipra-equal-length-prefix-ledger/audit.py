#!/usr/bin/env python3
"""Audit a prefix of the equal-source-root-length nine-variable replay.

Normalize only source paths in output bytes and already-checked predecessor
hashes in guard records. This is not a Lean serialization semantics theorem.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
RUNNER = DC / 'research/nine-variable-ipra/bounded-build-preflight/replay.py'
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
VERIFY = Path('/tmp/nine-ipra-guarded-verify-20261102-a')


def need(condition, message):
    if not condition: raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def normalize(value, root, hashes):
    if isinstance(value, str):
        value = value.replace(str(root), '<ROOT>')
        return hashes.get(value, value)
    if isinstance(value, list): return [normalize(x, root, hashes) for x in value]
    if isinstance(value, dict):
        return {normalize(k, root, hashes): normalize(v, root, hashes) for k, v in value.items()}
    return value


parser = argparse.ArgumentParser()
parser.add_argument('--upto', type=int, required=True)
args = parser.parse_args()
need(1 <= args.upto <= 104, 'bad prefix length')
need(len(str(AUTHOR)) == len(str(VERIFY)), 'source root length mismatch')
for name, root in [('author', AUTHOR), ('verify', VERIFY)]:
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                          '--output', str(root), '--check'], cwd=ROOT,
                         capture_output=True, text=True, timeout=180)
    words = run.stdout.strip().split()
    ok = (run.stdout.strip() == 'ALL_STAGES_RECORDED 104' or
          (name == 'verify' and len(words) >= 4 and words[0] == 'READY_NO_LEAN' and
           words[1].isdigit() and int(words[1]) >= args.upto and words[2] == 'completed;'))
    need(run.returncode == 0 and not run.stderr and ok, ('ledger check', name, run.stdout, run.stderr))

ma, mv = [json.loads((root / 'manifest.json').read_text()) for root in (AUTHOR, VERIFY)]
need(ma['modules'] == mv['modules'] and len(ma['modules']) == 104 and
     ma['runner_sha256'] == mv['runner_sha256'] == digest(RUNNER), 'plan/runner mismatch')
hash_map = {}; completed = {}; rows = []
for i in range(1, args.upto + 1):
    paths = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, VERIFY)]
    a, v = [json.loads(p.read_text()) for p in paths]
    need(a['status'] == v['status'] == 'PASS' and a['module'] == v['module'] == ma['modules'][i-1]['module']
         and a['source_sha256'] == v['source_sha256'], ('source/status mismatch', i))
    logs = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, v)]
    need(logs[0] == logs[1], ('normalized compiler log mismatch', i))
    author_direct = {name: entry['record']['sha256'] for name, entry in a['direct'].items()}
    verify_direct = {name: entry['record']['sha256'] for name, entry in v['direct'].items()}
    need(set(author_direct) == set(verify_direct), ('direct import set mismatch', i))
    differing = []
    for module in sorted(author_direct):
        ah, vh = author_direct[module], verify_direct[module]
        if ah != vh:
            need(module in completed and completed[module] == (ah, vh),
                 ('different input is not an already checked predecessor', i, module))
            differing.append({'module': module, 'author_sha256': ah, 'verify_sha256': vh})
    need(normalize(a['direct'], AUTHOR, {}) == normalize(v['direct'], VERIFY, hash_map) and
         normalize(a['direct_guards'], AUTHOR, {}) == normalize(v['direct_guards'], VERIFY, hash_map),
         ('direct/candidate guard mismatch after checked predecessor mapping', i))
    objects = [Path(r['output']['resolved']).read_bytes() for r in (a, v)]
    for obj, receipt in zip(objects, (a, v)):
        need(sha256(obj).hexdigest() == receipt['output']['sha256'], ('output drift', i))
    paths_source = [r['command'][5].encode() for r in (a, v)]
    need(len(paths_source[0]) == len(paths_source[1]) and len(objects[0]) == len(objects[1]),
         ('unequal source-path or object lengths', i))
    if objects[0] == objects[1]:
        comparison = 'byte-identical'
    else:
        need(objects[0].count(paths_source[0]) == objects[1].count(paths_source[1]) == 1 and
             objects[0].replace(paths_source[0], paths_source[1]) == objects[1],
             ('output differs beyond equal-length source pathname', i))
        comparison = 'equal-after-one-source-path-replacement'
    ah = a['output']['sha256']; vh = v['output']['sha256']
    if ah != vh:
        need(vh not in hash_map or hash_map[vh] == ah, ('ambiguous predecessor hash mapping', i))
        hash_map[vh] = ah
    completed[a['module']] = (ah, vh)
    if i in (81, 104):
        reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", logs[0], re.S)
        names = re.findall(r'^#print axioms (\S+)', Path(a['command'][5]).read_text(), re.M)
        actual = [name if i == 81 else name.rsplit('.', 1)[-1] for name, _ in reports]
        need(len(reports) == len(names) == (15 if i == 81 else 4) and actual == names and
             all({x.strip() for x in axioms.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
                 for _, axioms in reports), ('named axiom reports mismatch', i))
    rows.append({'stage': i, 'module': a['module'], 'source_sha256': a['source_sha256'],
                 'author_object_sha256': ah, 'verify_object_sha256': vh, 'comparison': comparison,
                 'direct_input_differences': differing, 'direct_guard_count': len(a['direct_guards']),
                 'normalized_log_sha256': sha256(logs[0].encode()).hexdigest(),
                 'author_receipt_sha256': digest(paths[0]), 'verify_receipt_sha256': digest(paths[1])})
print(json.dumps({'status': 'EQUAL_LENGTH_PREFIX_SCOPED_COMPARISON_PASS', 'upto': args.upto,
                  'runner_sha256': digest(RUNNER), 'author_manifest_sha256': digest(AUTHOR / 'manifest.json'),
                  'verify_manifest_sha256': digest(VERIFY / 'manifest.json'), 'stages': rows,
                  'scope': 'sampled guarded prefix, byte comparison after equal-length source-path '
                           'replacement; no Lean object-format semantics, full inherited ancestry or '
                           'file/PDF binding'}, indent=2, sort_keys=True))
