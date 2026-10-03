#!/usr/bin/env python3
"""Offline standard-library verifier and full scientific replay.

Integrity is anchored by INVENTORY.sha256 (and, externally, the release hash).
All retained upstream Python is inert .py.txt and is never imported or executed.
"""
import sys
sys.dontwritebytecode = True
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
DAG_SHA = 'a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2'
PROGRAM_SHA = 'fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01'
LITERAL_SHA = '3c8924dbb1b5d6e6b8897e59550b0e38a703654b87442c73487f411e94ae355b'

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))

def verify_inventory(root=ROOT):
    root = Path(root)
    seen = set()
    dirs = set()
    for p in root.rglob('*'):
        need(not p.is_symlink(), 'Symlink forbidden: ' + str(p.relative_to(root)))
        if p.is_dir():
            dirs.add(p.relative_to(root).as_posix())
        else:
            need(p.is_file(), 'Nonregular filesystem entry')
            seen.add(p.relative_to(root).as_posix())
    anchor = (root / 'INVENTORY.sha256').read_text(encoding='ascii')
    need(len(anchor) == 65 and anchor[-1] == '\n' and all(c in '0123456789abcdef' for c in anchor[:-1]), 'Malformed inventory anchor')
    need(digest(root / 'INVENTORY.json') == anchor.strip(), 'Inventory digest mismatch')
    inventory = read_json(root / 'INVENTORY.json')
    need(inventory['schema'] == 'grill-exact-inventory-v1', 'Inventory schema')
    files = inventory['files']
    expected = set(files) | {'INVENTORY.json', 'INVENTORY.sha256'}
    need(seen == expected, 'Inventory file-set mismatch; missing=' + repr(sorted(expected-seen)) + '; extra=' + repr(sorted(seen-expected)))
    need(dirs == set(inventory['directories']), 'Inventory directory-set mismatch')
    for name, rec in files.items():
        path = PurePosixPath(name)
        need(not path.is_absolute() and '..' not in path.parts and str(path) == name, 'Invalid inventory route')
        p = root / name
        need(p.stat().st_size == rec['bytes'] and digest(p) == rec['sha256'], 'Content digest mismatch: ' + name)
    # Check provenance independently; originals are hash commitments, delivered copies are verifiable bytes.
    provenance = read_json(root / 'PROVENANCE.json')
    for e in provenance['sources']:
        p = root / e['delivered']
        need(p.stat().st_size == e['delivered_bytes'] and digest(p) == e['delivered_sha256'], 'Provenance delivered-byte mismatch: '+e['delivered'])
        if e.get('byte_identical'):
            need(e['original_bytes'] == e['delivered_bytes'] and e['original_sha256'] == e['delivered_sha256'], 'False byte-identity receipt')
    for p in (root / 'replay_code').rglob('*.py'):
        need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(p.read_text()))), 'Removable assertion in executable replay')
    need(not list((root / 'frozen').rglob('*.py')), 'Frozen upstream executable extension')
    return {'status':'PASS_EXACT_INVENTORY', 'files':len(seen), 'directories':len(dirs), 'inventory_sha256':anchor.strip()}

def scientific_manifest(m):
    # Timing/resource snapshots and adapted code hashes are not scientific outputs.
    m = json.loads(json.dumps(m))
    m.pop('resources', None)
    m.pop('snapshots', None)
    m['extra'].pop('source_modules', None)
    return m

def replay(work):
    need(not any(work.iterdir()), 'Replay working directory must be empty')
    for src in (ROOT / 'frozen').iterdir():
        shutil.copytree(src, work / src.name)
    shutil.copytree(ROOT / 'frozen', work / 'frozen-copy')
    shutil.copyfile(ROOT / 'PROVENANCE.json', work / 'PROVENANCE.json')
    for p in (ROOT / 'replay_code').rglob('*.py'):
        dest = work / p.relative_to(ROOT / 'replay_code')
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, dest)
    outer_receipt=work/'input-audit/independent_outer_checks.json'
    outer=read_json(outer_receipt)
    outer['source_sha256']=digest(work/'input-audit/independent_outer_checks.py')
    outer_receipt.write_text(json.dumps(outer,indent=2,sort_keys=True)+'\n')
    initial_manifest = read_json(work / 'arithmetic/universal.json')
    reports = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    # Remove path injection into the isolated replay interpreter; scientific modules are sibling files.
    environment.pop('PYTHONPATH', None)
    flags = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    def run(name, relative, *args):
        started=time.monotonic()
        proc = subprocess.run(flags + [str(work / relative), *args], cwd=work, env=environment,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=600)
        need(proc.returncode == 0, name + ' failed:\n' + proc.stdout)
        reports.append({'check':name,'status':'PASS','seconds':round(time.monotonic()-started,3)})
        print(json.dumps(reports[-1]), flush=True)
    run('rebuild literal source tables', 'input-research/literal/build_literal.py')
    need(digest(work/'input-research/literal/literal_tables.json') == LITERAL_SHA, 'Re-emitted literal table differs')
    run('independent literal table/source semantics', 'input-research/literal/review_literal_tables.py')
    run('bounded original macro identities', 'input-research/own_macro_checks.py')
    run('literal queue simulation', 'input-research/literal/check_literal.py')
    run('normalization invariants', 'input-audit/normalization/check_normalization.py')
    run('independent input outer interfaces', 'input-audit/independent_outer_checks.py')
    run('independent full run-table byte/phase/cleanup checks', 'arithmetic/review_grill_program.py')
    run('independent exact all-row and all-coefficient audit', 'circuit-audit/check_exact_source.py')
    run('independent complete-interface checks', 'circuit-audit/check_interfaces.py')
    run('input loader and complete recoder identities', 'arithmetic/input_verify.py', '--write')
    run('native source identities', 'arithmetic/native_check.py')
    run('native streamed-backend identities', 'arithmetic/native_backend_check.py')
    run('rebuild complete run table', 'arithmetic/emit_grill_program.py')
    need(digest(work/'arithmetic/grill_program.u32') == PROGRAM_SHA, 'Re-emitted program differs')
    run('re-emit full 3,600,546-gate DAG', 'arithmetic/compose_universal.py', '--size', '397488')
    need(digest(work/'arithmetic/universal.dag') == DAG_SHA, 'Re-emitted full DAG differs')
    need(scientific_manifest(read_json(work/'arithmetic/universal.json')) == scientific_manifest(initial_manifest), 'Re-emitted scientific manifest differs')
    run('independent whole-DAG differential checks', 'arithmetic/review_complete_dag.py')
    need(not list(work.rglob('__pycache__')), 'Replay generated forbidden cache')
    return {'status':'PASS_OFFLINE_REPLAY','optimized':bool(sys.flags.optimize),'upstream_python_executed':False,
            'dag_bytes':(work/'arithmetic/universal.dag').stat().st_size,'dag_sha256':DAG_SHA,
            'program_sha256':PROGRAM_SHA,'literal_sha256':LITERAL_SHA,
            'scientific_manifest_exact_match_excluding_resources_and_adapted_code_hashes':True,'checks':reports}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--verify-only', action='store_true')
    p.add_argument('--work-dir', type=Path, help='Optional EMPTY output directory outside this package; preserve replay outputs here')
    args = p.parse_args()
    verified=verify_inventory()
    print(json.dumps(verified, sort_keys=True), flush=True)
    if args.verify_only:
        return
    if args.work_dir:
        work=args.work_dir.expanduser().resolve()
        need(work != ROOT and ROOT not in work.parents, 'Outputs must stay outside the integrity-checked package')
        work.mkdir(parents=True, exist_ok=True)
        result=replay(work)
    else:
        with tempfile.TemporaryDirectory(prefix='grill-offline-replay-') as temp:
            result=replay(Path(temp))
    print(json.dumps(result,indent=2,sort_keys=True), flush=True)
    verify_inventory()

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
