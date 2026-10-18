#!/usr/bin/env python3
"""Stage the reviewed batch166 write in a NEW external directory.

Copies only pinned source/evidence bytes and authored prose, without changing
the repository. The emitted publication map is for root's separate reviewed
installation/commit. No supplied code, verifier, compiler or builder is run.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json

HOST = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
def require(condition, message):
    if not condition: raise ValueError(message)
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def relative(name):
    p = PurePosixPath(name)
    require(bool(p.parts) and not p.is_absolute() and '..' not in p.parts and '\\' not in name
            and ':' not in name and '\n' not in name and '\r' not in name, 'Unsafe target ' + name)
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--inputs', type=Path, default=Path(__file__).with_name('write-inputs.json'))
    ap.add_argument('--inputs-sha', required=True)
    args = ap.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    require(not output.exists() and output != repo and repo not in output.parents, 'Output must be new and external')
    require(sha(args.inputs) == args.inputs_sha, 'Wrong frozen inputs manifest')
    p = json.loads(args.inputs.read_text())
    require(p['status'] == 'READY_FOR_ROOT_SOURCE_REVIEW' and p['batch'] == 166 and p['host_source'] == 70, 'Wrong write scope')
    require(p['placement'] == '6619bd0002a0771284cfda26d0e734f76cffaaa4', 'Wrong placement')
    require(sha(repo / p['base_article']['path']) == p['base_article']['sha256'], 'Base article changed')
    plan = json.loads(Path(p['placement_map']['path']).read_text())
    require(sha(p['placement_map']['path']) == p['placement_map']['sha256'], 'Placement map changed')
    rows = [r for r in plan['files'] if r['disposition'] == 'place_unchanged']
    require(len(rows) == 170 and len(plan['files']) == 191, 'Wrong placement census')
    for row in rows:
        require(sha(repo / row['target']) == row['sha256'], 'Placed ancillary changed: ' + row['target'])
    targets = set()
    for row in p['files']:
        src = Path(row['source'])
        require(src.is_file() and sha(src) == row['sha256'] and src.stat().st_size == row['bytes'], 'Changed input ' + str(src))
        relative(row['target'])
        require(row['target'] not in targets, 'Duplicate target')
        targets.add(row['target'])
        dest = repo / row['target']
        require(repo in dest.resolve().parents, 'Escaping repository target')
        if 'replace_before_sha256' in row:
            require(row['target'] == HOST + '/README.md' and sha(dest) == row['replace_before_sha256'], 'README baseline changed')
        else:
            require(not dest.exists() and not dest.is_symlink(), 'New target exists: ' + str(dest))
    full = json.loads(Path(p['full_runtime']['execution']).read_text())
    data = json.loads(Path(p['full_runtime']['result']).read_text())
    require(full['returncode'] == 0 and not full['timed_out'] and full['semantic_postchecks'] == 'PASS', 'Full replay did not pass')
    require(data['status'] == 'PASS' and data['complete'] and data['positive_progress_checked']
            and data['counts'] == {'cases': 8391, 'symbolic_rules': 2315075}
            and len(data['rows']) == 488 and data['minimum_steps'] == 13, 'Wrong complete principal scope')
    output.mkdir()
    result = []
    for row in p['files']:
        dest = output / 'files' / row['target']
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(Path(row['source']).read_bytes())
        require(sha(dest) == row['sha256'], 'Staged byte mismatch')
        result.append(dict(row, source=str(dest)))
    target = HOST + '/data/intake-166-write-inputs.json'
    require(target not in targets and not (repo / target).exists(), 'Inputs provenance target exists')
    dest = output / 'files' / target
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(args.inputs.read_bytes())
    result.append({'source': str(dest), 'target': target, 'sha256': args.inputs_sha,
                   'bytes': dest.stat().st_size, 'role': 'exact frozen write inputs and history mapping'})
    for row in p['files']:
        require(sha(row['source']) == row['sha256'], 'Source changed during staging')
    require(sha(args.inputs) == args.inputs_sha, 'Inputs changed during staging')
    record = {'status': 'STAGED_FOR_ROOT_REVIEW_NOT_INSTALLED', 'batch': 166, 'placement': p['placement'],
              'host_sources': 70, 'collection_reports': 290, 'files': result,
              'input_manifest_sha256': args.inputs_sha, 'builder_sha256': sha(__file__),
              'base_article': p['base_article'], 'maintained_mutations': False,
              'supplied_or_proof_execution': False, 'catalogue_pending_separate_step': True}
    (output / 'publication-map.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'files': len(result), 'map': str(output / 'publication-map.json')}))

if __name__ == '__main__': main()
