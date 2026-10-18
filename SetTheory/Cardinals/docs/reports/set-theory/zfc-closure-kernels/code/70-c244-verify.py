#!/usr/bin/env python3
"""Replay the portable checks for the exact 244-state construction.

Python 3.10+, standard library only. The default run proves the local
simulation anew and checks a complete blank prefix. It checks the integrity
of the archived all-values certificate; --full-runtime also regenerates it.
The mathematical induction arguments are in report.tex and proof/.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
OLD = 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
NEW = 'd603bc3793ac9373f510a05d4e898f4ee7b4cac492821406a665554dca5c6daf'
DENSE = '2ea5521fa7d0fc24b4f3dc07d497b10de2532147225820033d9c96f247444187'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_json(path):
    return json.loads(path.read_text())

def run(args, cwd):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    p = subprocess.run([sys.executable, '-B', *map(str, args)], cwd=cwd,
                       env=env, text=True, capture_output=True)
    if p.returncode:
        raise RuntimeError(f'Failed: {args}\n{p.stdout}\n{p.stderr}')
    print('PASS', args[0])
    return p.stdout

def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full-runtime', action='store_true',
                    help='Also regenerate all 8,391 universal frame cases (several minutes).')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    runtime = ROOT/'runtime'
    expected = {
        ROOT/'machine/zfc_compensated244.tm': DENSE,
        ROOT/'machine/zfc_compensated244_old.tm': NEW,
        runtime/'reference/zfc245_old.tm': OLD,
        runtime/'candidate_1_244.tm': DENSE,
        runtime/'candidate_1_244_old.tm': NEW,
    }
    for path, digest in expected.items():
        assert sha(path) == digest, path
    manifest_count = 0
    manifest = ROOT/'SHA256SUMS'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            assert sha(ROOT/name) == digest, name
            manifest_count += 1
        print('PASS SHA256SUMS', manifest_count, 'files')

    with tempfile.TemporaryDirectory(prefix='zfc244-replay-') as temp:
        work = Path(temp)
        (work/'reference').mkdir()
        shutil.copy2(runtime/'reference/zfc245_old.tm', work/'reference/zfc245_old.tm')
        for name in ('rebuild_candidates.py', 'prove_contextual_fold.py',
                     'verify_local_stuttering.py', 'check_new_boot.py'):
            shutil.copy2(runtime/name, work/name)
        run(['rebuild_candidates.py'], work)
        assert sha(work/'candidate_1_244_old.tm') == NEW
        assert sha(work/'candidate_1_244.tm') == DENSE
        assert (work/'candidate_1_renumbering.json').read_bytes() == (
            ROOT/'machine/renumbering.json').read_bytes()
        for i in range(1, 4):
            for suffix in ('244.tm', '244_old.tm', 'renumbering.json'):
                name = f'candidate_{i}_{suffix}'
                assert (work/name).read_bytes() == (runtime/name).read_bytes()
        run(['prove_contextual_fold.py'], work)
        direct = read_json(work/'contextual_fold_proof.json')
        assert direct == read_json(runtime/'contextual_fold_proof.json')
        run(['verify_local_stuttering.py', 'reference/zfc245_old.tm',
             'candidate_1_244_old.tm', '--output', 'independent.json'], work)
        independent = read_json(work/'independent.json')
        assert independent == read_json(runtime/'local-stuttering-audit.json')
        run(['check_new_boot.py', 'candidate_1_244_old.tm', 'boot.json'], work)
        boot = read_json(work/'boot.json')
        assert boot == read_json(runtime/'candidate_1_boot.json')
        assert boot['steps'] == 407951
        assert boot['physical_registers'] == [0,0,0,3,0,0,3,0,0]
        assert boot['spare_values'] == [1]*167
        assert boot['one_count'] == 351
        assert (boot['head'], boot['header'], boot['dispatcher']) == (-5,176,96)

        archived = read_json(runtime/'candidate_1_full_symbolic.json')
        assert archived['status'] == 'PASS' and archived['complete']
        assert archived['table_sha256'] == NEW
        assert archived['source_sha256'] == sha(runtime/'reference/context246/sources/Prog254.v')
        assert archived['alternative_sites_sha256'] == sha(runtime/'certificate/sites_physical.json')
        assert archived['invariant_sha256'] == sha(runtime/'results/interval-invariants.json')
        assert archived['counts'] == {'cases':8391, 'symbolic_rules':2315075}
        assert archived['expected_cases'] == len(archived['cases']) == 8391
        assert len(archived['rows']) == 488 and archived['minimum_steps'] == 13
        assert archived['positive_progress_checked']
        replay = work/'runtime-replay.json'
        command = [runtime/'code/full_symbolic_parametric.py', '--table',
                   runtime/'candidate_1_244_old.tm', '--all-values', '--sites',
                   runtime/'certificate/sites_physical.json', '--output', replay]
        if not args.full_runtime:
            command += ['--limit', '1']
        run(command, ROOT)
        replayed = read_json(replay)
        if args.full_runtime:
            assert {k:v for k,v in replayed.items() if k!='seconds'} == {
                k:v for k,v in archived.items() if k!='seconds'}
        else:
            assert replayed['status'] == 'PASS_LIMITED'
            assert replayed['counts']['cases'] == 1

        shutil.copytree(ROOT/'equational', work/'equational')
        run(['verify_backend.py'], work/'equational')
        run(['equational_search.py', 'demo_theory.json', '--search-below', '184'], work/'equational')
        eq = read_json(work/'equational/verification.json')
        assert eq == read_json(ROOT/'equational/verification.json')

    result = {
        'status':'PASS_PORTABLE_244_CONSTRUCTION',
        'baseline_old_sha256':OLD, 'new_old_sha256':NEW, 'new_canonical_sha256':DENSE,
        'working_states':244, 'binary_rows':488,
        'exact_rebuild_all_three_variants':True,
        'direct_local_proof_replayed':True,
        'independent_local_proof_replayed':True,
        'ordinary_checkpoint_rows':482, 'exceptional_local_cases':7,
        'invariant_boolean_implications':7784,
        'blank_sparse_dense_replayed':True, 'blank_steps':407951,
        'archived_full_runtime_integrity_checked':True,
        'archived_guarded_cases':8391, 'archived_covered_rows':488,
        'full_runtime_replayed_in_this_invocation':args.full_runtime,
        'runtime_dependency_smoke_cases':8391 if args.full_runtime else 1,
        'equational_backend_replayed':True,
        'artificial_contradiction_demo_replayed':True,
        'proof_assistant_endpoint_for_244_claimed':False,
    }
    destination = args.output or ROOT/'replay-results'/(
        'full-verification.json' if args.full_runtime else 'fast-verification.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
