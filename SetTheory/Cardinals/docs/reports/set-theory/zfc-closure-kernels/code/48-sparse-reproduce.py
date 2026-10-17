#!/usr/bin/env python3
"""Reproduce the delivered mathematical checks without changing frozen evidence.

Standard-library Python 3.10+ suffices. This is not a Lean/Coq build.
Full bounded searches are opt-in; they are not lower-bound proofs.
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
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    path = ROOT/'MANIFEST.sha256'
    if not path.exists():
        return {'status':'not present in development copy'}
    checked = 0
    for line in path.read_text().splitlines():
        expected, name = line.split('  ',1)
        target = (ROOT/name).resolve()
        if not target.is_relative_to(ROOT):
            raise ValueError('manifest path leaves the artifact directory')
        assert digest(target) == expected, f'manifest mismatch: {name}'
        checked += 1
    return {'status':'PASS','files':checked}


def read_table(path):
    table = {}
    for raw in path.read_text().splitlines():
        if not raw or raw.startswith('#'):
            continue
        q,read,write,move,nxt = raw.split()
        key = (int(q),int(read))
        assert key not in table
        assert move in ('L','R') and int(write) in (0,1)
        table[key] = (int(write),-1 if move=='L' else 1,int(nxt))
    return table


def machine_check(base):
    path = base/'machine/zfc_permutation252.tm'
    expected = json.loads((base/'machine/renumbering.json').read_text())
    assert digest(path) == expected['canonical_sha256']
    table = read_table(path)
    assert set(table) == {(q,b) for q in range(252) for b in (0,1)}
    assert all(0 <= row[2] <= 252 for row in table.values())
    assert sum(row[2] == 252 for row in table.values()) == 1
    old_path = base/'experiments/continuations/candidate-permutation252_zfc_permutation252_old.tm'
    assert digest(old_path) == expected['old_label_sha256']
    old = read_table(old_path)
    mapping = {int(a):b for a,b in expected['old_to_canonical'].items()}
    assert {(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in old.items()} == table
    state,head,ones = 0,0,set()
    endpoint = expected['blank_prefix']
    for _ in range(endpoint['steps']):
        assert state != 252
        write,move,state = table[(state,int(head in ones))]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
    assert state == endpoint['state_canonical']
    assert head == endpoint['head']
    assert sorted(ones) == endpoint['all_one_positions']
    return {'status':'PASS','working_states':252,'rows':len(table),
            'bootstrap_steps':endpoint['steps'],'state':state,'head':head,
            'all_nonzero_tape_cells_compared':len(ones),
            'canonical_sha256':digest(path),
            'scope':'Complete finite bootstrap and renumbering; not unbounded halting proof.'}


def run(base, name, args, cwd=None):
    then = time.monotonic()
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    proc = subprocess.run([sys.executable,*map(str,args)],cwd=cwd or base,
                          env=env,text=True,capture_output=True)
    if proc.returncode:
        raise RuntimeError(f'{name} failed\n{proc.stdout[-7000:]}\n{proc.stderr[-7000:]}')
    elapsed = round(time.monotonic()-then,3)
    print(f'PASS {name} ({elapsed}s)',flush=True)
    return {'status':'PASS','elapsed_seconds':elapsed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-searches',action='store_true')
    parser.add_argument('--skip-manifest',action='store_true')
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    assert __debug__, 'Run without Python optimization: assertions are verification checks.'
    started = time.monotonic()
    results = {'scope':'Executable finite audits and regression; no new kernel proof or state record.',
               'python':sys.version.split()[0],
               'manifest':{'status':'skipped intentionally'} if args.skip_manifest else check_manifest()}
    with tempfile.TemporaryDirectory(prefix='zfc-reproduction-') as tmp:
        work = Path(tmp)/'work'
        shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.aux','*.log','*.out','*.toc','report.pdf'))
        results['machine'] = machine_check(work)
        print('PASS canonical table and complete 82,552-step bootstrap',flush=True)
        original_ast = (work/'data/formula_circuits.json').read_bytes()
        results['source_export'] = run(work,'exact pinned source export',
            ['code/sparse_c254.py','--export-lean','source-excerpts/Code254.lean'])
        assert (work/'data/formula_circuits.json').read_bytes() == original_ast
        graph = (work/'data/arithmetic_graphs.txt').read_bytes()
        results['arithmetic_graphs'] = run(work,'explicit arithmetic graph regeneration',
                                          ['code/arithmetic_formula.py'])
        assert (work/'data/arithmetic_graphs.txt').read_bytes() == graph
        results['sparse_checker'] = run(work,'exact sparse numerical checker',
            ['code/sparse_c254.py','--test','--exhaustive','72','--output','data/reproduced-sparse.json'])
        numeric = json.loads((work/'data/reproduced-sparse.json').read_text())
        frozen = json.loads((work/'data/sparse_checker_tests.json').read_text())
        for field in frozen:
            if field != 'elapsed_seconds':
                assert numeric[field] == frozen[field], f'numerical metric differs: {field}'
        inv = work/'experiments/involutive'
        results['involutive'] = run(work,'involutive numerical self-test',
            ['involutive_search.py','self-test','--output','reproduced-evidence.json'],cwd=inv)
        assert json.loads((inv/'reproduced-evidence.json').read_text()) == json.loads((inv/'involutive-evidence.json').read_text())
        results['involutive_independent'] = run(work,'independent recursive-tour audit',
            ['review_involutive.py','involutive_search.py','reproduced-review.json'],cwd=inv)
        cont = work/'experiments/continuations'
        results['continuation_audit'] = run(work,'ranked continuation and ledger audit',
                                            ['audit_continuations.py'],cwd=cont)
        audit = json.loads((cont/'continuation-audit.json').read_text())
        assert audit['status'] == 'PASS' and audit['independent_control_successors'] == 8391
        assert audit['control_equivalence_classes'] == 4530 and audit['max_jump_rank'] == 4
        if args.full_searches:
            for mode,name,count,checks in [('uniform','continuation-uniform.json',55471,127868),
                                           ('incoming_actions','continuation-actions.json',132048,203162)]:
                results[mode] = run(work,f'full {mode} deletion search',
                    ['continuation_search.py','--mode',mode,'--output',name],cwd=cont)
                data = json.loads((cont/name).read_text())
                assert data['status'] == 'completed' and data['completed'] == count
                assert data['checks'] == checks and not data['survivors']
            results['residues'] = run(work,'four residue-domain analyses',['residue_phase.py'],cwd=cont)
            for M,m in [(2,1),(8,4),(32,8),(128,32)]:
                fresh = json.loads((cont/f'residue-phase-{M}-{m}.json').read_text())
                old = json.loads((ROOT/f'experiments/continuations/residue-phase-{M}-{m}.json').read_text())
                assert fresh['excluded'] == old['excluded'] and fresh['masks'] == old['masks']
            results['regenerated_ledger_audit'] = run(work,'regenerated ledger audit',
                                                      ['audit_continuations.py'],cwd=cont)
        results['total_elapsed_seconds'] = round(time.monotonic()-started,3)
        results['status'] = 'PASS'
    if args.output:
        args.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))


if __name__ == '__main__':
    main()
