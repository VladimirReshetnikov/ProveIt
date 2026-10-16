#!/usr/bin/env python3
"""Bounded one-state folds of the experimentally boot-shared 255 table.

All arbitrary-register affine cases affected by a fold are checked. Runtime
success does not establish initialization or a kernel-checked result.
"""
from pathlib import Path
import argparse
import collections
import importlib.util
import json
import sys
import time

if not __debug__:
    raise SystemExit("Run without -O/-OO: this bounded search requires assertions")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory', type=Path, help="the --output folder from reproduce_decoder255.py")
    args = ap.parse_args()
    here = args.directory.resolve()
    spec = importlib.util.spec_from_file_location('transfer_verify', here / '_source09/verify.py')
    verify = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verify)
    table, _ = verify.load(here / 'decoder255_bootshare.tm')
    saved = sys.argv
    sys.argv = ['symexec.py', str(here / '_source09/machines/baseline254.tm'), str(here), '41']
    env = {}
    exec((here / '_source09/vendor/symexec.py').read_text().split('paths = json.load')[0], env)
    sys.argv = saved
    cases = []
    for path, op in verify.paths_from_dag('candidate202.json'):
        branches = [('-', None)] if op == 'halt' else (
            [('z','dec0'),('p','dec')] if op.endswith('.decnz') else
            [('-', 'inc' if op.endswith('.inc') else None)])
        for branch, effect in branches:
            if op.endswith('.inc') or (op.endswith('.decnz') and branch == 'p'):
                successor = env['inc'](path)
            elif op.endswith('.decnz'):
                successor = env['inc'](env['strip']('0', 1, path))
            elif op.startswith('_continue'):
                successor = env['strip']('1', int(op.split('.')[1]), path)
            elif op.startswith('_break'):
                successor = env['inc'](env['strip']('0', int(op.split('.')[1]), path))
            else:
                successor = ''
            effects = () if effect is None else ((effect, env['REG'][op.split('.')[1]]),)
            expected = (env['canon']([('b',1)], [('r',0,1,42),('b',1),
                        ('box', ('plain',)+effects)]) if successor is None else
                        env['canon']([('b',1)],env['tape_R'](successor,0,effects)))
            cases.append((path,op,branch,expected))

    def check(i, current):
        path,op,branch,expected = cases[i]
        traced = verify.TracingTable(current)
        env['T'] = traced
        try:
            out = env['run']('96',[('b',1)],env['tape_R'](path,0,()),branch,expected,fuel=500)
            good = out[0] == ('halt' if op == 'halt' else 'ok')
            steps = out[1]
        except Exception:
            good,steps = False,1000
        return good,steps,traced.used

    usage = collections.defaultdict(list)
    for i in range(len(cases)):
        ok,steps,trace = check(i,table)
        assert ok, i
        for q in {q for q,_ in trace}:
            usage[q].append((steps,i))
    for group in usage.values():
        group.sort()
    states = {q for q,_ in table}
    protected = {str(q) for q in verify.BOX_STATES} | {'96','5'}
    tested,survivors = 0,[]
    begin = time.monotonic()
    for dead in sorted(states-protected,key=lambda q:(len(usage[q]),int(q))):
        for replacement in sorted(states-{dead},key=int):
            candidate = {(q,b):(w,d,replacement if n == dead else n)
                         for (q,b),(w,d,n) in table.items() if q != dead}
            if all(check(i,candidate)[0] for _,i in usage[dead]):
                survivors.append([dead,replacement])
                print('Runtime fold candidate:',dead,'->',replacement,flush=True)
            tested += 1
    result = {'tested':tested,'survivors':survivors,
              'elapsed_seconds':time.monotonic()-begin,'gap_lower_bound':41,
              'fuel_limit_per_case':500,'affine_cases':len(cases),
              'excluded_source_states':sorted(protected,key=int),
              'scope':'bounded one-state fold search only; no minimality conclusion'}
    (here/'fold_search_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__ == '__main__':
    main()
