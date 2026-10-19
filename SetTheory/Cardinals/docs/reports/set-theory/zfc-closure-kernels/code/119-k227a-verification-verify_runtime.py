#!/usr/bin/env python3
"""Universal instruction simulation for an explicit table and complete source.

This is an ordinary mathematical checker based on unary and finite-list
induction. It is not a proof-assistant kernel certificate. A PASS establishes
the runtime interface; source calibration and blank startup are separate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def parse_table(p):
    table = {}
    start = None
    for line in Path(p).read_text().splitlines():
        if not line or line.startswith('#'):
            if line.startswith('#! start ') or line.startswith('# start '):
                start = int(line.split()[-1])
            continue
        q, r, w, d, z = line.split()
        q, r, w, z = map(int, (q, r, w, z))
        require(r in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad row')
        require((q, r) not in table, 'Duplicate row')
        table[q, r] = w, 1 if d == 'R' else -1, z
    working = {q for q, r in table}
    require(start == 95 and 96 in working and 254 not in working,
            'Expected normalized start95 / runtime96 / halt254')
    require(all((q, r) in table for q in working for r in (0, 1)), 'Missing row')
    require({z for w, d, z in table.values()} - working == {254}, 'Bad targets')
    return table


def source_facts(sites):
    require(isinstance(sites, list) and sites, 'Empty source')
    leaves, prefixes = set(), set()
    for row in sites:
        require(isinstance(row, list) and len(row) == 3, 'Bad source row')
        pc, op, arg = row
        require(isinstance(pc, str) and 0 < len(pc) <= 64
                and set(pc) <= {'0', '1'}, 'Bad source path')
        require(pc not in leaves, 'Duplicate source path')
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Unknown instruction')
        if op == 'CH':
            require(arg is None, 'Bad halt argument')
        elif op in ('CI', 'CD'):
            require(type(arg) is int and 0 <= arg < 9, 'Bad register')
        else:
            require(type(arg) is int and arg >= 1, 'Bad control depth')
    require(not leaves.intersection(prefixes), 'Leaf is also internal node')
    require(all(p+b in leaves or p+b in prefixes
                for p in prefixes for b in ('0', '1')), 'Incomplete binary tree')
    require(len(prefixes) == len(leaves)-1, 'Invalid full-tree census')
    require(sites == sorted(sites), 'Source order is not lexicographic')
    return dict(leaves=len(leaves), guarded_cases=sum(1+(op == 'CD') for _, op, _ in sites),
                maximum_depth=max(map(len, leaves)),
                maximum_zero_run=max(len(x) for p in leaves for x in p.split('1')),
                complete_binary_tree=True)


def main():
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--engine-dir', type=Path, required=True)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--states', type=int, required=True)
    ap.add_argument('--leaves', type=int, required=True)
    ap.add_argument('--cases', type=int, required=True)
    ap.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    require(a.limit >= 0, 'Negative prefix limit')
    require(sha(a.engine_dir/'symbolic_runtime.py') ==
            'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
            'Unexpected induction engine')
    require(sha(a.engine_dir/'independent_runtime.py') ==
            '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
            'Unexpected runtime helper')
    sys.path.insert(0, str(a.engine_dir.resolve()))
    import symbolic_runtime as s
    table = parse_table(a.table)
    sites = json.loads(a.sites.read_text())
    facts = source_facts(sites)
    require(len(table) == 2*a.states, 'Wrong state count')
    require(facts['leaves'] == a.leaves and facts['guarded_cases'] == a.cases,
            'Wrong source census')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    began = time.monotonic()
    receipt = dict(status='IN_PROGRESS', table_sha256=sha(a.table),
                   sites_sha256=sha(a.sites), driver_sha256=sha(__file__),
                   engine_sha256=sha(s.__file__), helper_sha256=sha(s.r.__file__),
                   working_states=a.states, rows=len(table), source=facts,
                   expected_cases=a.cases, python_version=sys.version,
                   duration_slots=['constant', 'gap', *[f'R{i}' for i in range(9)],
                                   'first_spare', 'remaining_spare_list_width'],
                   scope='All nine independent natural register values, both decrement '
                         'guards, every natural extra gap, arbitrary first spare value, '
                         'and arbitrary finite spare tail. Exact whole tape, head '
                         'displacement, source successor and strictly positive duration.',
                   proof_status='Ordinary mathematical verification; not a kernel-checked endpoint.',
                   proof_construction_limit=4000,
                   limit_scope='The limit bounds symbolic proof construction only; '
                               'concrete time and data sizes are unbounded.')
    cases, used = [], set()

    def save():
        receipt.update(cases=len(cases), seconds=time.monotonic()-began)
        a.output.write_text(json.dumps(receipt, indent=2)+'\n')

    try:
        lemmas, blocks = s.prove_blocks(table)
        receipt['list_induction_blocks'] = blocks
        print('Four arbitrary-context list induction schemas proved.', flush=True)
        for i, site in enumerate(sites):
            for positive in ((False, True) if site[1] == 'CD' else (False,)):
                answer = s.case(table, lemmas, site, positive)
                used.update(answer.pop('rows'))
                answer.pop('trace')
                cases.append(dict(site_index=i, positive=positive, **answer))
                if len(cases) % 1000 == 0:
                    save()
                    print('proved', len(cases), 'cases;', round(time.monotonic()-began, 2),
                          'seconds', flush=True)
                if a.limit and len(cases) >= a.limit and len(cases) < a.cases:
                    receipt['status'] = 'PARTIAL_PREFIX_PASS'
                    save()
                    return
        require(len(cases) == a.cases, 'Incomplete proof')
        block_rows = {tuple(e[1][:2]) for b in blocks for e in b['trace'] if e[0] != 'list'}
        require(used | block_rows == set(table), 'Not every row covered by runtime or block proof')
        cp = a.output.with_name(a.output.stem+'_cases.json')
        cp.write_text(json.dumps(cases, indent=2)+'\n')
        receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS',
                       symbolic_steps=sum(x['symbolic_steps'] for x in cases),
                       minimum_actual_steps=min(x['duration'][0] for x in cases),
                       maximum_symbolic_steps=max(x['symbolic_steps'] for x in cases),
                       directly_used_rows=sorted(used), all_rows_covered=True,
                       cases_file=cp.name, cases_sha256=sha(cp))
        save()
        print(json.dumps({k: v for k, v in receipt.items()
                          if k not in ('directly_used_rows', 'list_induction_blocks')}, indent=2), flush=True)
    except Exception as exc:
        receipt.update(status='NOT_PROVED', site_index=locals().get('i'),
                       site=locals().get('site'), positive=locals().get('positive'), error=repr(exc))
        save()
        raise


if __name__ == '__main__':
    main()
