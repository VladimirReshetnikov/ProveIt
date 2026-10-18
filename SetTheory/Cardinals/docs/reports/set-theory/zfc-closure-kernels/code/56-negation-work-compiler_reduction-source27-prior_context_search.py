#!/usr/bin/env python3
"""Experimental state-redirection search using the published affine executor.

This is a diagnostic candidate search, not a proof or record certificate.
Its box summaries remain justified only when the underlying box transitions
are preserved. No successful candidate is reported without all runtime sites;
bootstrap and kernel verification are separate outstanding obligations.
"""
from pathlib import Path
import argparse
from collections import defaultdict
import json
import re
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from analyze_table import parse_table


def program_sites(program):
    import hashlib
    raw = Path(program).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
    text = raw.decode()
    body = text.split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', body)
    assert len(nodes) == 6459
    phys = (6, 7, 0, 2, 1, 8, 4, 3, 5)
    sites = []
    todo = [('CN 0', '')]
    while todo:
        v, q = todo.pop()
        kind, *arg = v.split()
        if kind == 'CN':
            l, r = nodes[int(arg[0])]
            todo.extend([(r, q + '1'), (l, q + '0')])
        else:
            a = None if not arg else int(arg[0])
            if kind in ('CI', 'CD'):
                a = phys[a]
            sites.append((q, kind, a))
    assert len(sites) == 6460
    return sites


def executor(table, executor_path):
    # Reuse the explicitly identified upstream design model, unchanged except
    # for an observation callback; its bottom-level CLI driver is not executed.
    import hashlib
    raw = Path(executor_path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d'
    code = raw.decode().split('paths = json.load', 1)[0]
    code = 'SKIP =' + code.split('SKIP =', 1)[1]
    code = code.replace('    while fuel > 0:\n', '    while fuel > 0:\n        if OBSERVE is not None: OBSERVE(q, form, L, R, branch, expect)\n')
    ns = {'OBSERVE': None, 'T': table, 'D0': 40}
    exec(compile(code, str(executor_path), 'exec'), ns)
    return ns


def cases(ns, sites):
    out = []
    for i, (q, op, r) in enumerate(sites):
        branches = ('z', 'p') if op == 'CD' else ('-',)
        for br in branches:
            if op == 'CI' or (op == 'CD' and br == 'p'):
                q2 = ns['inc'](q)
            elif op == 'CD':
                q2 = ns['inc'](ns['strip']('0', 1, q))
            elif op == 'CC':
                q2 = ns['strip']('1', r, q)
            elif op == 'CB':
                q2 = ns['inc'](ns['strip']('0', r, q))
            else:
                q2 = ''
            effect = () if op not in ('CI', 'CD') else ((('inc' if op == 'CI' else 'dec0' if br == 'z' else 'dec'), r),)
            if q2 is None:
                expect = ns['canon']([('b', 1)], [('r', 0, 1, 41), ('b', 1), ('box', ('plain',) + effect)])
            else:
                expect = ns['canon']([('b', 1)], ns['tape_R'](q2, 0, effect))
            out.append((i, q, op, r, br, expect))
    return out


def check(ns, case, fuel=1000):
    i, q, op, r, br, expect = case
    try:
        result = ns['run']('96', [('b', 1)], ns['tape_R'](q, 0, ()), br, expect, fuel=fuel)
    except (ns['Fail'], KeyError):
        return False
    return result[0] == ('halt' if op == 'CH' else 'ok')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--search', action='store_true')
    ap.add_argument('--all-noncore', action='store_true')
    ap.add_argument('--sources', type=Path, default=HERE / 'sources')
    ap.add_argument('--baseline', type=Path)
    ap.add_argument('--program', type=Path)
    ap.add_argument('--upstream-executor', type=Path)
    ap.add_argument('--output', type=Path, default=HERE / 'context_search.json')
    args = ap.parse_args()
    args.baseline = args.baseline or args.sources / 'zfc_254.tm'
    args.program = args.program or args.sources / 'Prog254.v'
    args.upstream_executor = args.upstream_executor or args.sources / 'symexec.py'
    # Old labels make the unchanged published box summaries applicable.
    rows, _, _, _, sha = parse_table(args.baseline)
    assert sha == 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
    table = {(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in rows.items()}
    table = {k: v for k, v in table.items() if k[0] != '8'}
    table.update({('3', 0): (0, 'L', '48'), ('5', 0): (1, 'R', '97'),
                  ('5', 1): (1, 'R', '64'), ('49', 1): (0, 'R', '5')})
    ns = executor(table, args.upstream_executor)
    sites = program_sites(args.program)
    allcases = cases(ns, sites)
    seen = defaultdict(set)
    current = [None]
    def observe(q, form, L, R, branch, expect):
        seen[q].add(current[0])
    ns['OBSERVE'] = observe
    for i, case in enumerate(allcases):
        current[0] = i
        assert check(ns, case), ('baseline failed', i)
    ns['OBSERVE'] = None
    print('all', len(allcases), 'baseline instruction cases passed', flush=True)
    report = {'instruction_sites': len(sites), 'branch_cases': len(allcases),
              'baseline_runtime_cases_passed': len(allcases),
              'symbolic_states_seen_including_terminal': len(seen),
              'states_not_stepped_because_hidden_inside_register_box_oracles': sorted(set(q for q, b in table) - set(seen), key=int),
              'state_redirection_candidates_checked': 0, 'all_site_survivors': [],
              'scope': 'Experimental affine-executor candidate search; not kernel verified.'}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    if not args.search:
        return
    core = {0,1,2,3,5,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,84,85,95,97,109,112,131}
    # Exclude dispatcher, because the oracle's stopping convention uses 96.
    eligible = [q for q in sorted(seen, key=int) if (q, 0) in table and int(q) not in core | {96}
                and (args.all_noncore or (table[q,0][:2] == (0,'R') and table[q,1][:2] == (1,'R')))]
    destinations = sorted(set(q for q, b in table), key=int)
    start = time.monotonic()
    for qi, q in enumerate(eligible):
        witnesses = sorted(seen[q], key=lambda j: len(allcases[j][1]))
        for p in destinations:
            if p == q:
                continue
            changed = {k: (w,d,p if t == q else t) for k,(w,d,t) in table.items() if k[0] != q}
            ns['T'] = changed
            report['state_redirection_candidates_checked'] += 1
            # Every runtime path affected by q is among these baseline cases.
            if all(check(ns, allcases[j]) for j in witnesses):
                # A surviving pair is now checked against every instruction site.
                if all(check(ns, case) for case in allcases):
                    report['all_site_survivors'].append({'deleted_old_state': q, 'redirected_to_old_state': p})
                    print('SURVIVOR', q, p, flush=True)
        if (qi+1) % 10 == 0:
            report['elapsed_seconds'] = round(time.monotonic()-start, 3)
            args.output.write_text(json.dumps(report, indent=2) + '\n')
            print('deleted-state candidates done', qi+1, '/', len(eligible), 'seconds', round(time.monotonic()-start), flush=True)
    report['elapsed_seconds'] = round(time.monotonic()-start, 3)
    report['eligible_deleted_states'] = eligible
    report['scope'] += ' Only direct state redirections of ' + ('all observed noncore states' if args.all_noncore else 'selected right-reading decoder states') + ' were searched.'
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()

