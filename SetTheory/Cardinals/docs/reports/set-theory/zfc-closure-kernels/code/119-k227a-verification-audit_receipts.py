#!/usr/bin/env python3
"""Audit receipt binding, complete case census, and source-frame composition.

This does not rederive the stored symbolic instruction proofs. The full
runtime driver does that. A successful audit is never a fresh runtime PASS.
"""
from pathlib import Path
import argparse
import hashlib
import json
from verify_runtime import parse_table, source_facts, require


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def increment(pc):
    if not pc:
        return '', 1
    bits = list(pc)
    for i in range(len(bits)-1, -1, -1):
        if bits[i] == '0':
            bits[i] = '1'
            return ''.join(bits), 0
        bits[i] = '0'
    return ''.join(bits), 1


def strip(pc, symbol, count):
    for i in range(len(pc)-1, -1, -1):
        if pc[i] == symbol:
            count -= 1
            if count == 0:
                return pc[:i]
    return ''


def audit(root, n):
    tablep = root/'machines'/f'k{n}_inherited.tm'
    sitesp = root/'source'/f'k{n}_sites_logical.json'
    receiptp = root/'evidence'/f'runtime{n}.json'
    table = parse_table(tablep)
    sites = json.loads(sitesp.read_text())
    facts = source_facts(sites)
    r = json.loads(receiptp.read_text())
    require(r['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Stored runtime is not complete')
    for key, path in [('table_sha256', tablep), ('sites_sha256', sitesp),
                      ('driver_sha256', root/'verification/verify_runtime.py'),
                      ('engine_sha256', root/'verification/engine/symbolic_runtime.py'),
                      ('helper_sha256', root/'verification/engine/independent_runtime.py')]:
        require(r[key] == sha(path), 'Runtime receipt input mismatch: '+key)
    cp = receiptp.with_name(r['cases_file'])
    require(cp.parent == receiptp.parent and cp.is_file(), 'Invalid case-data path')
    require(sha(cp) == r['cases_sha256'], 'Case-data hash mismatch')
    cases = json.loads(cp.read_text())
    expected = [(i, p) for i, (_, op, _) in enumerate(sites)
                for p in ((False, True) if op == 'CD' else (False,))]
    require([(c['site_index'], c['positive']) for c in cases] == expected, 'Incomplete case sequence')
    require(len(cases) == r['cases'] == r['expected_cases'] == facts['guarded_cases'] == 6656,
            'Wrong guarded-case census')
    require(facts == r['source'] and len(table) == r['rows'] == 2*n, 'Wrong input facts')
    for c in cases:
        require(len(c['duration']) == len(c['motion']) == 13, 'Bad affine vector')
        require(all(type(x) is int and x >= 0 for x in c['duration']) and c['duration'][0] > 0,
                'No positive duration')
        require(0 < c['symbolic_steps'] <= 4000 and sum(c['kinds'].values()) == c['symbolic_steps'],
                'Wrong proof construction census')
    require(sum(c['symbolic_steps'] for c in cases) == r['symbolic_steps'], 'Aggregate proof count')
    require(min(c['duration'][0] for c in cases) == r['minimum_actual_steps'], 'Minimum duration')
    require(max(c['symbolic_steps'] for c in cases) == r['maximum_symbolic_steps'], 'Maximum proof count')
    used = {tuple(row) for row in r['directly_used_rows']}
    for block in r['list_induction_blocks']:
        for event in block['trace']:
            if event[0] != 'list':
                used.add(tuple(event[1][:2]))
    require(used == set(table), 'Stored row coverage incomplete')
    # Exact finite successor-to-next-leaf composition; no optimizer imported.
    padded = {p+'0'*(64-len(p)): (i, p) for i, (p, _, _) in enumerate(sites)}
    require(len(padded) == len(sites), 'Ambiguous padded leaves')
    successors = 0
    for c in cases:
        pc, op, arg = sites[c['site_index']]
        overflow = 0
        if op == 'CH':
            continue
        if op == 'CI' or (op == 'CD' and c['positive']):
            nxt, overflow = increment(pc)
        elif op in ('CD', 'CB'):
            nxt, overflow = increment(strip(pc, '0', arg if op == 'CB' else 1))
        else:
            nxt = strip(pc, '1', arg)
        word = nxt+'0'*(64-len(nxt))
        require(word in padded, 'Successor is not the padded next source leaf')
        require(c['motion'] == [-overflow]+[0]*12, 'Wrong recorded nonhalt motion')
        successors += 1
    boot = json.loads((root/'evidence'/f'bootstrap{n}.json').read_text())
    require(boot['table_sha256'] == sha(tablep) and boot['steps'] == 409835, 'Startup pin')
    require(sites[0] == ['000', 'CD', 8], 'Wrong first source leaf')
    physical = [0, 0, 0, 3, 0, 0, 3, 0, 0]
    want, pos = {-6, 176}, 177
    for value in physical+[1]*167:
        pos += 1
        want.update(range(pos, pos+value+1))
        pos += value+1
    require(boot['one_cells'] == sorted(want) and boot['final_state'] == 96
            and boot['final_head'] == -5 and boot['gap'] == 181, 'Wrong initial complete frame')
    return dict(status='PASS_STORED_RUNTIME_BINDING_AND_COMPOSITION_AUDIT', states=n,
                cases=len(cases), nonhalt_successors_checked=successors,
                exact_startup_frame=True, extra_initial_gap=117,
                table_sha256=sha(tablep), source_sha256=sha(sitesp),
                scope='Stored proof receipt audit and exact finite interfaces, not a fresh universal proof replay.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    out = [audit(a.root, n) for n in (228, 227)]
    a.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
