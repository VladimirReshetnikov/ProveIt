#!/usr/bin/env python3
"""Role-based replay of the same 211-to-172 reduction on each U209 archive."""
from pathlib import Path
import argparse, json, sys, hashlib
from check_local import require, read, census, incoming, execute, encode

def roles(old):
    rows = incoming(old, 211)
    require(len(rows) == 2 and rows[0][0] == rows[1][0], 'Unique folded helper')
    entry = rows[0][0]
    require(rows == [[entry, 0, 0, -1], [entry, 1, 1, 1]], 'Helper semantics')
    entrants = incoming(old, entry)
    zero = [row for row in entrants if row[2:] == [0, 1]]
    ones = [row for row in entrants if row[2:] == [1, 1]]
    require(len(zero) == 1 and len(ones) + 1 == len(entrants), 'Entry tag partition')
    helper = zero[0][0]
    require(zero[0][1] == 0, 'Zero selector read')
    require(old[helper, 0] == (0, 1, entry), 'Helper zero branch')
    ins_helper = incoming(old, helper)
    require(ins_helper and all(row[2:] == [1, 1] for row in ins_helper),
            'Third predecessor tag')
    follower = old[helper, 1][2]
    require(old[helper, 1][:2] == (1, 1), 'Helper one branch')
    require(old[follower, 0] == (0, 1, 157), 'Follower zero branch')
    require(incoming(old, 172) == [[116, 0, 0, 1]], 'Keep-state entrance')
    ins116 = incoming(old, 116)
    require(ins116 and all(row[2:] == [1, 1] for row in ins116),
            'Second predecessor keep-state tag')
    require(0 not in (172, 211, 116, entry, helper), 'Initial guard bypass')
    return {'entry': entry, 'helper': helper, 'follower': follower,
            'entry_inventory': entrants, 'helper_inventory': ins_helper,
            'keep_predecessor_inventory': ins116}

def construct(old, helper):
    new = {(q, b): (w, d, 172 if z == 211 else z)
           for (q, b), (w, d, z) in old.items() if q != 211}
    new[172, 0] = (0, -1, helper)
    return new

def verify(old, new):
    info = roles(old)
    census(old, 209, 254)
    census(new, 208, 254)
    require(set(old) - set(new) == {(211, 0), (211, 1)} and
            not set(new) - set(old), 'Deleted state')
    rho = lambda q: 172 if q == 211 else q
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if q not in (172, 211):
            require(new[rho(q), b] == (w, d, rho(z)), 'Ordinary quotient')
            ordinary += 1
    cases = []
    for q, cells, steps in [(172, {-2: 1, -1: 0, 0: 0}, 7),
                            (211, {-1: 1, 0: 0}, 3),
                            (172, {0: 1}, 1), (211, {0: 1}, 1)]:
        end_old, trace_old = execute(old, q, cells, 1)
        end_new, trace_new = execute(new, rho(q), cells, steps)
        require(end_new == (rho(end_old[0]), end_old[1], end_old[2]), 'Endpoint')
        require(end_old[2] == cells, 'Tape unchanged')
        cases.append({'old_state': q, 'input': cells, 'steps': steps,
                      'old_trace': trace_old, 'new_trace': trace_new})
    require(ordinary == 414, 'Ordinary row count')
    return {'status': 'PORTABLE_ALL_TAPE_SIMULATION_PASS', 'roles': info,
            'old_states': 209, 'new_states': 208, 'ordinary_rows': ordinary,
            'cases': cases, 'min_steps': 1, 'max_steps': 7}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('table', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--candidate-dir', type=Path)
    p.add_argument('--sites', type=Path)
    a = p.parse_args()
    old = read(a.table, 209)
    info = roles(old)
    new = construct(old, info['helper'])
    result = verify(old, new)
    mapping = {q: i for i, q in enumerate(sorted({q for q, b in new}))}
    mapping[254] = 208
    dense = {(mapping[q], b): (w, d, mapping[z])
             for (q, b), (w, d, z) in new.items()}
    census(dense, 208, 208)
    sha = lambda data: hashlib.sha256(data).hexdigest()
    result['input'] = str(a.table)
    result['sha256'] = {'parent_native': sha(a.table.read_bytes()),
                        'candidate_native': sha(encode(new)),
                        'candidate_dense': sha(encode(dense))}
    if a.candidate_dir:
        a.candidate_dir.mkdir(parents=True, exist_ok=True)
        (a.candidate_dir / 'u208.native.tm').write_bytes(encode(new))
        (a.candidate_dir / 'u208.tm').write_bytes(encode(dense))
        (a.candidate_dir / 'u209.native.tm').write_bytes(a.table.read_bytes())
        sites = a.sites or a.table.parent / 'sites.json'
        (a.candidate_dir / 'sites.json').write_bytes(sites.read_bytes())
        (a.candidate_dir / 'state_map.json').write_text(json.dumps({
            'native_to_dense': mapping,
            'dense_to_native': {v: k for k, v in mapping.items()}}, indent=2) + '\n')
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'cases'}, indent=2))

if __name__ == '__main__':
    main()
