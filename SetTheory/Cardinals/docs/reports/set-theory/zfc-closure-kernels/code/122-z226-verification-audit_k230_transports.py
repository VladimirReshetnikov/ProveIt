#!/usr/bin/env python3
"""Independent finite verification of K230 source normalization and fold79.

No imports from the builders, inherited checkers, or candidate generators.
The source check reconstructs path arithmetic directly from RM.v and verifies
that the four macros have no external entry at any non-entry instruction.
The fold check verifies the supplied invariant and every literal trace over
an open tape.  It does not claim an all-tape theorem for fold140.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    starts = []
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = int(q), int(b), int(w), int(z)
            require((q, b) not in rows and b in (0, 1) and w in (0, 1)
                    and d in ('L', 'R'), 'Malformed table row')
            rows[q, b] = w, (-1 if d == 'L' else 1), z
    states = {q for q, b in rows}
    require(starts == [0], 'Expected unique start 0')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    terminal = {z for w, d, z in rows.values()} - states
    require(len(terminal) == 1, 'Terminal state census')
    return rows, terminal.pop()


def read_sites(path):
    raw = json.loads(path.read_text())
    names = dict(EInc='CI', EDecnz='CD', EBreak='CB', EContinue='CC', EHalt='CH')
    if len(raw[0]) == 2:
        sites = {}
        for p, text in raw:
            words = text.split()
            require(p not in sites, 'Duplicate source path')
            sites[p] = names[words[0]], int(words[1]) if len(words) > 1 else None
    else:
        sites = {p: (op, arg) for p, op, arg in raw}
        require(len(raw) == len(sites), 'Duplicate source path')
    prefixes = {p[:i] for p in sites for i in range(len(p))}
    require(not set(sites) & prefixes, 'Source paths not prefix-free')
    require(all(p + b in sites or p + b in prefixes for p in prefixes for b in '01'),
            'Source tree is not full')
    require(all(p and set(p) <= {'0', '1'} for p in sites), 'Invalid source path')
    return sites


def increment(bits):
    out = list(bits)
    for i in range(len(out) - 1, -1, -1):
        if out[i] == '0':
            out[i] = '1'
            break
        out[i] = '0'
    return ''.join(out)


def strip(bits, value, count):
    for i in range(len(bits), -1, -1):
        if count == 0:
            return bits[:i]
        if i:
            count -= bits[i - 1] == value
    return ''


def locate(sites, bits):
    path = ''
    for i in range(max(map(len, sites))):
        path += bits[i] if i < len(bits) else '0'
        if path in sites:
            require('1' not in bits[i + 1:], 'Noncanonical successor residual')
            return path
    raise ValueError('No source instruction reached')


def successors(sites, path):
    op, arg = sites[path]
    if op == 'CH':
        return ()
    if op == 'CI':
        bits = (increment(path),)
    elif op == 'CD':
        bits = (increment(path), increment(strip(path, '0', 1)))
    elif op == 'CB':
        bits = (increment(strip(path, '0', arg)),)
    elif op == 'CC':
        bits = (strip(path, '1', arg),)
    else:
        raise ValueError('Unknown source opcode')
    return tuple(locate(sites, b) for b in bits)


def source_audit(pinned, normalized, certificate):
    old = read_sites(pinned)
    new = read_sites(normalized)
    cert = json.loads(certificate.read_text())
    require(digest(pinned) == cert['input_source_sha256']
            and digest(normalized) == cert['output_source_sha256'],
            'Source certificate hash mismatch')
    roots = cert['occurrence_paths']
    require(len(roots) == 4 and len(set(roots)) == 4, 'Four distinct macro roots')
    require(not any(a.startswith(b) for a in roots for b in roots if a != b),
            'Overlapping macro occurrences')
    old_local = {'00': ('CD', 6), '010': ('CI', 5), '011': ('CC', 2), '1': ('CI', 5)}
    new_local = {'0': ('CI', 5), '10': ('CD', 6), '11': ('CC', 2)}
    old_inner = {a + suffix for a in roots for suffix in old_local}
    new_inner = {a + suffix for a in roots for suffix in new_local}
    require({p: op for p, op in old.items() if p not in old_inner}
            == {p: op for p, op in new.items() if p not in new_inner},
            'Outside instruction context changed')
    for a in roots:
        require({p[len(a):]: op for p, op in old.items() if p.startswith(a)} == old_local,
                'Old local subtree differs')
        require({p[len(a):]: op for p, op in new.items() if p.startswith(a)} == new_local,
                'New local subtree differs')
    old_entries = {a + '00': a + '0' for a in roots}
    new_entries = set(old_entries.values())
    mapping = {p: p for p in old if p not in old_inner}
    mapping.update(old_entries)
    incoming = Counter()
    outside_edges = 0
    for p in old:
        if p in old_inner:
            continue
        osucc, nsucc = successors(old, p), successors(new, p)
        require(len(osucc) == len(nsucc), 'Outside opcode branch count')
        for x, y in zip(osucc, nsucc):
            require(x in mapping, 'Outside edge enters non-entry old macro leaf')
            require(y not in new_inner or y in new_entries,
                    'Outside edge enters non-entry new macro leaf')
            require(mapping[x] == y, 'Outside edge not preserved')
            outside_edges += 1
            if x in old_entries:
                incoming[x] += 1
    local_rows = []
    for a in roots:
        d, i, c, post = (a + x for x in ('00', '010', '011', '1'))
        ni, nd, nc = (a + x for x in ('0', '10', '11'))
        require(successors(old, d) == (i, post), 'Old decrement successors')
        require(successors(old, i) == (c,), 'Old increment successor')
        require(successors(old, c) == (d,), 'Old continue successor')
        require(successors(new, ni) == (nd,), 'New increment successor')
        old_exit, = successors(old, post)
        require(old_exit in mapping, 'Macro old exit enters an internal leaf')
        new_exit = mapping[old_exit]
        require(successors(new, nd) == (nc, new_exit), 'New decrement successors')
        require(successors(new, nc) == (ni,), 'New continue successor')
        local_rows.append(dict(root=a, old_entry=d, new_entry=ni,
                               old_exit=old_exit, new_exit=new_exit,
                               external_incoming_edges=incoming[d]))
    require(mapping[locate(old, '')] == locate(new, ''), 'Root initial entry mismatch')
    return dict(status='EXACT_CFG_CONTEXT_AUDIT_PASS', old_leaves=len(old),
                new_leaves=len(new), unchanged_outside_leaves=len(mapping)-len(roots),
                checked_outside_edges=outside_edges, macro_occurrences=local_rows,
                external_edges_to_proper_internal_leaves=0,
                local_math='Both normal-entry macros terminate normally in 3*b+2 primitive '
                           'steps with R5=a+b+1,R6=0, other registers unchanged; '
                           'induction on natural b.',
                scope='Whole root-start source for every register map. Does not assert '
                      'equivalence for arbitrary instruction pointers inside a macro.')


def source_cfg_isomorphism(old_path, new_path):
    """Exact all-register instruction graph comparison, with paths renamed.

    Reassociation preserves the left-to-right instruction sequence.  Use
    that finite sequence to map source sites, then independently compare
    every opcode, operand and guarded outgoing edge.  No assumption about
    closedness or admissibility of the proposed rotation is needed.
    """
    old, new = read_sites(old_path), read_sites(new_path)
    opaths, npaths = sorted(old), sorted(new)
    require(len(opaths) == len(npaths), 'Source reassociation changed leaf count')
    mapping = dict(zip(opaths, npaths))
    edge_count = 0
    moved = 0
    for p, q in mapping.items():
        require(old[p] == new[q], 'Source reassociation changed instruction or operand')
        osucc, nsucc = successors(old, p), successors(new, q)
        require(tuple(mapping[x] for x in osucc) == nsucc,
                'Source reassociation changed a guarded control-flow edge')
        edge_count += len(osucc)
        moved += p != q
    require(mapping[locate(old, '')] == locate(new, ''), 'Reassociation root entry mismatch')
    return dict(status='EXACT_ALL_REGISTER_SOURCE_CFG_ISOMORPHISM_PASS',
                input_source_sha256=digest(old_path), output_source_sha256=digest(new_path),
                leaf_instructions=len(opaths), guarded_edges=edge_count,
                relocated_leaf_paths=moved,
                maximum_zero_run=max(len(z) for p in npaths for z in p.split('1')),
                scope='All register maps and every corresponding canonical instruction '
                      'site. Same opcode, operand, zero/positive guarded successor and '
                      'halt leaf under the checked path bijection. Exact source step '
                      'correspondence; arbitrary noncanonical IP suffixes are not claimed.')


def verify_block(old, new, q, b, guard, trace, phi):
    require(guard.get(0) == b and trace, 'Missing read guard or zero block')
    tape = dict(guard)
    state, head = phi(q), 0
    touched = set()
    for index, literal in enumerate(trace):
        require((state, head) == tuple(literal[:2]), 'Trace state/head mismatch')
        require(head in tape, 'Trace depends on an unconstrained input bit')
        read = tape[head]
        require((state, read) in new, 'Interior halt or unknown state')
        w, move, dest = new[state, read]
        require(literal == [state, head, read, w, move, dest], 'Literal transition mismatch')
        tape[head] = w
        touched.add(head)
        state, head = dest, head + move
    w, move, dest = old[q, b]
    require((state, head) == (phi(dest), move), 'Wrong block endpoint')
    require(all(tape[p] == (w if p == 0 else guard[p]) for p in touched | {0}),
            'Block does not preserve entire old-step tape')


def fold79_audit(old_path, new_path, cert_path):
    old, halt = read_table(old_path)
    new, new_halt = read_table(new_path)
    cert = json.loads(cert_path.read_text())
    require(halt == new_halt == 254, 'Fold input halt names')
    require(cert['old_sha256'] == digest(old_path) and cert['new_sha256'] == digest(new_path),
            'Fold artifact hash mismatch')
    states = {q for q, b in old}
    facts = {int(q): {int(p): v for p, v in f.items()} for q, f in cert['invariant'].items()}
    require(set(facts) == states | {halt} and facts[0] == {}, 'Invariant census/start')
    checks = 0
    for (q, b), (w, move, dest) in old.items():
        require(0 not in facts[q] or facts[q][0] == b, 'This checker expects both row guards live')
        known = dict(facts[q])
        known[0] = w
        require(all(known.get(p + move) == v for p, v in facts[dest].items()),
                'Inductive invariant preservation failed')
        checks += 1
    phi = lambda q: 63 if q == 79 else q
    expected = {(q, b): (w, move, phi(z)) for (q, b), (w, move, z) in old.items() if q != 79}
    expected[63, 0] = 0, -1, 123
    expected[63, 1] = 1, -1, 30
    require(expected == new, 'Fold literal table construction differs')
    seen = set()
    hist = Counter()
    exceptional = []
    for row in cert['row_proofs']:
        q, b = row['row']
        require((q, b) in old and (q, b) not in seen, 'Repeated/unrecognized proof row')
        seen.add((q, b))
        require(len(row['branches']) == 1, 'Checker expects branch-free guard traces')
        branch, = row['branches']
        guard = {int(p): v for p, v in branch['guard'].items()}
        require(guard == {**facts[q], 0: b}, 'Undischarged branch guard')
        trace = branch['trace']
        require(len(trace) == branch['steps'], 'Block length mismatch')
        verify_block(old, new, q, b, guard, trace, phi)
        hist[len(trace)] += 1
        if len(trace) > 1:
            exceptional.append(dict(old_row=[q, b], steps=len(trace),
                                    path=[t[0] for t in trace] + [phi(old[q, b][2])]))
    require(seen == set(old), 'Incomplete row proof coverage')
    return dict(status='INDEPENDENT_ALL_INITIAL_TAPES_FOLD79_PASS',
                invariant_preservation_rows=checks, checked_open_tape_blocks=len(seen),
                block_lengths=dict(sorted(hist.items())), exceptional_blocks=exceptional,
                scope='Every initial binary tape at state0, and every integer initial '
                      'head position; invariant proved by induction. Positive blocks '
                      'preserve state image, head and entire tape, so halting is equivalent.')


def fold140_local_audit(old_path, new_path, certificate):
    old, h1 = read_table(old_path)
    new, h2 = read_table(new_path)
    require(h1 == h2, 'Fold140 terminal mismatch')
    phi = lambda q: 71 if q == 140 else q
    expected = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in old.items() if q != 140}
    expected[71, 0] = 0, -1, 91
    expected[80, 1] = 1, -1, 138
    require(expected == new, 'Fold140 literal table mismatch')
    cert = json.loads(certificate.read_text())
    require({tuple(x['row']) for x in cert['cases']} == {(71, 0), (140, 0), (140, 1), (80, 1)},
            'Fold140 exceptional case census')
    for case in cert['cases']:
        q, b = case['row']
        guard = {int(p): v for p, v in case['guard'].items()}
        guard[0] = b
        require(case['steps'] == len(case['trace']), 'Fold140 length mismatch')
        verify_block(old, new, q, b, guard, case['trace'], phi)
    return dict(status='FOUR_CONDITIONAL_OPEN_TAPE_BLOCKS_PASS',
                additional_condition='At source state140 on read1, right neighbor is1.',
                scope='Local explanation only. No all-initial-tape or blank calibration '
                      'claim follows from these guarded blocks alone; direct universal '
                      'instruction simulation plus exact startup supplies blank calibration.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--upstream-root', type=Path,
                        help='Pinned K230 repository root (containing machine/).')
    parser.add_argument('--machine-root', type=Path,
                        help='Directory containing the named candidate .tm and fold JSON files.')
    parser.add_argument('--source-root', type=Path,
                        help='Directory containing sites_logical.json and source_loop_certificate.json.')
    parser.add_argument('--equivalent-source', type=Path, action='append', default=[],
                        help='Further reassociated source to compare directly with the loop source; repeatable.')
    parser.add_argument('--source-only', action='store_true',
                        help='Check source normalization and reassociation only; no candidate-table or fold files needed.')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = args.root
    pinned = args.upstream_root or root / 'baseline/k230-rocq-3142e4dd980f0be12f4abb636c4ae2528afc17eb'
    search = args.machine_root or root / 'search_machine/k230'
    source = args.source_root or root / 'search_rotation/k_loop'
    require(digest(pinned/'machine/k230.tm') == 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8', 'Pinned table changed')
    require(digest(pinned/'machine/sites230.json') == '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487', 'Pinned source changed')
    output = dict(status='INDEPENDENT_FINITE_AUDIT_PASS',
                  source=source_audit(pinned/'machine/sites230.json', source/'sites_logical.json',
                                      source/'source_loop_certificate.json'),
                  further_source_cfg_isomorphisms=[source_cfg_isomorphism(source/'sites_logical.json', path)
                                                   for path in args.equivalent_source],
                  checker_sha256=digest(Path(__file__)))
    if not args.source_only:
        original, terminal = read_table(pinned/'machine/k230.tm')
        old, ht = read_table(search/'k230.tm')
        require(terminal == 230 and ht == 254, 'Expected harmless halt-name adapter')
        adapted = {(q, b): (w, d, 254 if z == 230 else z) for (q, b), (w, d, z) in original.items()}
        require(old == adapted, 'Search baseline differs beyond halt name')
        loop, _ = read_table(search/'k230_looprotated.tm')
        adapted[121, 0] = 0, 1, 63
        adapted[121, 1] = 1, 1, 13
        require(loop == adapted, 'Loop table changed more than K121')
        output['fold79'] = fold79_audit(search/'k230_looprotated.tm', search/'k229_fold79.tm', search/'fold79.json')
        output['fold140'] = fold140_local_audit(search/'k230.tm', search/'k229_fold140.tm', search/'fold140_conditional.json')
    destination = args.output or root/'independent_k230_transport_audit.json'
    destination.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
