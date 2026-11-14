#!/usr/bin/env python3
"""Deterministically reconstruct and verify PA195; Python 3 standard library.

Run without -O. The default checks source binding, all incoming-history and
local quotient obligations, both complete symbolic runtime contract lists,
and the exact blank startup. --quick omits only the two runtime contract lists.
--export regenerates derived JSON certificates and the unfolded 202-state table.
This executable certificate is not a Lean/Rocq kernel theorem.
"""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import json
import re
import sys

P = Path(__file__).resolve().parent
sys.path.insert(0, str(P / 'vendor'))
import compiler as c
INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)
c.MACROS[(INC, INC)] = 99
c.MACROS[((INC, INC), (INC, INC))] = 190
EXPECTED_SHA = '5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def table(path):
    out = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        need(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'nonbinary row')
        need((q, b) not in out, 'duplicate row')
        out[q, b] = w, d == 'R', n
    return out


def table_bytes(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items())).encode()


NAMES = {'node49': 'push', 'node55': 'copyD', 'node58': 'copyH',
         'node70': 'copyA', 'node65': 'cons', 'node72': 'readH',
         'node75': 'readDCons', 'node142': 'copyGuard',
         'node150': 'compareGuard', INC: 'incT', BREAK: 'close'}


def word(t):
    if t == 'node60':
        return ['incT'] * 2
    if t == 'node61':
        return ['incT'] * 4
    if c.isnode(t):
        return word(t[0]) + word(t[1])
    return [NAMES[t]]


def original_blocks():
    text = (P / 'vendor/reference/PA196/Source/AXProgram.lean').read_text()
    return [(op, int(a), int(b)) for op, a, b in
            re.findall(r'\(\.(\w+), (\d+), (\d+)\)', text.split('def program')[0])]


def emitter(t):
    """A free-algebra computation, not numeric formula-code sampling."""
    ww = word(t)
    old = [op for op, a, b in original_blocks()]
    expected = old[:121] + ['copyA', 'copyA', 'copyA', 'cons', 'incT', 'incT', 'cons'] + old[138:]
    need(ww == expected, 'diagonal emitter word differs')
    ZERO = ('zero',)
    succ = lambda x: ('succ', x)
    ONE = succ(ZERO)
    add = lambda x, y: ('add', x, y)
    I = lambda a, b: ('im', a, b)
    M = lambda a, b: succ(I(a, b))
    U = lambda a, b: succ(succ(I(b, a)))
    E = lambda a, b: succ(succ(succ(I(a, b))))
    N = lambda a: I(a, ONE)
    And = lambda a, b: N(I(a, N(b)))
    Ex = lambda a, b: N(U(a, N(b)))
    oldt, A, d, h, Y, X = [('atom', z) for z in ['t', 'a', 'd', 'h', 'y', 'x']]
    T, D, H, stack, fields = oldt, d, h, [], [Y, X]
    for op in ww[:-3]:
        if op == 'push':
            stack.append(T); T = ZERO
        elif op in ('copyD', 'copyH', 'copyA'):
            stack.append(T); T = {'copyD': D, 'copyH': H, 'copyA': A}[op]
        elif op == 'cons':
            T = I(stack.pop(), T)
        elif op == 'incT':
            T = succ(T)
        elif op == 'readH':
            H = add(H, fields.pop(0))
        elif op == 'readDCons':
            D = add(D, fields.pop(0)); T = I(T, D)
        else:
            raise ValueError(op)
    need(not fields, 'argument reads')
    heads = [I(Ex(D, U(D, H)), H), I(U(D, U(A, H)), U(A, U(D, H))),
             I(M(H, D), I(E(H, A), M(A, D))),
             I(E(H, D), I(M(A, H), M(A, D))), Ex(D, E(H, D)),
             I(U(D, A), I(U(D, I(A, H)), U(D, H)))]
    rho = I(I(I(H, d), D), I(I(D, H), I(A, H)))
    gamma = I(A, U(A, A))
    V = I(M(H, D), U(A, M(H, D)))
    B = I(A, M(A, D))
    S = U(D, And(I(M(H, D), B), I(M(A, D), A)))
    Q = U(A, I(S, N(B)))
    need(stack == [oldt, U(d, h), rho] + heads, 'emitted complete stack')
    need(T == N(I(gamma, I(V, Q))), 'emitted gate')
    need(ww[-3:] == ['copyGuard', 'compareGuard', 'close'], 'guard and cleanup')
    return {'macro_tokens': len(ww), 'complete_stack_free_algebra_identity': True,
            'complete_top_free_algebra_identity': True, 'head_parameters_unchanged': True}


def interval_cfg(sites):
    """Independent CFG resolver using subtree intervals and ancestor walking."""
    bypath = {p: i for i, (p, op, arg) in enumerate(sites)}
    need(len(bypath) == len(sites), 'duplicate source path')
    spans = {}
    def visit(p):
        if p in bypath:
            result = bypath[p], bypath[p] + 1
        else:
            a, b = visit(p + (0,)), visit(p + (1,))
            need(a[1] == b[0], 'noncontiguous subtree')
            result = a[0], b[1]
        spans[p] = result
        return result
    need(visit(()) == (0, len(sites)), 'full binary source tree')
    def unwind(p, edge, count):
        while p:
            last, p = p[-1], p[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return (spans[p][1] % len(sites)) if edge == 0 else spans[p][0]
        return 0
    cfg = []
    for i, (p, op, arg) in enumerate(sites):
        nxt = (i + 1) % len(sites)
        if op == 'inc':
            code = ('inc', arg, nxt)
        elif op == 'dec':
            code = ('dec', arg, unwind(p, 0, 1), nxt)
        elif op == 'continueTo':
            code = ('jump', unwind(p, 1, arg))
        elif op == 'breakTo':
            code = ('jump', unwind(p, 0, arg))
        else:
            need(op == 'halt', 'unknown source opcode'); code = ('halt',)
        cfg.append(code)
    return cfg


def source_binding(t, sites, cfg):
    need(cfg == interval_cfg(sites), 'independent CFG resolver disagreement')
    oldt = c.read_grammar(P / 'vendor/reference/diagonal196/grammar.json')
    oldsites, oldcfg, _ = c.source(oldt)
    need(oldcfg == interval_cfg(oldsites), 'reference CFG resolver disagreement')
    need([s[1:] for s in sites] == [s[1:] for s in oldsites], 'ordered instruction word changed')
    need(cfg == oldcfg, 'ordinal source CFG changed')
    need(word(t) == word(oldt), 'macro token word changed')
    return {'primitive_sites': len(sites), 'independent_cfg_resolvers': 2,
            'ordered_primitive_word_equal_to_diagonal196': True,
            'all_ordinal_successors_equal_to_diagonal196': True,
            'same_seed_site': 25, 'seed_path': ''.join(map(str, sites[25][0]))}


def quotient(raw, folds):
    aliases = {a: b for a, b, actions in folds}
    replacement = {b: actions for a, b, actions in folds}
    flat = [q for a, b, actions in folds for q in (a, b)]
    need(len(set(flat)) == len(flat), 'overlapping folds')
    need(74 not in flat and 254 not in flat, 'start or halt folded')
    out = {}
    for (q, bit), act in raw.items():
        if q in aliases:
            continue
        w, d, n = replacement[q][bit] if q in replacement else act
        out[q, bit] = w, bool(d), aliases.get(n, n)
    return out, aliases


def quotient_certificate(raw, folded, folds, aliases):
    """Exhaustive two-cell checks valid for every outside-tape extension."""
    history, incoming = {}, []
    for a, b, acts in folds:
        history[a] = 0; history[b] = 1
    for (q, bit), (w, d, n) in raw.items():
        if n in history:
            need(d and w == history[n], 'invalid incoming-history premise')
            incoming.append([q, bit, w, int(d), n, history[n]])
    need(set(history) <= {r[4] for r in incoming}, 'unentered fold state')
    for (q, bit), (w, d, n) in raw.items():
        if q not in history:
            need(folded[q, bit] == (w, d, aliases.get(n, n)), 'unmodified row does not commute')
    traces = []
    for q, p in sorted(history.items()):
        for bit in (0, 1):
            w, d, n = raw[q, bit]
            expected = {-1: p, 0: w}
            pos, now, tape = 0, aliases.get(q, q), {-1: p, 0: bit}
            target, target_pos = aliases.get(n, n), (1 if d else -1)
            steps = []
            for tick in range(64):
                if tick and (now, pos, tape) == (target, target_pos, expected):
                    break
                need(pos in (-1, 0), 'fold detour reads an unrecorded tape cell')
                read = tape[pos]
                ww, dd, nn = folded[now, read]
                steps.append([now, pos, read, ww, 'R' if dd else 'L', nn])
                tape[pos] = ww; pos += 1 if dd else -1; now = nn
            else:
                raise ValueError('fold local simulation did not finish')
            traces.append({'raw_state': q, 'left_bit': p, 'read_bit': bit,
                           'raw_transition': [w, 'R' if d else 'L', n],
                           'projected_target': target, 'steps': steps,
                           'duration': len(steps), 'whole_tape_boundary_equal': True})
    return {'incoming_rows': incoming, 'local_traces': traces,
            'local_cases': len(traces), 'durations': dict(Counter(x['duration'] for x in traces)),
            'all_outside_tape_cells_unread_and_unchanged': True,
            'other_raw_rows_commute_in_one_step': True,
            'start_preserved': True, 'halting_control_preserved': True}


def startup(dense, labels):
    q, head, ones = 0, 0, set()
    for _ in range(58154):
        w, d, q = dense[q, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    want = {head - 1, head}
    pos = head + 48; want.add(pos); pos += 1
    for v in physical:
        pos += 1; want.update(range(pos, pos + v + 1)); pos += v + 1
    need((labels[q], head) == (84, -2) and ones == want, 'complete blank startup differs')
    return {'literal_steps': 58154, 'native_state': labels[q], 'absolute_head': head,
            'header_gap': 48, 'physical_register_file': physical,
            'complete_one_positions': sorted(ones), 'outside_tape_all_zero': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--export', action='store_true')
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run without Python -O')
    for name, digest in json.loads((P / 'vendor_hashes.json').read_text()).items():
        need(hashlib.sha256((P / name).read_bytes()).hexdigest() == digest, 'vendored input hash: ' + name)
    need(hashlib.sha256((P / 'pa195.tm').read_bytes()).hexdigest() == EXPECTED_SHA, 'literal hash')
    t = c.read_grammar(P / 'grammar.json')
    raw, node_states, shapes = c.build(t)
    need(len(raw) == 404 and len(shapes) == 68, 'unfolded census')
    folds = json.loads((P / 'folds.json').read_text())
    need(len(folds) == 7, 'fold count')
    folded, aliases = quotient(raw, folds)
    need(folded == table(P / 'pa195.native.tm'), 'native table reconstruction')
    labels = json.loads((P / 'labels.json').read_text())
    need(len(labels) == 196 and labels[0] == 74 and labels[-1] == 254 and len(set(labels)) == 196, 'dense labels')
    dense = table(P / 'pa195.tm')
    need(set(dense) == {(q, b) for q in range(195) for b in (0, 1)}, 'literal binary domain')
    need({(labels[q], b): (w, d, labels[n]) for (q, b), (w, d, n) in dense.items()} == folded,
         'literal/native conjugacy')
    reachable, todo = {0}, [0]
    for q in todo:
        for bit in (0, 1):
            n = dense[q, bit][2]
            need(0 <= n <= 195, 'nonliteral target')
            if n < 195 and n not in reachable:
                reachable.add(n); todo.append(n)
    need(reachable == set(range(195)), 'unreachable advertised working state')
    cert = quotient_certificate(raw, folded, folds, aliases)
    sites, cfg, contracts = c.source(t)
    binding = source_binding(t, sites, cfg)
    emission = emitter(t)
    seed = startup(dense, labels)
    old, _ = c.machine()
    need(all(folded[q, b] == old[q, b] for q in c.BOXSTATES for b in (0, 1)), 'changed register-block oracle rows')
    result = {'working_states': 195, 'binary_rows': 390, 'halt_label': 195,
              'start_label': 0, 'graph_reachable_working_states': len(reachable),
              'literal_sha256': EXPECTED_SHA, 'unfolded_working_states': 202,
              'AX_reader_nodes': 68, 'simultaneous_folds': 7,
              'quotient_local_cases': cert['local_cases'], 'quotient_durations': cert['durations'],
              'source': binding, 'emitter': emission, 'startup_literal_steps': 58154,
              'maximum_path_length': max(len(p) for p, op, arg in sites),
              'full_runtime_replayed': not args.quick, 'new_kernel_checked_theorem': False}
    if not args.quick:
        for name, rows in [('unfolded_runtime', raw), ('folded_runtime', folded)]:
            check = c.validate(rows, contracts)
            need(check['ok'], name + ' failed')
            result[name] = check
    if args.export:
        dump(P / 'source.json', [{'ordinal': i, 'path': ''.join(map(str, p)), 'op': op,
                                 'arg': a, 'instruction': cfg[i]} for i, (p, op, a) in enumerate(sites)])
        dump(P / 'local_fold_certificate.json', cert)
        dump(P / 'startup_certificate.json', seed)
        dump(P / 'emitter_tokens.json', word(t))
        (P / 'unfolded202.native.tm').write_bytes(table_bytes(raw))
        if not args.quick:
            dump(P / 'validation.json', result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
