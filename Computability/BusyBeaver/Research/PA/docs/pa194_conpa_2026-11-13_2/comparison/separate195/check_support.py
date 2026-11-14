from pathlib import Path
from collections import Counter
import sys,json
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'vendor'))
import compiler as c
INC=('leaf','inc',1)
BREAK=('leaf','breakTo',1)
c.MACROS[(INC,INC)]=99
c.MACROS[((INC,INC),(INC,INC))]=190
NAMES={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA','node65':'cons','node72':'readH','node75':'readDCons','node142':'copyGuard','node150':'compareGuard',INC:'incT',BREAK:'close'}

def need(condition, message):
    if not condition:
        raise ValueError(message)

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

def word(t):
    if t == 'node60':
        return ['incT'] * 2
    if t == 'node61':
        return ['incT'] * 4
    if c.isnode(t):
        return word(t[0]) + word(t[1])
    return [NAMES[t]]

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
