"""Independent static data review; no delivered module is imported/executed."""
import copy
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
DET = Path('/tmp/zfc-compare-d584512002/zfc242-detour-20261018/zfc242-detour-20261018')
ZERO = Path('/tmp/zfc-compare-d584512002/zfc242-zero-branch-reuse-20261018/zfc242-zero-branch-reuse-20261018')
BASE = Path('/tmp/zfc-intake-8c41b1fb7d/BusyBeaver_242_Research_2026-10-18/busybeaver242-research/runtime/survivor_1_old.tm')
FOLD = Path('/tmp/zfc-intake-8c41b1fb7d/BusyBeaver_241_Companion_2026-10-18/busybeaver241-companion/runtime/candidate_1_old.tm')
COMBINED = Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-combined243/zfc_combined243_old.tm')
checks = 0
inputs = {}


def demand(ok, message):
    global checks
    checks += 1
    if not ok:
        raise ValueError(message)


def raw(p):
    b = p.read_bytes()
    pin = {'path': str(p), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}
    demand(str(p) not in inputs or inputs[str(p)] == pin, 'Input changed during review')
    inputs[str(p)] = pin
    return b


def table(p, count):
    rows = {}
    for line in raw(p).decode().splitlines():
        if not line or line.startswith('#'):
            continue
        fields = line.split()
        demand(len(fields) == 5, 'Unexpected table row')
        q, bit, write, direction, target = fields
        key = (int(q), int(bit))
        demand(key not in rows, 'Duplicate table action')
        demand(bit in ('0', '1') and write in ('0', '1') and direction in ('L', 'R'), 'Invalid action')
        rows[key] = (int(write), direction, None if target == 'H' else int(target))
    states = {q for q, _ in rows}
    demand(len(states) == count and len(rows) == 2 * count, 'Table census differs')
    demand(all((q, b) in rows for q in states for b in (0, 1)), 'Table is partial')
    demand(all(t is None or t in states for _, _, t in rows.values()), 'Undefined target')
    return rows


def relabel(rows, f):
    return {(f(q), bit): (w, direction, None if t is None else f(t))
            for (q, bit), (w, direction, t) in rows.items()}


def names(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(names(a) for a in t[1:])) if len(t) > 1 else set()


def count_nodes(t):
    return 1 if isinstance(t, str) else 1 + sum(count_nodes(a) for a in t[1:])


def measure(data):
    sig = data['signature']
    eqs = data['equations']
    cap = max(len(names(a) | names(b)) for a, b in eqs)
    width = max(1, (len(sig) + cap - 1).bit_length())
    symbol_index = {s: cap + i for i, s in enumerate(sig)}
    def encode(t, variables):
        if isinstance(t, str):
            demand(t in variables, 'Unbound serialized variable')
            return format(variables[t], '0' + str(width) + 'b')
        demand(isinstance(t, (list, tuple)) and t and t[0] in sig, 'Unknown term symbol')
        demand(len(t) - 1 == sig[t[0]], 'Arity mismatch')
        return format(symbol_index[t[0]], '0' + str(width) + 'b') + ''.join(encode(a, variables) for a in t[1:])
    header = format(len(sig), '08b') + ''.join(format(a, '03b') for a in sig.values()) + format(cap, '08b')
    body = ''
    for a, b in eqs:
        local = {v: i for i, v in enumerate(sorted(names(a) | names(b)))}
        body += '1' + encode(a, local) + encode(b, local)
    body += '0'
    endpoints = encode(data['start'], {}) + encode(data['target'], {})
    result = {'signature_symbols': len(sig), 'variable_capacity': cap, 'opcode_width': width,
              'header_bits': len(header), 'equation_bits': len(body), 'endpoint_bits': len(endpoints),
              'complete_packet_bits': len(header + body + endpoints), 'equations': len(eqs),
              'both_side_tree_nodes': sum(count_nodes(x) for e in eqs for x in e)}
    return result, header + body + endpoints


def transform(data, fuse=False, membership=False):
    result = copy.deepcopy(data)
    d = ['d']
    atom = ['A', d, ['A', d, d]]
    def walk(t):
        if isinstance(t, str):
            return t
        if fuse and t == ['top']:
            return d
        children = [walk(a) for a in t[1:]]
        if membership and t[0] == 'p_E':
            x, y = children
            return ['p_eps', ['P', x, ['P', y, d]], atom]
        return [t[0], *children]
    result['equations'] = [[walk(a), walk(b)] for a, b in result['equations']]
    result['start'], result['target'] = walk(result['start']), walk(result['target'])
    if fuse:
        del result['signature']['top']
    if membership:
        del result['signature']['p_E']
    return result


def main():
    base = table(BASE, 242)
    detour = table(DET / 'machine/zfc_detour242_old.tm', 242)
    zero = table(ZERO / 'machine/zfc_zero_reuse242_old.tm', 242)
    combined = table(COMBINED, 243)
    fold = table(FOLD, 241)
    demand(base == detour, 'Detour is not exact primary242A')
    demand(raw(BASE) == raw(DET / 'machine/zfc_detour242_old.tm'), 'Detour byte identity differs')
    rename = lambda x: 27 if x == 15 else x
    renamed = relabel(base, rename)
    for key, value in zero.items():
        demand(renamed.get(key) == value, 'Zero-branch isomorphism mismatch')
    demand(set(renamed) == set(zero), 'Zero-branch state domain differs')
    changes = {}
    for name, rows in [('detour', detour), ('zero_branch', zero), ('current241', fold)]:
        changes[name] = {'deleted_labels': sorted({q for q, _ in combined} - {q for q, _ in rows}),
                         'changed_retained_rows': [{'state': q, 'read': b, 'before': combined[q, b], 'after': v}
                                                  for (q, b), v in rows.items() if combined[q, b] != v]}
    # Exact row support of the existing second fold is unaffected by the rename.
    second_changes = {k: v for k, v in fold.items() if base[k] != v}
    demand(39 in {q for q, _ in base} - {q for q, _ in fold}, 'Expected second fold deletion absent')
    demand(all(q not in (15, 27) for q, _ in second_changes), 'Second fold changes overlap retained-label rename')
    changes['current241_from_primary242A'] = [{'state': q, 'read': b, 'before': base[q, b], 'after': v}
                                             for (q, b), v in second_changes.items()]
    packets = {}
    for stem, directory in [('alias', DET / 'research/equational1768/output'),
                            ('stack_epsc_explicit_pick', ZERO / 'research/stack-kernel/generated'),
                            ('stack_epsc_derived_pick', ZERO / 'research/stack-kernel/generated')]:
        data = json.loads(raw(directory / (stem + '.json')))
        stats, bits = measure(data)
        demand(raw(directory / (stem + '.bits')) == (bits + '\n').encode(), 'Independent exact codec reconstruction differs')
        if 'metrics' in data:
            demand(data['metrics'] == stats, 'Recorded metrics differ')
        packets[stem] = stats
    data = json.loads(raw(ZERO / 'research/stack-kernel/generated/stack_epsc_explicit_pick.json'))
    variants = {}
    for name, fuse, eliminate in [('fuse_truth_only', True, False), ('eliminate_membership_only', False, True), ('both', True, True)]:
        variants[name] = measure(transform(data, fuse, eliminate))[0]
    for p in [DET / 'report.tex', DET / 'README.md', DET / 'research/equational1768/NOTES.md',
              DET / 'research/equational1768/compress_packet.py', DET / 'research/equational1768/optimize_alias.py',
              DET / 'research/equational1768/verify_exact.py', DET / 'research/equational1768/output/horn_proofs.json',
              ZERO / 'README.txt', ZERO / 'paper/zero_reuse242_proof.tex', ZERO / 'paper/stack_kernel_full.tex',
              ZERO / 'research/stack-kernel/README.md', ZERO / 'research/stack-kernel/stack_kernel.py']:
        raw(p)
    for p, old in inputs.items():
        b = Path(p).read_bytes()
        demand(hashlib.sha256(b).hexdigest() == old['sha256'], 'Input changed at close')
    script = Path(__file__)
    result = {'status': 'INDEPENDENT_STATIC_DATA_REVIEW_PASS', 'checks': checks,
              'scope': 'Own strict table/term parser and packet reconstruction only. No delivered code, simulator, compiler, consistency search, or proof assistant executed.',
              'reviewer_source': {'path': str(script), 'sha256': hashlib.sha256(script.read_bytes()).hexdigest()},
              'inputs': list(inputs.values()), 'table_changes': changes,
              'zero_branch_isomorphism': {'renaming': {'15': 27}, 'matched_actions': 484, 'all_other_labels_fixed': True},
              'delivered_packets': packets,
              'own_static_stack_term_transform_censuses': variants,
              'variant_scope': 'Exact syntax-only size calculations of specified replacements; no executable candidate or model calibration is inferred from these measurements.',
              'findings': []}
    (OUT / 'static-review.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': checks, 'packets': packets, 'stack_transforms': variants}))


if __name__ == '__main__':
    main()
