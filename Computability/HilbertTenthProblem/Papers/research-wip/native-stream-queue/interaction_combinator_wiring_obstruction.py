"""Finite wiring obstruction inside Lafont's interaction combinators.

Only the delta-delta rule is simulated.  It preserves auxiliary-port labels.
The engine retains agent-free cyclic wires and accepts closed, port-linear
nets with delta cells.  No Diophantine operation bound is claimed.
"""
from collections import Counter, defaultdict
from copy import deepcopy
from functools import lru_cache
import argparse
import hashlib
import json
from pathlib import Path


REFERENCE = {
    'author': 'Yves Lafont',
    'title': 'Interaction Combinators',
    'journal': 'Information and Computation 137 (1997), 69-101',
    'author_primary_url': 'https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/combinators.ps',
    'inspected_pdf_url': 'https://chorasimilarity.wordpress.com/wp-content/uploads/2024/01/ic-lafont-1.pdf',
    'inspected_pdf_sha256': 'b717eeb9d4fe7ddb7be5f4905ead82770dc8624b1d58be759dbd308acd7142ec',
    'inspected_author_postscript_sha256': 'ffdc57506bcbd1d75c3bcd0d7d044bdefd196fd1e56103406a137e20d6d59fa9',
    'port_and_cyclic_wire_definition': 'journal page 71, section 1.1',
    'six_rule_table': 'journal page 81, Figure 2',
    'delta_port_convention_and_universality': 'journal page 82, section 2.1 and Theorem 1',
}
PORT_TYPES = ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2))


def check_net(net):
    """Validate an exact canonical closed delta-net, including cyclic wires."""
    if type(net) is not dict or set(net) != {'cells', 'wires', 'loops'}:
        raise ValueError('a complete closed delta-net is required')
    cells, wires, loops = net['cells'], net['wires'], net['loops']
    if (type(cells) is not list or any(type(c) is not int or c < 0 for c in cells)
            or cells != sorted(set(cells))):
        raise ValueError('cell labels must be a sorted list of distinct naturals')
    if type(loops) is not int or loops < 0:
        raise ValueError('cyclic-wire count must be a natural integer')
    if type(wires) is not list:
        raise ValueError('wires must be a canonical list')
    for edge in wires:
        if (type(edge) is not list or len(edge) != 2
                or any(type(p) is not int or p < 0 for p in edge)
                or edge[0] >= edge[1]):
            raise ValueError('wire endpoints must be two ordered distinct natural ports')
    if wires != sorted(wires):
        raise ValueError('wire list must be ordered')
    expected = sorted(3 * c + p for c in cells for p in range(3))
    if sorted(p for edge in wires for p in edge) != expected:
        raise ValueError('each existing cell port must occur exactly once')
    return net


def make_net(cells, wires, loops=0):
    """Canonicalize integer lists supplied by internal constructors."""
    return check_net({'cells': sorted(cells),
                      'wires': sorted([sorted(edge) for edge in wires]),
                      'loops': loops})


def examples():
    return {
        'A': make_net([0, 1, 2, 3],
                      [[0, 3], [1, 7], [2, 9], [4, 10], [5, 6], [8, 11]]),
        'B': make_net([0, 1, 2, 3],
                      [[0, 3], [1, 7], [2, 9], [4, 10], [5, 8], [6, 11]]),
    }


def active_pairs(net):
    check_net(net)
    return [[a // 3, b // 3] for a, b in net['wires'] if a % 3 == b % 3 == 0]


def summary(net):
    """Forget port attachment but retain the full labelled underlying graph."""
    check_net(net)
    hist = Counter(tuple(sorted((a % 3, b % 3))) for a, b in net['wires'])
    return {
        'cells': list(net['cells']),
        'agent_counts_gamma_delta_epsilon': [0, len(net['cells']), 0],
        'underlying_cell_edges': sorted([sorted((a // 3, b // 3))
                                         for a, b in net['wires']]),
        'port_type_edge_counts_00_01_02_11_12_22': [hist[p] for p in PORT_TYPES],
        'initial_active_pairs': active_pairs(net),
        'free_ports': 0,
        'cyclic_wires': net['loops'],
    }


def annihilate(net, pair):
    """Apply actual delta-delta gluing, preserving every resulting wire cycle.

    Old matching edges and new same-label auxiliary joins form paths or cycles.
    A path has two surviving ports; a cycle has none and becomes a cyclic wire.
    Parallel temporary edges are retained: a two-edge cycle is a real loop.
    """
    check_net(net)
    if (type(pair) is not list or len(pair) != 2
            or any(type(v) is not int for v in pair) or pair not in active_pairs(net)):
        raise ValueError('an actual ordered principal-principal pair is required')
    u, v = pair
    removed = {3 * c + p for c in pair for p in range(3)}
    principal_edge = [3 * u, 3 * v]
    adjacent = defaultdict(list)
    for a, b in net['wires']:
        if [a, b] == principal_edge:
            continue
        adjacent[a].append(b)
        adjacent[b].append(a)
    for p in (1, 2):
        a, b = 3 * u + p, 3 * v + p
        adjacent[a].append(b)
        adjacent[b].append(a)
    for port, neighbors in adjacent.items():
        assert len(neighbors) == (2 if port in removed else 1)
    seen, wires, loops = set(), [], net['loops']
    for start in sorted(adjacent):
        if start in seen:
            continue
        todo, component = [start], set()
        while todo:
            port = todo.pop()
            if port in component:
                continue
            component.add(port)
            todo.extend(adjacent[port])
        seen.update(component)
        survivors = sorted(component - removed)
        assert len(survivors) in (0, 2)
        if survivors:
            wires.append(survivors)
        else:
            loops += 1
    return make_net([c for c in net['cells'] if c not in pair], wires, loops)


def normalize(net):
    """Delta-only reduction terminates because every step removes two cells."""
    check_net(net)
    trace = []
    current = deepcopy(net)
    while active_pairs(current):
        pair = active_pairs(current)[0]
        trace.append({'net': deepcopy(current), 'chosen_pair': pair})
        following = annihilate(current, pair)
        assert len(following['cells']) == len(current['cells']) - 2
        current = following
    trace.append({'net': current, 'chosen_pair': None})
    return trace


def is_normal(net):
    return not active_pairs(net)


def is_agent_free(net):
    check_net(net)
    return not net['cells']


def is_exact_target(net):
    check_net(net)
    return net == {'cells': [], 'wires': [], 'loops': 2}


def matchings(ports):
    if not ports:
        yield ()
        return
    first = ports[0]
    for j in range(1, len(ports)):
        for rest in matchings(ports[1:j] + ports[j + 1:]):
            yield ((first, ports[j]),) + rest


def is_k4(net):
    return (net['cells'] == [0, 1, 2, 3]
            and summary(net)['underlying_cell_edges'] ==
            [[i, j] for i in range(4) for j in range(i + 1, 4)])


def frozen_key(net):
    return tuple(net['cells']), tuple(tuple(e) for e in net['wires']), net['loops']


@lru_cache(None)
def terminal_keys(key):
    net = make_net(key[0], key[1], key[2])
    pairs = active_pairs(net)
    if not pairs:
        return frozenset([key])
    out = set()
    for pair in pairs:
        out.update(terminal_keys(frozen_key(annihilate(net, pair))))
    return frozenset(out)


def audit_pair():
    nets = examples()
    assert summary(nets['A']) == summary(nets['B'])
    assert is_k4(nets['A']) and is_k4(nets['B'])
    assert active_pairs(nets['A']) == active_pairs(nets['B']) == [[0, 1]]
    traces = {name: normalize(net) for name, net in nets.items()}
    expected_A1 = make_net([2, 3], [[6, 9], [7, 10], [8, 11]])
    expected_B1 = make_net([2, 3], [[6, 11], [7, 10], [8, 9]])
    assert traces['A'][1]['net'] == expected_A1
    assert traces['B'][1]['net'] == expected_B1
    assert active_pairs(expected_A1) == [[2, 3]]
    assert is_normal(expected_B1)
    assert summary(expected_A1) != summary(expected_B1)
    assert len(traces['A']) - 1 == 2 and len(traces['B']) - 1 == 1
    assert is_exact_target(traces['A'][-1]['net'])
    assert not is_agent_free(traces['B'][-1]['net'])
    assert all(is_normal(trace[-1]['net']) for trace in traces.values())
    # The first step is uniquely enabled in each literal input.  B then has no
    # redex, so no alternative schedule could reach an agent-free state.
    assert all(len(terminal_keys(frozen_key(net))) == 1 for net in nets.values())
    return {'inputs': nets, 'common_summary': summary(nets['A']), 'traces': traces,
            'A_reaches_exact_two_loop_target': True,
            'B_reaches_any_agent_free_net': False,
            'both_inputs_normalize': True}


def exhaustive_search():
    all_count = k4_count = transitions = 0
    port_histogram_classes = defaultdict(set)
    all_digest = hashlib.sha256()
    k4_digest = hashlib.sha256()
    for wires in matchings(tuple(range(12))):
        net = make_net([0, 1, 2, 3], wires)
        trace = normalize(net)
        final = trace[-1]['net']
        assert is_normal(final)
        assert len(terminal_keys(frozen_key(net))) == 1
        assert terminal_keys(frozen_key(net)) == frozenset([frozen_key(final)])
        record = {'input': net, 'normal_form': final, 'steps': len(trace) - 1}
        payload = (json.dumps(record, sort_keys=True, separators=(',', ':')) + '\n').encode()
        all_digest.update(payload)
        all_count += 1
        transitions += len(active_pairs(net))
        if is_k4(net):
            k4_count += 1
            k4_digest.update(payload)
            hist = tuple(summary(net)['port_type_edge_counts_00_01_02_11_12_22'])
            port_histogram_classes[hist].add((len(final['cells']), final['loops']))
    assert all_count == 10395 and k4_count == 1296
    ambiguous = []
    for hist, outcomes in sorted(port_histogram_classes.items()):
        if any(c == 0 for c, _ in outcomes) and any(c > 0 for c, _ in outcomes):
            ambiguous.append({'port_type_counts': list(hist),
                              'normal_form_cell_loop_counts': [list(x) for x in sorted(outcomes)]})
    assert ambiguous
    return {'all_closed_four_delta_matchings': all_count,
            'initial_enabled_pair_checks': transitions,
            'all_schedules_same_normal_form_checked': all_count,
            'simple_K4_matchings': k4_count,
            'K4_port_histogram_classes': len(port_histogram_classes),
            'ambiguous_K4_histograms': ambiguous,
            'all_records_sha256': all_digest.hexdigest(),
            'K4_records_sha256': k4_digest.hexdigest()}


def guard_checks():
    count = 0
    def reject(fn):
        nonlocal count
        try:
            fn()
        except (TypeError, ValueError, KeyError):
            count += 1
        else:
            raise AssertionError('invalid net accepted')
    base = examples()['A']
    malformed = []
    for field, value in [('loops', -1), ('loops', True), ('loops', 0.0),
                         ('cells', [0, 1, 2, True]), ('cells', [0, 1, 2, 3.0]),
                         ('cells', [0, 1, 2, 2]), ('cells', [3, 2, 1, 0]),
                         ('wires', base['wires'][:-1]), ('wires', tuple(base['wires']))]:
        bad = deepcopy(base); bad[field] = value; malformed.append(bad)
    for value in (True, 0.0, -1, 999):
        bad = deepcopy(base); bad['wires'][0][0] = value; malformed.append(bad)
    bad = deepcopy(base); bad['wires'][0].reverse(); malformed.append(bad)
    bad = deepcopy(base); bad['wires'][0] = list(bad['wires'][1]); malformed.append(bad)
    bad = deepcopy(base); bad['extra'] = 0; malformed.append(bad)
    for bad in malformed:
        for api in (check_net, active_pairs, summary, normalize, is_agent_free, is_exact_target):
            reject(lambda bad=bad, api=api: api(bad))
    for pair in ([1, 0], [0, 2], [0, True], [0.0, 1], (0, 1), [0, 1, 2]):
        reject(lambda pair=pair: annihilate(base, pair))
    # Preserve a pre-existing cyclic wire and count new parallel-edge cycles.
    two = make_net([0, 1], [[0, 3], [1, 4], [2, 5]], loops=3)
    assert annihilate(two, [0, 1]) == {'cells': [], 'wires': [], 'loops': 5}
    empty = make_net([], [], loops=7)
    assert normalize(empty) == [{'net': empty, 'chosen_pair': None}]
    return {'rejected_malformed_calls': count,
            'preexisting_and_created_cycles_preserved': True,
            'agent_free_cyclic_wires_retained': True}


def verify():
    return {
        'status': 'PASS_INTERACTION_COMBINATOR_WIRING_OBSTRUCTION',
        'source_file_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'primary_source': REFERENCE,
        'port_encoding': 'port (cell c, label p) is the natural integer 3*c+p; p=0 is principal',
        'simulated_rule': 'delta-delta; auxiliary 1 joins 1 and auxiliary 2 joins 2',
        'domain': 'closed port-linear finite delta-only nets, with nonnegative cyclic-wire count',
        'witness_pair': audit_pair(),
        'exhaustive_search': exhaustive_search(),
        'guards': guard_checks(),
        'limitation': 'Only the displayed summary abstraction is refuted. No obstruction to topology-aware Diophantine representations, no operation bound, and no ordinary-input universal loader is claimed.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(json.dumps({'search': result['exhaustive_search'], 'guards': result['guards']}, sort_keys=True))
