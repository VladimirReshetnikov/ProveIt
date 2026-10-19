#!/usr/bin/env python3
"""Independent, portable checker of a source-register product invariant.

No discovery code is imported. The CFG is rebuilt with a full binary trie and
the consumed-path list operations of RegisterPath. The abstract atoms are
{0},...,{K-1}, {n>=K: n even}, {n>=K: n odd}. Every delivered fact is a product
of unions of these atoms, or null for the empty set. Seed inclusion and every
guarded transfer inclusion prove an invariant of the unbounded source run.

The checker verifies a post-fixpoint, not that the discovery procedure computed
the least one. Its proof applies to arbitrary execution length and arbitrarily
large register values, through arithmetic-progression identities for tail atoms.
"""
from pathlib import Path
from collections import Counter
import argparse
import copy
import hashlib
import json

SEED = (3, 0, 0, 0, 3, 0, 0, 0, 0)


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def build_cfg(rows):
    require(isinstance(rows, list) and rows, 'The source must be a nonempty list')
    for row in rows:
        require(isinstance(row, list) and len(row) == 3, 'Malformed source leaf')
        p, op, arg = row
        require(isinstance(p, str) and p and all(b in '01' for b in p), 'Invalid path')
        if op in ('CI', 'CD'):
            require(type(arg) is int and 0 <= arg < 9, 'Invalid register')
        elif op in ('CB', 'CC'):
            require(type(arg) is int and arg >= 0, 'Invalid jump count')
        else:
            require(op == 'CH' and arg is None, 'Invalid opcode or halt argument')
    ordered = sorted(rows, key=lambda x: x[0])
    trie = {}
    for i, (path, _, _) in enumerate(ordered):
        node = trie
        for bit in path:
            require('leaf' not in node, 'A source leaf is a prefix of another')
            node = node.setdefault(int(bit), {})
        require(not node, 'A source path is duplicated or prefixes another')
        node['leaf'] = i

    def check_full(node):
        if 'leaf' in node:
            require(set(node) == {'leaf'}, 'Leaf with children')
            return 0
        require(set(node) == {0, 1}, 'The source tree is not full')
        return 1 + max(check_full(node[0]), check_full(node[1]))

    depth = check_full(trie)

    def decode(path):
        node, consumed = trie, 0
        while 'leaf' not in node:
            bit = path[consumed] if consumed < len(path) else 0
            node = node[bit]
            consumed += 1
        require(not any(path[consumed:]), 'Nonzero unused path tail')
        return node['leaf']

    # These are list operations, independently of the discovery checker's
    # integer increment and last-k-position slicing implementation.
    def increment(path):
        result = list(path)
        carry = 1
        for i in range(len(result)-1, -1, -1):
            if carry:
                result[i], carry = 1-result[i], result[i]
        return result

    def strip(path, selected_bit, count):
        result = list(path)
        while count and result:
            if result.pop() == selected_bit:
                count -= 1
        return result

    cfg = []
    for path, op, arg in ordered:
        consumed = [int(b) for b in path]
        if op == 'CI':
            cfg.append(('INC', arg, decode(increment(consumed))))
        elif op == 'CD':
            cfg.append(('DEC', arg, decode(increment(consumed)),
                        decode(increment(strip(consumed, 0, 1)))))
        elif op == 'CB':
            cfg.append(('JUMP', decode(increment(strip(consumed, 0, arg)))))
        elif op == 'CC':
            cfg.append(('JUMP', decode(strip(consumed, 1, arg))))
        else:
            cfg.append(('HALT',))
    return ordered, cfg, decode([]), depth


def arithmetic_atoms(threshold):
    require(type(threshold) is int and threshold >= 1, 'Threshold must be positive')

    def classify(n):
        require(n >= 0, 'Negative register value')
        return n if n < threshold else threshold + n % 2

    # Each large atom is the progression first + 2*t, t in N. Its shifted
    # progression has finitely many values below K and an unbounded tail of
    # a single parity. This proves the image mask without bounded sampling.
    actions, proof_rows = {}, []
    for atom in range(threshold+2):
        for delta in (-1, 1):
            if atom < threshold:
                value = atom+delta
                small = [value] if 0 <= value < threshold else []
                tail_parity = value % 2 if value >= threshold else None
                mask = 0 if value < 0 else 1 << classify(value)
                description = {'kind': 'singleton', 'value': atom}
            else:
                parity = atom-threshold
                first = threshold + ((parity-threshold) % 2)
                image_first = first+delta
                require(image_first >= 0, 'A positive tail shifted below zero')
                small = list(range(image_first, threshold, 2)) if image_first < threshold else []
                tail_parity = (parity+delta) % 2
                mask = (1 << (threshold+tail_parity)) | sum(1 << n for n in small)
                description = {'kind': 'arithmetic_progression', 'first': first, 'step': 2}
            actions[atom, delta] = mask
            proof_rows.append({'atom': atom, 'input': description, 'delta': delta,
                               'image_small_values': small,
                               'image_unbounded_tail_parity': tail_parity,
                               'least_abstract_image_mask': mask})

    def image(mask, delta):
        result = 0
        for atom in range(threshold+2):
            if mask & (1 << atom):
                result |= actions[atom, delta]
        return result

    return classify, image, proof_rows


def verify(ordered, cfg, start, facts, threshold):
    classify, image, arithmetic = arithmetic_atoms(threshold)
    require(isinstance(facts, list) and len(facts) == len(cfg), 'Incorrect fact array length')
    full_mask = (1 << (threshold+2))-1
    for i, fact in enumerate(facts):
        if fact is not None:
            require(isinstance(fact, list) and len(fact) == 9, f'Malformed fact at {i}')
            require(all(type(mask) is int and 0 < mask <= full_mask for mask in fact),
                    f'Invalid atom mask at {i}')
    require(facts[start] is not None, 'The seed leaf is marked unreachable')
    for register, value in enumerate(SEED):
        require(facts[start][register] & (1 << classify(value)),
                f'Seed register {register} is excluded')

    edge_counts = Counter()
    zero_only, positive_only = [], []
    for i, descriptor in enumerate(cfg):
        fact = facts[i]
        if fact is None:
            continue
        transfers = []
        op = descriptor[0]
        if op == 'INC':
            _, register, target = descriptor
            successor = list(fact)
            successor[register] = image(fact[register], 1)
            transfers.append(('increment', target, successor))
        elif op == 'DEC':
            _, register, positive_target, zero_target = descriptor
            if fact[register] & 1:
                successor = list(fact)
                successor[register] = 1
                transfers.append(('decrement_zero', zero_target, successor))
            positive_mask = fact[register] & ~1
            if positive_mask:
                successor = list(fact)
                successor[register] = image(positive_mask, -1)
                transfers.append(('decrement_positive', positive_target, successor))
            claim = {'index': i, 'path': ordered[i][0], 'reg': register}
            if fact[register] == 1:
                zero_only.append({**claim, 'only': 'zero'})
            elif not fact[register] & 1:
                positive_only.append({**claim, 'only': 'positive'})
        elif op == 'JUMP':
            transfers.append(('jump', descriptor[1], list(fact)))
        else:
            require(descriptor == ('HALT',), 'Unknown CFG descriptor')
            edge_counts['halt_leaf'] += 1
        for guard, target, successor in transfers:
            require(facts[target] is not None,
                    f'Enabled {guard} edge {i}->{target} enters a bottom fact')
            for register, mask in enumerate(successor):
                require(mask & ~facts[target][register] == 0,
                        f'Post-fixpoint failure {i}->{target}, guard {guard}, register {register}')
            edge_counts[guard] += 1
    return {
        'postfixpoint_edge_counts': dict(sorted(edge_counts.items())),
        'arithmetic_atom_rules': arithmetic,
        'forced_decrement_guards': sorted(zero_only+positive_only, key=lambda c:c['index']),
        'unreachable_instructions': [i for i, fact in enumerate(facts) if fact is None],
        'reachable_in_abstraction': sum(fact is not None for fact in facts),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--facts', type=Path, required=True)
    parser.add_argument('--summary', type=Path, required=True)
    parser.add_argument('--threshold', type=int, default=16)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    sites = json.loads(args.sites.read_text())
    facts = json.loads(args.facts.read_text())
    summary = json.loads(args.summary.read_text())
    ordered, cfg, start, depth = build_cfg(sites)
    result = verify(ordered, cfg, start, facts, args.threshold)
    expected = {
        'status': 'PASS_FINITE_PRODUCT_INVARIANT',
        'domain': list(range(args.threshold))+['large even', 'large odd'],
        'initial_registers': list(SEED),
        'source_sha256': digest(args.sites),
        'instructions': len(cfg),
        **{k: result[k] for k in ('forced_decrement_guards', 'unreachable_instructions',
                                  'reachable_in_abstraction')},
    }
    for key, value in expected.items():
        require(summary.get(key) == value, f'Summary mismatch: {key}')

    controls = []
    modified = copy.deepcopy(facts)
    seed_atom = 3 if 3 < args.threshold else args.threshold+1
    modified[start][0] &= ~(1 << seed_atom)
    if not modified[start][0]:
        modified[start][0] = 1
    try:
        verify(ordered, cfg, start, modified, args.threshold)
        rejected, reason = False, None
    except ValueError as error:
        rejected, reason = True, str(error)
    controls.append({'change': 'exclude the first seed register value',
                     'rejected': rejected, 'reason': reason})
    forced = next((c for c in result['forced_decrement_guards']
                   if c['only'] == 'zero' and facts[cfg[c['index']][2]] is None), None)
    if forced is not None:
        modified = copy.deepcopy(facts)
        modified[forced['index']][forced['reg']] |= 2
        try:
            verify(ordered, cfg, start, modified, args.threshold)
            rejected, reason = False, None
        except ValueError as error:
            rejected, reason = True, str(error)
        controls.append({'change': 'add value 1 to a forced-zero decrement guard',
                         'index': forced['index'], 'register': forced['reg'],
                         'rejected': rejected, 'reason': reason})
    require(all(c['rejected'] for c in controls), 'A negative control was accepted')

    output = {
        'status': 'PASS_INDEPENDENT_SOURCE_PRODUCT_INVARIANT',
        'source_sha256': digest(args.sites), 'facts_sha256': digest(args.facts),
        'supplied_summary_sha256': digest(args.summary), 'checker_sha256': digest(Path(__file__)),
        'threshold': args.threshold, 'registers': 9, 'initial_registers': list(SEED),
        'instructions': len(cfg), 'initial_leaf': start, 'maximum_source_depth': depth,
        'cfg_sha256': canonical_digest(cfg),
        'all_successor_paths_have_only_zero_unused_tail': True,
        **result,
        'negative_controls': controls,
        'scope': 'An inductive invariant of every finite prefix of the exact source run from the calibrated seed. Tail atoms contain arbitrarily large naturals. No time or register-value bound, and no binary-state saving is asserted by this certificate.'
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k != 'arithmetic_atom_rules'}, indent=2))


if __name__ == '__main__':
    main()
