#!/usr/bin/env python3
"""Standalone source proof for candidate1dcd14a4, standard library only.
No machine execution, imported research module, or finite register sample is used.
Two independent complete guarded-CFG resolvers prove source bisimulation.
"""
import json, hashlib
from pathlib import Path
from functools import cache

def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(data):
    return (json.dumps(data, separators=(',', ':')) + '\n').encode('ascii')


def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def leaf(node):
    return isinstance(node[0], str)


def tree(rows):
    root = {}
    for path, op, arg in rows:
        require(path and set(path) <= {'0', '1'}, 'Invalid source path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid opcode')
        require((op == 'CH' and arg is None) or
                (op != 'CH' and type(arg) is int and arg >= 0), 'Invalid operand')
        require(op not in ('CI', 'CD') or arg < 9, 'Invalid register')
        require(op not in ('CB', 'CC') or arg >= 1, 'Invalid control depth')
        at = root
        for bit in path:
            require('instruction' not in at, 'Overlapping source paths')
            at = at.setdefault(bit, {})
        require(not at, 'Duplicate or overlapping source path')
        at['instruction'] = (op, arg)
    def visit(node):
        if 'instruction' in node:
            require(set(node) == {'instruction'}, 'Leaf has children')
            return node['instruction']
        require(set(node) == {'0', '1'}, 'Source tree is not full')
        return visit(node['0']), visit(node['1'])
    result = visit(root)
    require(sites(result) == rows, 'Source rows are not in canonical ordinal order')
    return result


def sites(node, prefix=''):
    if leaf(node):
        return [[prefix, *node]]
    return sites(node[0], prefix + '0') + sites(node[1], prefix + '1')


@cache
def boundary(node):
    if leaf(node):
        op, arg = node
        if op == 'CD': return 1, 0, False
        if op == 'CB': return arg, 0, False
        if op == 'CC': return 0, arg, False
        return 0, 0, op == 'CH'
    a, b = boundary(node[0]), boundary(node[1])
    return (max(max(a[0] - 1, 0), b[0]),
            max(a[1], max(b[1] - 1, 0)), a[2] or b[2])


def metrics(root):
    seen = set()
    def visit(node):
        if node in seen: return
        seen.add(node)
        if not leaf(node):
            visit(node[0]); visit(node[1])
    visit(root)
    rows = sites(root)
    return {'dag_nodes': len(seen), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def graph_arithmetic(rows):
    """Binary successor/cut resolver, including the no-stray-suffix premise."""
    leaves = {p: i for i, (p, _, _) in enumerate(rows)}
    depth = max(map(len, leaves))
    checks = 0
    def locate(prefix):
        nonlocal checks
        word = prefix + '0' * depth
        for length in range(1, depth + 1):
            if word[:length] in leaves:
                require('1' not in prefix[length:], 'Stray one beyond successor leaf')
                checks += 1
                return leaves[word[:length]]
        raise ValueError('Successor has no leaf')
    def increment(path):
        if not path: return ''
        return format((int(path, 2) + 1) % (1 << len(path)), '0' + str(len(path)) + 'b')
    def cut(path, edge, level):
        positions = [i for i, bit in enumerate(path) if bit == edge]
        return path[:positions[-level]] if len(positions) >= level else ''
    graph = []
    for path, op, arg in rows:
        if op == 'CI':
            effect, targets = ['increment', arg], [locate(increment(path))]
        elif op == 'CD':
            effect = ['decrement', arg]
            targets = [locate(increment(cut(path, '0', 1))), locate(increment(path))]
        elif op == 'CB':
            effect, targets = ['identity'], [locate(increment(cut(path, '0', arg)))]
        elif op == 'CC':
            effect, targets = ['identity'], [locate(cut(path, '1', arg))]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    require(locate('') == 0, 'Initial ordinal leaf is not zero')
    return graph, checks


def graph_intervals(rows):
    """Independent resolver: subtree intervals and outward ancestor walking."""
    indices = {path: i for i, (path, _, _) in enumerate(rows)}
    intervals = {}
    def visit(path):
        if path in indices:
            answer = indices[path], indices[path] + 1
        else:
            a, b = visit(path + '0'), visit(path + '1')
            require(a[1] == b[0], 'Noncontiguous source subtree')
            answer = a[0], b[1]
        intervals[path] = answer
        return answer
    require(visit('') == (0, len(rows)), 'Source interval census')
    def unwind(path, edge, count):
        while path:
            last, path = path[-1], path[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return intervals[path][1] % len(rows) if edge == '0' else intervals[path][0]
        return 0
    graph = []
    for i, (path, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            effect, targets = ['increment', arg], [after]
        elif op == 'CD':
            effect, targets = ['decrement', arg], [unwind(path, '0', 1), after]
        elif op == 'CB':
            effect, targets = ['identity'], [unwind(path, '0', arg)]
        elif op == 'CC':
            effect, targets = ['identity'], [unwind(path, '1', arg)]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    return graph



def main():
    here = Path(__file__).resolve().parent
    baseline_raw = (here/'baseline_sites219.json').read_bytes()
    candidate_raw = (here/'candidate_sites218.json').read_bytes()
    recipe_raw = (here/'dag_recipe.json').read_bytes()
    baseline_pin = '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
    middle_pin = '1b7c4685c3a594cd52f30872ec4cb2e70360e86cd5eb5411d71dcf454174a3c6'
    candidate_pin = '1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
    require(sha(baseline_raw) == baseline_pin, 'Pinned upstream source mismatch')
    require(sha(candidate_raw) == candidate_pin, 'Pinned candidate source mismatch')
    baseline_rows = json.loads(baseline_raw)
    baseline_tree = tree(baseline_rows)
    recipe = json.loads(recipe_raw)
    require(recipe['baseline_sha256'] == baseline_pin and recipe['output_sha256'] == middle_pin, 'DAG recipe source pins')
    nodes, ids = [], {}
    def intern(n):
        if n not in ids:
            ids[n] = len(nodes); nodes.append(n)
        return ids[n]
    def freeze(t):
        return intern(t if leaf(t) else (freeze(t[0]), freeze(t[1])))
    native_root = freeze(baseline_tree)
    require(len(nodes) == recipe['baseline_DAG_nodes'] == 206, 'Upstream DAG census')
    require(native_root == 205, 'Native root index')
    for index, row in enumerate(recipe['new_nodes'], len(nodes)):
        n = tuple(row)
        require(isinstance(n[0], str) or all(type(x) is int and 0 <= x < index for x in n), 'DAG topological order')
        require(intern(n) == index, 'DAG recipe duplicate or index mismatch')
    @cache
    def thaw(n):
        x = nodes[n]
        return x if leaf(x) else (thaw(x[0]), thaw(x[1]))
    middle_tree = thaw(recipe['root'])
    middle_rows = sites(middle_tree)
    require(sha(compact(middle_rows)) == middle_pin, 'Intermediate reconstruction pin')
    require(nodes[98] == (84,67) and nodes[84] == (83,56) and nodes[68] == (56,67), 'Global rotation shape')
    old_piece = thaw(98)
    new_piece = (thaw(83), (thaw(56), thaw(67)))
    occurrences = []
    def collect(t, p='', ordinal=0):
        if t == old_piece: occurrences.append([p, ordinal])
        if not leaf(t):
            collect(t[0], p+'0', ordinal)
            collect(t[1], p+'1', ordinal+len(sites(t[0])))
    collect(middle_tree)
    require(len(occurrences) == 5, 'Expected five global rotation occurrences')
    @cache
    def rewrite(t):
        if t == old_piece: return new_piece
        return t if leaf(t) else (rewrite(t[0]), rewrite(t[1]))
    candidate_tree = rewrite(middle_tree)
    candidate_rows = sites(candidate_tree)
    rebuilt = compact(candidate_rows)
    require(rebuilt == candidate_raw, 'Candidate byte-for-byte reconstruction')
    require(tree(candidate_rows) == candidate_tree, 'Candidate full tree and order')
    stages = [('upstream219', baseline_rows), ('startup37_182', middle_rows), ('only_role96_218_source', candidate_rows)]
    controls = []
    reference = None
    for name, rows in stages:
        arithmetic, checks = graph_arithmetic(rows)
        intervals = graph_intervals(rows)
        require(arithmetic == intervals, 'Independent CFG resolvers disagree at '+name)
        require([row[1:] for row in rows] == [row[1:] for row in baseline_rows], 'Primitive ordinal word changed')
        require(rows[:37] == baseline_rows[:37], 'Bootstrap37 source prefixes changed')
        if reference is None: reference = arithmetic
        require(arithmetic == reference, 'Guarded ordinal CFG changed at '+name)
        controls.append(dict(stage=name, source_sha256=sha(compact(rows)), primitive_count=len(rows),
            guarded_successors=sum(len(row[1]) for row in arithmetic), no_stray_suffix_checks=checks,
            first37_PC_equal=True, metrics=metrics(tree(rows))))
    require(controls[-1]['metrics'] == dict(dag_nodes=205, leaf_occurrences=4744, maximum_depth=38, maximum_zero_run=6), 'Candidate source metric pin')
    correspondence = dict(schema='ORDINAL_REGISTER_STORE_IDENTITY_V1',
        columns=['ordinal','upstream_PC','startup37_PC','candidate_PC','operation','argument','guarded_target_ordinals'],
        rows=[[i, baseline_rows[i][0], middle_rows[i][0], candidate_rows[i][0], *candidate_rows[i][1:], reference[i][1]] for i in range(len(candidate_rows))])
    (here/'reconstructed_sites218.json').write_bytes(rebuilt)
    (here/'ordinal_correspondence.json').write_bytes(compact(correspondence))
    receipt = dict(status='ALL_NATURAL_SOURCE_BISIMULATION_PASS',
        baseline_source_sha256=baseline_pin, intermediate_source_sha256=middle_pin, candidate_source_sha256=candidate_pin,
        recipe_sha256=sha(recipe_raw), verifier_sha256=sha(Path(__file__).read_bytes()),
        complete_guarded_CFG_sha256=sha(compact(reference)), correspondence_sha256=sha(compact(correspondence)),
        stages=controls, final_rotation=dict(old_node=98, old_shape='((83,56),67)', new_shape='(83,(56,67))', occurrences=occurrences),
        theorem='For every ordinal and every nine-tuple of natural-register values, relate corresponding sources by identical ordinal and register store. The operation and argument coincide, so guards, register updates and halting status coincide; the exhaustive guarded-CFG equality gives identical successor ordinals. This is a strong step-for-step bisimulation, hence the initialized sources halt in exactly the same circumstances.',
        scope='Source proof only. This receipt does not certify binary-machine execution, startup, state count, or the upstream foundational equiconsistency theorem.')
    dump(here/'verification.json', receipt)
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__': main()
