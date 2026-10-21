#!/usr/bin/env python3
"""Standalone source equivalence proof for partial-selector proposals, standard library only.
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
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--baseline', default='research_sub216/intake/K217_Dominated_Continuation_2026-10-20/machine/sites217.json')
    ap.add_argument('--candidate', required=True)
    ap.add_argument('--out', required=True)
    args=ap.parse_args(); out=Path(args.out); out.mkdir(parents=True,exist_ok=True)
    baseline_raw=Path(args.baseline).read_bytes(); candidate_raw=Path(args.candidate).read_bytes()
    require(sha(baseline_raw)=='9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655', 'Wrong pinned upstream217 source')
    baseline=json.loads(baseline_raw); candidate=json.loads(candidate_raw)
    trees=[tree(baseline),tree(candidate)]
    require([r[1:]for r in baseline]==[r[1:]for r in candidate], 'Literal primitive word changed')
    require(baseline[:37]==candidate[:37], 'Startup-facing37 paths changed')
    AX='11101001001'
    require([r for r in baseline if not r[0].startswith(AX)]==[r for r in candidate if not r[0].startswith(AX)], 'Non-AX path changed')
    graphs=[]; controls=[]
    for name,rows,t in zip(('upstream217','selector_proposal'),(baseline,candidate),trees):
        ar,checks=graph_arithmetic(rows); iv=graph_intervals(rows)
        require(ar==iv, 'Independent CFG disagreement')
        graphs.append(ar);controls.append(dict(name=name,source_sha256=sha(compact(rows)),metrics=metrics(t),no_stray_suffix_checks=checks))
    require(graphs[0]==graphs[1], 'Complete guarded ordinal CFG differs')
    nodes=[]; ids={}
    def intern(n):
        if n not in ids:ids[n]=len(nodes);nodes.append(n)
        return ids[n]
    def freeze(t):return intern(t if leaf(t)else(freeze(t[0]),freeze(t[1])))
    oldroot=freeze(trees[0]); count=len(nodes);newroot=freeze(trees[1])
    recipe=dict(baseline_sha256=sha(baseline_raw),candidate_sha256=sha(candidate_raw),candidate_canonical_sha256=sha(compact(candidate)),baseline_nodes=count,baseline_root=oldroot,new_nodes=nodes[count:],candidate_root=newroot)
    replay=nodes[:count]
    for n in recipe['new_nodes']:
        require(all(type(x)is int and 0<=x<len(replay)for x in n),'Invalid recipe edge')
        replay.append(tuple(n))
    @cache
    def thaw(n):return replay[n]if leaf(replay[n])else tuple(thaw(ch)for ch in replay[n])
    require(compact(sites(thaw(newroot)))==compact(candidate),'Exact canonical source recipe replay failed')
    def intervals(t,p='',lo=0):
        hi=lo+len(sites(t)); result={(lo,hi):(p,t)}
        if not leaf(t):
            result.update(intervals(t[0],p+'0',lo));result.update(intervals(t[1],p+'1',lo+len(sites(t[0]))))
        return result
    oldiv,newiv=map(intervals,trees)
    require(newiv[187,228][1]==oldiv[187,228][1], 'Existing213 selector changed')
    selector=newiv[412,4586][1]
    require(selector==(newiv[412,4574][1],newiv[4574,4586][1]), 'Desired provider siblings missing')
    require(selector[0][0]==oldiv[412,466][1], 'Left trigger continuation differs')
    require(selector[1][0]==oldiv[4574,4584][1], 'Right trigger continuation differs')
    correspondence=dict(schema='ORDINAL_REGISTER_STORE_IDENTITY_V1',columns=['ordinal','upstream_PC','candidate_PC','operation','argument','guarded_target_ordinals'],rows=[[i,baseline[i][0],candidate[i][0],*candidate[i][1:],graphs[0][i][1]]for i in range(len(candidate))])
    (out/'recipe.json').write_bytes(compact(recipe));(out/'ordinal_correspondence.json').write_bytes(compact(correspondence))
    report=dict(status='ALL_NATURAL_SOURCE_BISIMULATION_PASS',candidate_raw_source_sha256=sha(candidate_raw),candidate_canonical_source_sha256=sha(compact(candidate)),raw_input_serialization_bound=True,stages=controls,guarded_successors=sum(len(x[1])for x in graphs[0]),complete_guarded_CFG_sha256=sha(compact(graphs[0])),recipe_sha256=sha(compact(recipe)),correspondence_sha256=sha(compact(correspondence)),verifier_sha256=sha(Path(__file__).read_bytes()),selector_span=[412,4586],provider_spans=[[412,4574],[4574,4586]],first37_and_nonAX_unchanged=True,theorem='For every primitive ordinal and every nine-tuple of natural-register values, relate the two source configurations by identical ordinal and register store. Equal operations and operands give equal guards, updates and halt decisions. The exhaustive equality of every guarded successor gives equal next ordinals. This is a strong step-for-step bisimulation, and therefore preserves halting from every corresponding source configuration, without a bound on register values or run length.',scope='SOURCE ONLY. No physical allocation, state count, primitive microcode, blank startup, or foundational equiconsistency conclusion is certified by this source receipt.')
    dump(out/'verification.json',report);print(json.dumps(report,indent=2))

if __name__=='__main__':main()
