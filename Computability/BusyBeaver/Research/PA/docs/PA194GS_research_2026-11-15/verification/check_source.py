#!/usr/bin/env python3
"""Independent source binding for the split-gate construction.

No builder, optimizer, machine compiler, or inherited resolver is imported.
This verifies finite source identities; it does not replace literal runtime
certificates or the written iPRA soundness argument.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def grammar(data):
    rules = data['rules']
    def expand(t):
        if isinstance(t, str) and t in rules:
            return [expand(x) for x in rules[t]]
        return t
    return expand(data['root'])


def resolve(nodes, axial):
    """Expand the actual source tree, retaining each ancestor's leaf interval."""
    pending = [('node172', '', False)]
    sites, spans = [], {}
    while pending:
        node, path, closing = pending.pop()
        if closing:
            lo = spans[path][0]
            spans[path] = (lo, len(sites))
            continue
        while isinstance(node, str):
            node = axial if node == 'x67' else nodes[node]
        if node[0] == 'leaf':
            assert len(node) == 3
            spans[path] = (len(sites), len(sites)+1)
            sites.append([path, node[1], node[2]])
        else:
            assert len(node) == 2
            spans[path] = (len(sites), None)
            pending.extend([(None, path, True), (node[1], path+'1', False),
                            (node[0], path+'0', False)])
    count = len(sites)
    instructions = []
    def outward(path, side, level):
        seen = 0
        for length in range(len(path)-1, -1, -1):
            if path[length] == side:
                seen += 1
                if seen == level:
                    lo, hi = spans[path[:length]]
                    target = hi if side == '0' else lo
                    assert 0 <= target < count, ('escaped subtree', path, side, level)
                    return target
        raise AssertionError(('unbound return', path, side, level))
    for i, (path, op, arg) in enumerate(sites):
        if op == 'inc':
            row = [op, arg, i+1]
        elif op == 'dec':
            row = [op, arg, outward(path, '0', 1), i+1]
        elif op == 'breakTo':
            row = ['jump', outward(path, '0', arg)]
        elif op == 'continueTo':
            row = ['jump', outward(path, '1', arg)]
        else:
            assert op == 'halt' and arg is None
            row = ['halt']
        assert all(0 <= target < count for target in
                   (row[2:] if row[0] in ('inc', 'dec') else row[1:])), row
        instructions.append(row)
    return sites, instructions


def check(args):
    parent_nodes = read(args.nodes)
    child_nodes = read(args.candidate/'nodes.json')
    assert parent_nodes == child_nodes, 'This certificate expects an unchanged node dictionary'
    old_sites, old = resolve(parent_nodes, grammar(read(args.grammar)))
    new_sites, new = resolve(child_nodes, read(args.candidate/'tree.json'))
    assert new_sites == read(args.candidate/'sites.json'), 'tree/sites binding'
    assert new == read(args.candidate/'instructions.json'), 'tree/instructions binding'
    assert old == new, 'full resolved source identity'
    assert old_sites[25] == new_sites[25] == ['1000000', 'dec', 8]
    changed = [i for i, (a,b) in enumerate(zip(old_sites, new_sites)) if a[0] != b[0]]
    closed = []
    for name, lo, hi in [('node146',3523,3535), ('node149',3535,3553), ('node49',3553,3572)]:
        exits = []
        for i in range(lo,hi):
            row = new[i]
            targets = row[2:] if row[0] in ('inc','dec') else row[1:]
            for target in targets:
                if not lo <= target < hi:
                    assert target == hi, (name,i,target)
                    exits.append([i,target])
        closed.append({'name':name,'first':lo,'count':hi-lo,'ordinary_exits':exits})
    files = [args.nodes,args.grammar] + [args.candidate/x for x in
              ('nodes.json','tree.json','sites.json','instructions.json')]
    receipt = {'status':'PASS','scope':'Finite exact source binding, not a physical runtime proof',
      'instruction_count':len(new),'instruction_counts':dict(Counter(r[0] for r in new)),
      'source_operations':dict(Counter(r[1] for r in new_sites)),
      'changed_address_count':len(changed),'changed_address_sites':changed,
      'max_old_address_length':max(map(lambda s:len(s[0]),old_sites)),
      'max_new_address_length':max(map(lambda s:len(s[0]),new_sites)),
      'unchanged_initial_site':old_sites[25],'closed_subtrees':closed,
      'files':[{'path':str(p),'sha256':digest(p)} for p in files]}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('status','instruction_count','changed_address_count','closed_subtrees')},indent=2))


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    inp = root/'reference/inputs'
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--nodes',type=Path,default=inp/'AX11H.nodes.json')
    p.add_argument('--grammar',type=Path,default=inp/'AX11H.grammar.json')
    p.add_argument('--candidate',type=Path,default=root/'machine')
    p.add_argument('--output',type=Path,default=root/'verification/source_identity.json')
    check(p.parse_args())
