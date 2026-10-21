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




BASELINE='8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc'
CANDIDATE='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
RECIPE='47e896480a7b2f6bd44dd3df715a51450a88b7528a3aaa7638aee48f7b0e4987'

def main():
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    home=Path(__file__).resolve().parent
    ap.add_argument('--baseline',type=Path,default=home/'baseline216.compact.json')
    ap.add_argument('--candidate',type=Path,default=home/'source215.compact.json')
    ap.add_argument('--recipe',type=Path,default=home/'recipe.json')
    ap.add_argument('--out',type=Path,default=home/'replay')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    require(__debug__,'Run Python without -O')
    br,cr,rr=a.baseline.read_bytes(),a.candidate.read_bytes(),a.recipe.read_bytes()
    require(sha(br)==BASELINE,'Wrong pinned parent216 source')
    source=json.loads(cr)
    require(sha(compact(source))==CANDIDATE,'Wrong compact candidate215 source')
    require(sha(rr)==RECIPE,'Wrong source recipe')
    parent=json.loads(br);old=tree(parent);new=tree(source);r=json.loads(rr)
    require(r['baseline_sha256']==BASELINE and r['candidate_compact_sha256']==CANDIDATE,'Recipe pins')
    nodes=[];ids={}
    def intern(n):
        if n not in ids:ids[n]=len(nodes);nodes.append(n)
        return ids[n]
    def freeze(t):return intern(t if leaf(t)else(freeze(t[0]),freeze(t[1])))
    oldroot=freeze(old)
    require(oldroot==r['baseline_root'] and len(nodes)==r['baseline_nodes'],'Parent DAG census')
    for node in r['new_nodes']:
        require(len(node)==2 and all(type(x)is int and 0<=x<len(nodes) for x in node),'Non-prior recipe edge')
        nodes.append(tuple(node))
    @cache
    def thaw(i):return nodes[i]if leaf(nodes[i])else tuple(thaw(j)for j in nodes[i])
    built=thaw(r['candidate_root'])
    require(compact(sites(built))==compact(source),'Deterministic reconstruction differs')
    (a.out/'rebuilt_source215.json').write_bytes(compact(sites(built)))
    stages=[];graphs=[]
    for name,data,t in [('parent216',parent,old),('candidate215',source,new)]:
        ar,checks=graph_arithmetic(data);iv=graph_intervals(data)
        require(ar==iv,'Independent all-guard CFG resolvers disagree')
        stages.append({'name':name,'compact_sha256':sha(compact(data)),'metrics':metrics(t),'guarded_successors':sum(len(x[1])for x in ar),'no_stray_suffix_checks':checks})
        graphs.append(ar)
    require(graphs[0]==graphs[1],'Complete primitive-effect/control graph differs')
    require(len(source)==4751 and sum(len(x[1])for x in graphs[0])==6175,'Source census')
    require(sum(x[0]==['halt'] for x in graphs[0])==1,'Unique halt')
    correspondence={'schema':'ORDINAL_REGISTER_STORE_IDENTITY_V1','columns':['ordinal','parent_PC','candidate_PC','effect','guarded_targets'],'rows':[[i,parent[i][0],source[i][0],*graphs[0][i]]for i in range(len(source))]}
    (a.out/'ordinal_correspondence.json').write_bytes(compact(correspondence))
    report={'status':'ALL_NATURAL_SOURCE_BISIMULATION_PASS','stages':stages,'candidate_input_sha256':sha(cr),'recipe_sha256':sha(rr),'new_recipe_nodes':len(r['new_nodes']),'complete_guarded_CFG_sha256':sha(compact(graphs[0])),'correspondence_sha256':sha(compact(correspondence)),'verifier_sha256':sha(Path(__file__).read_bytes()),'theorem':'Relate configurations by identical primitive ordinal and identical arbitrary nine-tuple of natural registers. Equal primitive effects give equal guards, register updates, and halting decisions. Equal exhaustive successor lists give equal successor ordinals. This is a strong step-for-step bisimulation for every register value and every run length.','scope':'Source only. Does not certify physical table, state count, microcode, or blank startup. Foundational equivalence is inherited from the pinned parent216 source calibration.'}
    dump(a.out/'verification.json',report);print(json.dumps(report,indent=2))
if __name__=='__main__':main()
