#!/usr/bin/env python3
"""Bounded source-only pricing of K/S + Q-double-negation elimination.

This measures closed source splices. It does not certify enumeration,
primitive runtime, startup, or a binary machine consistency theorem.
"""
import argparse, collections, hashlib, itertools, json, sys, time
from pathlib import Path
sys.dont_write_bytecode = True
import source_language as s
import build221 as b
import measure_pinned as m

def combine(ts, shape):
    if len(ts) == 1: return ts[0]
    k = 1 if shape == 'right' else len(ts)-1 if shape == 'left' else len(ts)//2
    return combine(ts[:k], shape), combine(ts[k:], shape)

def rename(t, mapping):
    if not isinstance(t, tuple): return mapping.get(t, t)
    return t[0], rename(t[1], mapping), rename(t[2], mapping)

def postfix(t):
    if not isinstance(t, tuple): return [t]
    return postfix(t[1]) + postfix(t[2]) + [t[0]]

def decode(word):
    stack = []
    for x in word:
        if x in ('I', 'Q'):
            rhs, lhs = stack.pop(), stack.pop()
            stack.append((x, lhs, rhs))
        else: stack.append(x)
    assert len(stack) == 1
    return stack[0]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seed', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--baseline', type=int, choices=[218,219], default=218)
    args = ap.parse_args()
    assert not args.out.exists()
    args.out.mkdir()
    sources = {}
    for name, pin in [('source_language.py', m.PINS['source_language.py']), ('build221.py', m.PINS['build221.py'])]:
        raw = Path(__file__).with_name(name).read_bytes()
        assert m.sha(raw) == pin
        sources[name] = pin
    src_path = args.seed/f'sites{args.baseline}.json'
    tab_path = args.seed/f'k{args.baseline}.native.tm'
    src_raw, tab_raw = src_path.read_bytes(), tab_path.read_bytes()
    if args.baseline == 218:
        assert m.sha(src_raw) == 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'
        assert m.sha(tab_raw) == '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
    else:
        assert m.sha(src_raw) == m.PINS['sites219.json']
        assert m.sha(tab_raw) == m.PINS['k219.native.tm']
    tree = s.tree(json.loads(src_raw)); table = b.read_table(tab_raw)
    groups, _ = b.decoder_map(table, tree)
    q = lambda k: b.sole(groups, k)
    imp, neg, inc = q(90), q(184), ('CI',1)
    macros = {'a':q(98), 'b':q(12), 'c':q(166), 1:neg[0], 'I':imp, 'Q':(imp,(inc,inc))}
    assert all(s.boundary(x) == (0,0,False) for x in macros.values())
    I = lambda x,y: ('I',x,y)
    Q = lambda x,y: ('Q',x,y)
    N = lambda x: I(x,1)
    a,bb,c = 'a','b','c'
    forms = [I(a,I(bb,a)), I(I(a,I(bb,c)),I(I(a,bb),I(a,c))), I(N(N(Q(a,bb))),Q(a,bb))]
    identical, im = m.compile_tree(s,b,table,tree,tree)
    assert identical == table and im['working_states'] == args.baseline
    assert len(m.flat(tree)) == 4744
    start = time.monotonic(); best = 999; kept = []; census = collections.Counter(); count = 0
    perms = list(itertools.permutations('abc'))
    for pp in itertools.product(perms,repeat=3):
        fs = [rename(f,dict(zip('abc',p))) for f,p in zip(forms,pp)]
        words = [postfix(f) for f in fs]
        assert [decode(w) for w in words] == fs
        for shape in ['right','left','balanced']:
            blocks = [combine([macros[x] for x in w],shape) for w in words]
            assert all(s.boundary(x) == (0,0,False) for x in blocks)
            for order in itertools.permutations(range(3)):
                new = combine([blocks[i] for i in order],shape)
                variant = m.splice(s,tree,135,486,new)
                met = s.metrics(variant); count += 1
                score = met['dag_nodes']; census[(score,met['maximum_zero_run'])] += 1
                if score < best:
                    best = score
                    print('BEST',count,pp,shape,order,met,'seconds',round(time.monotonic()-start,3),flush=True)
                if met['maximum_zero_run'] <= 6:
                    key = (score, met['maximum_depth'])
                    info = dict(permutations=pp,order=order,shape=shape,source_metrics=met,postfix=[words[i] for i in order])
                    if len(kept)<8 or key < kept[-1][0]:
                        kept.append((key,info,variant)); kept.sort(key=lambda x:x[0]); kept = kept[:8]
    for i,(_,info,variant) in enumerate(kept):
        path = args.out/f'candidate{i:03}'; path.mkdir()
        rows = s.sites(variant)
        assert s.graph_arithmetic(rows)[0] == s.graph_intervals(rows)
        (path/'sites.json').write_bytes(s.compact(rows))
        try:
            tt,cm = m.compile_tree(s,b,table,tree,variant)
            info['compiler'] = cm
            (path/'raw.tm').write_bytes(b.table_bytes(tt))
        except (ValueError,KeyError,AssertionError) as err:
            info['compiler_error'] = repr(err)
        m.dump(path/'receipt.json',info)
        print('RETAIN',i,info.get('compiler',info.get('compiler_error')),flush=True)
    result = dict(status='BOUNDED_SOURCE_PRICING_COMPLETE',seed=args.baseline,
        source_sha256=m.sha(src_raw), table_sha256=m.sha(tab_raw),utility_pins=sources,
        trials=count, seconds=time.monotonic()-start,best_dag_nodes=best,
        histogram=[dict(dag_nodes=x,maximum_zero_run=y,count=z) for (x,y),z in sorted(census.items())],
        identity_compiler_control=im,baseline_metrics=s.metrics(tree),
        replaced_interval=[135,486],old_AX_output_count=10,new_AX_output_count=12,
        scope='Closed source splices, exact symbolic postfix, two CFG resolvers and exploratory decoder-prefix table allocation only. No enumerator, primitive runtime, startup, or whole-machine consistency proof.')
    assert count == 3888
    m.dump(args.out/'result.json',result)
    print(json.dumps(result),flush=True)

if __name__ == '__main__': main()
