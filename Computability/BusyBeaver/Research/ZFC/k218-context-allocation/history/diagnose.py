"""Bounded decoder failure localization; no primitive or startup claim."""
from pathlib import Path
from collections import defaultdict
import sys, json
sys.dont_write_bytecode = True
P = Path('/tmp/k218-qs-span-dp')
sys.path.insert(0, str(P))
import source_language as s, build221 as b, measure_pinned as m, global_allocator_v2 as g
OUT = Path(__file__).resolve().parent
suffix = '-protected' if '--protected' in sys.argv else ''
protection = frozenset(json.loads((OUT/'protected-result.json').read_text())['protected_states']) if suffix else frozenset()
plan = json.loads((P/'input.json').read_text())
seed = Path(plan['seed'])
old = s.tree(json.loads((seed/'sites218.json').read_text()))
new = s.tree(json.loads((P/'verified/candidate000/sites.json').read_text()))
table = b.read_table((seed/'k218.native.tm').read_bytes())
original_decoder = b.decoder_map
old_groups, old_paths = original_decoder(table,old)
results = []
seen_mismatch = set()

def diagnostic_decoder(T, tree):
    if tree == old:
        return original_decoder(T, tree)
    (OUT/('attempted-global'+suffix+'.tm')).write_bytes(b.table_bytes(T))
    groups, paths = defaultdict(set), defaultdict(list)
    def walk(node, prefix, state, ancestors=()):
        if s.leaf(node): return
        if state != 84 and state in old_groups and node not in old_groups[state] and all(T[state,k]==table[state,k] for k in (0,1)) and state not in seen_mismatch:
            seen_mismatch.add(state)
            results.append({'unexpected_unchanged_state':state,'prefix':prefix,'old_paths':old_paths[state], 'expected_node':node, 'old_nodes':list(old_groups[state])})
        groups[state].add(node); paths[state].append(prefix)
        for bit in (0,1):
            if s.leaf(node[bit]): continue
            tape = {i:int(value) for i,value in enumerate(prefix+str(bit))}
            tape[-1]=1; before=dict(tape); head=len(prefix); q=state; trace=[]
            err=None
            for tick in range(100):
                if head==len(prefix)+1: break
                if head not in tape:
                    err='outside prefix'; break
                read=tape[head]; action=T[q,read]
                trace.append([q,head,read,list(action)])
                w,d,q=action; tape[head]=w; head+=d
            if err or tape!=before or head!=len(prefix)+1:
                fail={'state':state,'prefix':prefix,'bit':bit,'trace':trace,'ancestors':ancestors,
                      'head':head,'end_state':q,'error':err,
                      'changed_cells':[[i,before.get(i),tape.get(i)] for i in set(tape)|set(before) if tape.get(i)!=before.get(i)],
                      'subtree':node,'child':node[bit], 'attempted_states':len(T)//2}
                results.append(fail)
                raise ValueError('diagnostic localized prefix failure')
            walk(node[bit],prefix+str(bit),q,ancestors+((state,prefix,bit,trace),))
    walk(tree,'',84)
    return groups,paths

b.decoder_map=diagnostic_decoder
try:
    _,receipt=g.compile_tree(s,b,table,old,new,protected_states=protection)
    results.append({'status':'pass','receipt':receipt})
except (ValueError,AssertionError,KeyError) as e:
    results.append({'error':repr(e)})
(OUT/('result'+suffix+'.json')).write_text(json.dumps(results,indent=2)+'\n')
for r in results:
    print(json.dumps({k:v for k,v in r.items() if k not in ('subtree','child','expected_node','old_nodes')}))
