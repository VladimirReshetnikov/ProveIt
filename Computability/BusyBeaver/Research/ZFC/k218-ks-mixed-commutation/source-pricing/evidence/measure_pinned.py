#!/usr/bin/env python3
"""Pinned, bounded K219 pivot-fusion source experiment, not a machine proof.

Imports only two pinned, reviewed pure K221 utility modules. No supplied
main, optimizer, runtime engine, network operation, or proof assistant runs.
"""
from pathlib import Path
from functools import cache
from collections import Counter, defaultdict
import argparse
import hashlib
import importlib
import itertools
import json
import sys

PINS = {
    'source_language.py': '4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
    'build221.py': '3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
    'sites219.json': '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',
    'k219.native.tm': 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26',
}

def sha(raw): return hashlib.sha256(raw).hexdigest()
def require(x, message):
    if not x: raise ValueError(message)
def dump(path, value): path.write_text(json.dumps(value, indent=2) + '\n')

@cache
def flat(n): return (n,) if isinstance(n[0], str) else flat(n[0]) + flat(n[1])

def serial(nodes):
    require(bool(nodes), 'Empty sequence')
    out = nodes[-1]
    for n in reversed(nodes[:-1]): out = n, out
    return out

def rename(t, mp):
    if isinstance(t[0], str):
        op, arg = t
        return op, mp.get(arg, arg) if op in ('CI', 'CD') else arg
    return tuple(rename(x, mp) for x in t)

def splice(s, tree, lo, hi, new):
    """Replace an exact consecutive forest of closed factors; prune empty arms."""
    used = []
    def walk(t, i=0):
        j = i + len(flat(t))
        if j <= lo or i >= hi: return t
        if lo <= i and j <= hi:
            require(s.boundary(t) == (0, 0, False), ('Open splice', i, j))
            if i == lo:
                used.append(i)
                return new
            return None
        require(not s.leaf(t), ('Partial leaf', i, j))
        a, b = walk(t[0], i), walk(t[1], i + len(flat(t[0])))
        return b if a is None else a if b is None else (a, b)
    out = walk(tree)
    require(used == [lo], ('Missing exact splice start', lo, hi, used))
    return out

def run_macro(s, node, registers, limit=500000):
    rows = s.sites((node, ('CH', None)))
    graph = s.graph_arithmetic(rows)[0]
    require(graph == s.graph_intervals(rows), 'Independent macro CFG mismatch')
    r = list(registers); pc = 0
    for step in range(limit):
        effect, targets = graph[pc]
        if effect[0] == 'halt': return r, step
        if effect[0] == 'increment': r[effect[1]] += 1; pc = targets[0]
        elif effect[0] == 'decrement':
            v = r[effect[1]]; r[effect[1]] = max(0, v-1); pc = targets[bool(v)]
        else: pc = targets[0]
    raise RuntimeError(('Finite macro diagnostic limit', registers))

def compile_tree(s, b, table, old_src, new_src):
    """Incremental exploratory allocator, adapted from K220 recompile.py.

    K219 has one duplicated subtree role. Unlike the older function-valued
    validator, unchanged nodes may resolve to any of their exact old states.
    This is a decoder-prefix check only, never a primitive/runtime proof.
    """
    groups, _ = b.decoder_map(table, old_src)
    old_states = defaultdict(set)
    for q, nodes in groups.items():
        for n in nodes: old_states[n].add(q)
    node_state = {n: min(qs) for n, qs in old_states.items()}
    live = set()
    def visit(n):
        if s.leaf(n) or n in live: return
        live.add(n); visit(n[0]); visit(n[1])
    visit(new_src)
    origins = {}
    def walk(n, o):
        if s.leaf(n) or o is None or s.leaf(o): return
        if n != o: origins.setdefault(n, o)
        walk(n[0], o[0]); walk(n[1], o[1])
    walk(new_src, old_src)
    origins = {n: o for n, o in origins.items() if o not in live}
    compiled = dict(table); mapped = dict(node_state); mapped[new_src] = 84
    claimed = {84: new_src}; fresh = max(300, max(q for q, _ in table)+1)
    nextfresh = fresh; reused = 0; leaves = {}
    for op in ['CI', 'CD', 'CC', 'CB', 'CH']:
        for arg in ([None] if op == 'CH' else range(10)):
            ch = op, arg
            for bit in (0, 1):
                choices = Counter(table[q, bit] for n, qs in old_states.items() for q in qs if n[bit] == ch)
                direct = [a for a in choices if a[:2] == (bit, 1)]
                if len(direct) == 1: leaves[ch, bit] = direct[0]
                elif ch == ('CC', 1) and bit == 1: leaves[ch, bit] = (0, -1, 1)
                elif ch == ('CC', 2) and bit == 1: leaves[ch, bit] = (0, -1, 16)
                elif ch == ('CB', 1) and bit == 1: leaves[ch, bit] = (0, -1, 40)
    def go(n):
        nonlocal fresh, reused
        if n in mapped: return mapped[n]
        if n in origins and origins[n] in node_state and len(groups[node_state[origins[n]]]) == 1 and node_state[origins[n]] not in claimed:
            q = node_state[origins[n]]; reused += 1
        else: q = fresh; fresh += 1
        mapped[n] = q; claimed[q] = n
        for bit, ch in enumerate(n):
            if not s.leaf(ch): compiled[q, bit] = (bit, 1, go(ch))
            elif n in origins and origins[n] in node_state and origins[n][bit] == ch:
                compiled[q, bit] = table[node_state[origins[n]], bit]
            elif (ch, bit) in leaves: compiled[q, bit] = leaves[ch, bit]
            else: raise ValueError(('No generic leaf entry', ch, bit, q))
        return q
    for bit, ch in enumerate(new_src):
        compiled[84, bit] = (bit, 1, go(ch)) if not s.leaf(ch) else leaves[ch, bit]
    reach = {0}; todo = [0]
    for q in todo:
        for bit in (0, 1):
            z = compiled[q, bit][2]
            if z != 254 and z not in reach: reach.add(z); todo.append(z)
    compiled = {k: v for k, v in compiled.items() if k[0] in reach}
    gg, _ = b.decoder_map(compiled, new_src)
    for q, nodes in gg.items():
        for n in nodes:
            permitted = old_states[n] if n in old_states and n != new_src else {mapped[n]}
            require(q in permitted, ('Node binding mismatch', q, sorted(permitted)))
    return compiled, {'working_states': len(compiled)//2, 'fresh': fresh-nextfresh,
        'reused': reused, 'aliases': sum(len(ns)-1 for ns in gg.values()),
        'decoder_states': len(gg), 'interior_roles': sum(map(len, gg.values())),
        'scope': 'Raw table and exact decoder-prefix binding only; no runtime or startup validation.'}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k219', type=Path, required=True)
    ap.add_argument('--k221', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
    require(not a.out.exists(), 'Output must be fresh')
    library = a.k221/'portable'
    inputs = {}
    for root, names in [(library, ['source_language.py','build221.py']), (a.k219, ['sites219.json','k219.native.tm'])]:
        for name in names:
            p = root/name; h = sha(p.read_bytes()); require(h == PINS[name], ('Input identity', p, h))
            inputs[name] = {'path': str(p.resolve()), 'sha256': h}
    sys.dont_write_bytecode = True; sys.path.insert(0, str(library.resolve()))
    s = importlib.import_module('source_language'); b = importlib.import_module('build221')
    rows = json.loads((a.k219/'sites219.json').read_text()); tree = s.tree(rows)
    table = b.read_table((a.k219/'k219.native.tm').read_bytes()); groups, _ = b.decoder_map(table, tree)
    q = lambda k: b.sole(groups, k)
    push = q(98)[0]; imp = q(90); inc = ('CI', 1)
    macros = {'a':q(98), 'b':q(12), 'c':q(166),
              'u':rename(q(98), {4:0}), 'I':imp, 'R':(imp,inc),
              'Q':(imp,(inc,inc)), 'E':(imp,((inc,inc),inc))}
    pair = lambda x,y: (x+y)*(x+y+1)//2+y
    # Existing inverse-Cantor core returns first field in scratch6 and tail in8.
    pop8 = rename(imp[0], {2:8})
    move = lambda src,dst: (('CD',src),(('CI',dst),('CC',2)))
    save = serial([rename(push,{1:0,2:8}), move(1,0), rename(q(98)[1],{4:0})])
    restore = serial([(('CD',0),('CC',1)), pop8, move(6,0)])
    require(all(s.boundary(n)==(0,0,False) for n in [push,save,restore,*macros.values()]), 'Macro is open')
    require(flat(tree)[194:221] == flat(imp), 'rho8 first implication interval')
    require(flat(tree)[4536:4563] == flat(imp), 'Final bundle implication interval')
    old_v = ['a','b','R','c','a','b','R','Q','I']
    old_rho5 = ['c','a','E','c','b','R','a','b','R','I','I']
    new_m = ['u','a','E','u','b','R','c','a','b','R','Q','I','I']
    require(flat(serial([macros[x] for x in old_v])) == flat(tree)[2650:2892], 'Exact V word')
    require(flat(serial([macros[x] for x in old_rho5])) == flat(tree)[1178:1474], 'Exact rho5 word')
    def symbolic(word):
        st=[]
        for x in word:
            if x in ('a','b','c','u'): st.append(x)
            else:
                rhs,lhs=st.pop(),st.pop();st.append((x,lhs,rhs))
        require(len(st)==1,'Postfix stack');return st[0]
    expected_m=('I',('E','u','a'),('I',('R','u','b'),('Q','c',('R','a','b'))))
    require(symbolic(new_m)==expected_m,'Fused formula')
    primitive_checks=0;max_steps=0
    for np,u,tail in itertools.product(range(5),repeat=3):
        regs=[np,u,17,4,6,8,0,0,tail]
        got,steps=run_macro(s,save,regs)
        want=regs.copy();want[0]=u;want[8]=pair(np,tail)
        require(got==want,('Save contract',regs,got,want))
        # Formula construction may change top/stack but leaves this saved state.
        got[1],got[2]=23,29
        restored,steps2=run_macro(s,restore,got)
        want=got.copy();want[0]=np;want[8]=tail
        require(restored==want,('Restore contract',got,restored,want))
        primitive_checks+=2;max_steps=max(max_steps,steps,steps2)
    # Descending original intervals avoid reindexing later source fragments.
    changed=splice(s,tree,4536,4563,(imp,restore))
    changed=splice(s,changed,2650,2892,serial([macros[x] for x in new_m]))
    changed=splice(s,changed,1178,1474,push)
    changed=splice(s,changed,194,221,(save,imp))
    rr=s.sites(changed);graph=s.graph_arithmetic(rr)[0]
    require(graph==s.graph_intervals(rr),'Independent complete CFG mismatch')
    require(len(rr)==4621,'Predicted exact primitive census')
    # Identity must retain exact K219 bytes despite the duplicated old role.
    identity,im=compile_tree(s,b,table,tree,tree)
    require(identity==table and im['working_states']==219,'Compiler baseline control')
    a.out.mkdir(parents=True)
    (a.out/'sites.json').write_bytes(s.compact(rr))
    dump(a.out/'save-u.json',save);dump(a.out/'restore-cache.json',restore)
    result={'status':'SOURCE_VARIANT_MEASURED', 'inputs':inputs,
      'source_sha256':sha(s.compact(rr)), 'baseline_metrics':s.metrics(tree),
      'source_metrics':s.metrics(changed), 'postfix_M':new_m, 'formula_M':expected_m,
      'source_change':'rho5 slot becomes truth0; V in final gated bundle becomes M; cache0 temporarily holds u while old cache is paired into proof-data8.',
      'extra_proof_fields':0,'AX_output_count_unchanged':True,
      'gate':'Original c!=a,b gate remains byte-identical outside moved closed factors; u is not compared.',
      'finite_primitive_contract_tests':primitive_checks,'maximum_test_steps':max_steps,
      'save_primitives':len(flat(save)),'restore_primitives':len(flat(restore)),
      'truth_stub_primitives':len(flat(push)), 'baseline_compiler_control':im,
      'source_limits':'Independent CFG equality, closed splice binding, symbolic postfix and finite macro tests; all-natural macro algebra described separately.',
      'candidate_scope':'No primitive-runtime, startup, Lean/Rocq or exact-machine calibration claim.'}
    try:
        tt,m=compile_tree(s,b,table,tree,changed);result['compiler']=m
        (a.out/'raw-candidate.tm').write_bytes(b.table_bytes(tt))
    except (ValueError,KeyError,AssertionError) as e:
        result['compiler_error']=repr(e)
    require(all(sha(Path(d['path']).read_bytes())==d['sha256'] for d in inputs.values()),'Input changed')
    dump(a.out/'result.json',result)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
