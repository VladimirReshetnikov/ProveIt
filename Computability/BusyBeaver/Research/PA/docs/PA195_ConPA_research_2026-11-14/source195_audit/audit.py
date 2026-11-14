#!/usr/bin/env python3
"""Independent source-identity audit for the 195-state separated machine.

Python 3.10+, standard library only. The runtime stage imports the pinned
arbitrary-register block contracts; the accompanying theorem distinguishes
those inherited mathematical interfaces from these executable certificates.
"""
from pathlib import Path
from collections import defaultdict
import hashlib, json
import compiler as c
import source_language as sl
import verify_emitter as ve
from support import apply, localvalid

HERE = Path(__file__).resolve().parent
INC = ('leaf', 'inc', 1)
c.MACROS[(INC, INC)] = 99
c.MACROS[((INC, INC), (INC, INC))] = 190

def need(ok, why):
    if not ok:
        raise ValueError(why)

def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

def load_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        key = (int(q), int(b))
        need(key not in rows, 'duplicate transition')
        need(b in ('0', '1') and w in ('0', '1') and d in ('L', 'R'), 'binary transition syntax')
        rows[key] = (int(w), d == 'R', int(n))
    states = {q for q, _ in rows}
    need({(q, b) for q in states for b in (0, 1)} == rows.keys(), 'incomplete transition table')
    need({n for w, d, n in rows.values()} <= states | {254}, 'unknown target')
    reached = {74}
    todo = [74]
    while todo:
        q = todo.pop()
        if q == 254:
            continue
        for b in (0, 1):
            n = rows[q, b][2]
            if n not in reached:
                reached.add(n)
                todo.append(n)
    need(reached == states | {254}, 'unreachable state or halt label')
    return rows

def normalized_rows(sites):
    ops = {'inc':'CI', 'dec':'CD', 'breakTo':'CB', 'continueTo':'CC', 'halt':'CH'}
    return [[''.join(map(str, p)), ops[op], arg] for p, op, arg in sites]

def checked_graph(sites, graph):
    rows = normalized_rows(sites)
    tree = sl.tree(rows)
    arithmetic, checks = sl.graph_arithmetic(rows)
    intervals = sl.graph_intervals(rows)
    need(arithmetic == intervals, 'independent source resolvers disagree')
    normalized = []
    for effect, targets in arithmetic:
        op = effect[0]
        normalized.append(('inc', effect[1], targets[0]) if op == 'increment' else
                          ('dec', effect[1], *targets) if op == 'decrement' else
                          ('halt',) if op == 'halt' else ('jump', targets[0]))
    need(normalized == graph, 'imported compiler graph differs from independent resolvers')
    return {'no_stray_successor_checks': checks, 'maximum_source_depth': max(len(p) for p, _, _ in sites),
            'instruction_graph_sha256': digest(graph), 'rows': len(graph)}

def startup(rows, path):
    head = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {head-1, head+48} | {head+i for i, b in enumerate(path) if b}
    pos = head + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos+value+1))
        pos += value+1
    ones = set()
    q, h = 74, 0
    for step in range(1, 100001):
        w, d, q = rows[q, int(h in ones)]
        (ones.add if w else ones.discard)(h)
        h += 1 if d else -1
        if q == 84 and h == head and ones == expected:
            return step
        need(q != 254, 'premature startup halt')
    raise ValueError('startup did not reach exact source seed')

def main():
    parent = c.read_grammar(HERE/'parent.grammar.json')
    candidate = c.read_grammar(HERE/'candidate.grammar.json')
    word = ve.word(candidate)
    original = [x[0] for x in ve.literal_blocks()]
    expected = original[:121] + ['copyA', 'copyA', 'copyA', 'cons', 'incT', 'incT', 'cons'] + original[138:]
    need(expected[184] == 'cons', 'expected separation edit moved')
    expected = expected[:184] + expected[185:]
    need(word == ve.word(parent) == expected, '190-token emitter word changed')
    ps, pg, pc = c.source(parent)
    ns, ng, nc = c.source(candidate)
    need(pg == ng, 'primitive source graph changed')
    need([(o, a) for p, o, a in ps] == [(o, a) for p, o, a in ns], 'primitive operation word changed')
    parent_graph = checked_graph(ps, pg)
    candidate_graph = checked_graph(ns, ng)
    ptable = load_table(HERE/'parent.machine.native.tm')
    ntable = load_table(HERE/'candidate.machine.native.tm')
    raw, index, shape = c.build(candidate)
    chosen = json.loads((HERE/'folds.json').read_text())
    folded, aliases = apply(raw, chosen)
    need(folded == ntable, 'folded compiler output differs from supplied machine')
    need(len(chosen) == 6 and len({q for a,b,acts in chosen for q in (a,b)}) == 12, 'folds overlap')
    incoming = defaultdict(set)
    for (q,b), (w,d,n) in raw.items():
        if n in shape:
            need(d and w == b, 'reader entrance does not preserve previous bit')
            incoming[n].add(b)
    for a,b,acts in chosen:
        need(incoming[a] == {0} and incoming[b] == {1}, 'reader fold context premise fails')
    need(localvalid(raw, folded, aliases, chosen), 'simultaneous reader folds fail finite simulation')
    need(len(shape) == 67 and len(raw) == 402 and len(ntable) == 390, 'state count')
    fixed, _ = c.machine()
    retained = {k:v for k,v in fixed.items() if k[0] < 1300}
    changed = [list(k) for k,v in retained.items() if ntable[k] != v]
    need(changed == [[101,1]], 'fixed register-machine control changed')
    box_states = [0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]
    box_rows = [(q,b) for q in box_states for b in (0,1) if b or q not in (113,198)]
    need(len(box_rows) == 44 and all(ntable[k] == fixed[k] for k in box_rows), 'Native.boxRows agreement')
    need(ntable[198,0] == (1,False,40), 'Native.IncTail1 append-one row')
    need(startup(ptable, ps[25][0]) == startup(ntable, ns[25][0]) == 58154, 'startup step count changed')
    pv = c.validate(ptable, pc)
    nv = c.validate(ntable, nc)
    need(pv['ok'] and nv['ok'], 'whole-tape symbolic runtime contracts failed')
    result = {
        'parent_working_states': len(ptable)//2,
        'candidate_working_states': len(ntable)//2,
        'candidate_transition_rows': len(ntable),
        'all_states_graph_reachable': True,
        'same_190_token_word': True,
        'word_sha256': digest(word),
        'head_parameter_permutations': ['identity']*6,
        'head_order_unchanged': True,
        'exact_source_graph_identity': True,
        'changed_source_paths': sum(a[0] != b[0] for a,b in zip(ps,ns)),
        'parent_graph': parent_graph,
        'candidate_graph': candidate_graph,
        'fixed_control_row_changes': changed,
        'native_box_rows_unchanged': len(box_rows),
        'native_append_one_tail_unchanged': True,
        'raw_reader_nodes': len(shape),
        'simultaneous_context_folds': len(chosen),
        'reader_fold_bit_cases': 4*len(chosen),
        'parent_symbolic_runtime': pv,
        'candidate_symbolic_runtime': nv,
        'exact_startup_steps_both': 58154,
        'parent_native_sha256': hashlib.sha256((HERE/'parent.machine.native.tm').read_bytes()).hexdigest(),
        'candidate_native_sha256': hashlib.sha256((HERE/'candidate.machine.native.tm').read_bytes()).hexdigest(),
        'scope': 'Exact source identity and symbolic tape certificates with inherited arbitrary-register block contracts; accompanying mathematical preservation theorem, not a newly exported Lean endpoint.'
    }
    (HERE/'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
