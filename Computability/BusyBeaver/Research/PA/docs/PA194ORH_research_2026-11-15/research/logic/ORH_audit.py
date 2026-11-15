#!/usr/bin/env python3
"""Independent finite audit of PA194ORH's changed selector and source.

No construction compiler, symbolic executor, or proof-checker is imported.
This is a finite certificate check, not a Lean proof.
"""
from pathlib import Path
from bisect import bisect_left, bisect_right
import argparse
import hashlib
import json

BASE = Path(__file__).resolve().parents[2]
PACKET = BASE / 'machines/PA194ORH'
PARENT = BASE / 'reference/AX11H_machine'
BOXSTATES = {0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}

def table(path):
    out = {}
    for line in path.read_text().splitlines():
        q,b,w,d,n = line.split()
        key = int(q),int(b)
        assert key not in out
        out[key] = int(w), (1 if d == 'R' else -1), int(n)
    return out

def walk(t, nodes, rules, path='', leaves=None):
    if leaves is None:
        leaves = []
    if isinstance(t, str):
        if t == 'x67':
            t = rules['@root']
        return walk(rules[t] if t in rules else nodes[t], nodes, rules, path, leaves)
    if t[0] == 'leaf':
        leaves.append((path, t[1], t[2]))
    else:
        assert len(t) == 2
        walk(t[0], nodes, rules, path+'0', leaves)
        walk(t[1], nodes, rules, path+'1', leaves)
    return leaves

def source(nodes, grammar):
    rules = dict(grammar['rules'])
    rules['@root'] = grammar['root']
    leaves = walk('node172', nodes, rules)
    paths = [p for p,_,_ in leaves]
    assert paths == sorted(paths) and len(paths) == len(set(paths))
    def ancestor(p, bit, k):
        matches = [i for i,c in enumerate(p) if c == bit]
        assert 0 < k <= len(matches)
        return p[:matches[-k]]
    instructions = []
    for i,(p,op,arg) in enumerate(leaves):
        if op == 'inc':
            ins = ['inc',arg,i+1]
        elif op == 'dec':
            prefix = ancestor(p,'0',1)
            ins = ['dec',arg,bisect_right(paths,prefix+'2'),i+1]
        elif op == 'breakTo':
            prefix = ancestor(p,'0',arg)
            ins = ['jump',bisect_right(paths,prefix+'2')]
        elif op == 'continueTo':
            prefix = ancestor(p,'1',arg)
            ins = ['jump',bisect_left(paths,prefix)]
        else:
            assert op == 'halt'
            ins = ['halt']
        instructions.append(ins)
    for ins in instructions:
        targets = ins[2:] if ins[0] in ('inc','dec') else ins[1:]
        assert all(0 <= i < len(leaves) for i in targets)
    return leaves,instructions

def trace(rows,q,tape,steps):
    tape = dict(tape)
    head = 0
    history = []
    for _ in range(steps):
        bit = tape.get(head,0)
        history.append([q,head,bit])
        w,d,q = rows[q,bit]
        tape[head] = w
        head += d
    return q,head,{i:b for i,b in tape.items() if b},history

def main():
    global PACKET, PARENT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=PACKET,
                        help='directory containing ORH literal tables, nodes, sites and instructions')
    parser.add_argument('--parent',type=Path,default=PARENT,
                        help='directory containing parent nodes.json and grammar.json')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('ORH_audit.json'))
    args = parser.parse_args()
    PACKET, PARENT = args.packet, args.parent
    old = table(PACKET/'parent.native.tm')
    new = table(PACKET/'machine.native.tm')
    assert len(old) == len(new) == 388
    assert all(old[q,b] == new[q,b] for q in BOXSTATES for b in (0,1))
    changed = sorted({q for q,b in set(old)|set(new) if old.get((q,b)) != new.get((q,b))})
    assert not BOXSTATES.intersection(changed)
    fixed_changed = [q for q in changed if q < 1300]
    assert fixed_changed == [69,92,185,213,333]
    histories = []
    for history_bit in (0,1):
        # The four displayed distant cells certify they remain untouched.
        tape = {-3:1,-2:1,-1:history_bit,0:0,1:1,2:1}
        duration = 3-history_bit
        a = trace(old,69,tape,duration)
        b = trace(new,69,tape,duration)
        assert a[:3] == b[:3]
        assert a[2] == {i:x for i,x in tape.items() if x}
        histories.append({'history_bit':history_bit,'old':a[3],'new':b[3],
                          'exit_state':a[0],'exit_head':a[1],'steps':duration})
    dispatch = []
    for old_word,new_word,target in [('00','0',104),('010','10',107),
                                      ('011','110',98),('1','111',90)]:
        for rows,word in [(old,old_word),(new,new_word)]:
            tape = {i:int(x) for i,x in enumerate(word)}
            result = trace(rows,213,tape,len(word))
            assert result[0] == target and result[1] == len(word)
            assert result[2] == {i:x for i,x in tape.items() if x}
        dispatch.append({'old_word':old_word,'new_word':new_word,'target':target})
    old_nodes = json.loads((PARENT/'nodes.json').read_text())
    new_nodes = json.loads((PACKET/'nodes.json').read_text())
    grammar = json.loads((PARENT/'grammar.json').read_text())
    old_leaves,old_ins = source(old_nodes,grammar)
    new_leaves,new_ins = source(new_nodes,grammar)
    assert old_ins == new_ins == json.loads((PACKET/'instructions.json').read_text())
    assert [list(x) for x in new_leaves] == json.loads((PACKET/'sites.json').read_text())
    assert len(old_leaves) == len(new_leaves) == 3671
    changed_addresses = sum(a[0] != b[0] for a,b in zip(old_leaves,new_leaves))
    assert changed_addresses == 134
    receipt = {'status':'PASS','working_states':194,'transition_rows':388,
        'box_states_checked':len(BOXSTATES),'all_box_rows_identical':True,
        'changed_fixed_controls':fixed_changed,'selector_cases':histories,
        'closed_macro_dispatch':dispatch,'source_sites':len(new_leaves),
        'resolved_instruction_lists_identical':True,'changed_source_addresses':changed_addresses,
        'max_path_length':max(len(p) for p,_,_ in new_leaves),
        'machine_sha256':hashlib.sha256((PACKET/'machine.tm').read_bytes()).hexdigest(),
        'scope':'Independent finite selector, dispatch, box-preservation and source-CFG audit; does not replay the full symbolic runtime or startup.'}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
