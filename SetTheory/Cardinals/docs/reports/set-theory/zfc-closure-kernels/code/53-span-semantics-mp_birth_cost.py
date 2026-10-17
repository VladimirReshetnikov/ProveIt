#!/usr/bin/env python3
"""Complete Wade-compiler controls for observing falsity at its first MP birth.

The unchanged source is Mira-Cult's program, Jeff's verified finite DAG and
Wade's MIT-0 compiler, upstream 297ab8df7e5de329605c3875b4934643b371a5e3.
This experiment supplies finite source and table checks, not binary simulation.
"""
from pathlib import Path
import hashlib
import importlib
import json
import sys

BASE = Path(__file__).resolve().parents[1]
REF = Path(__file__).resolve().parent / 'reference'
BACKEND = Path(__file__).resolve().parent / 'backend'
OUT = Path(__file__).resolve().parent / 'mp_birth_results'
sys.path[:0] = [str(REF), str(BACKEND)]
import recover_wade_dag as recover
import TMBuilder as backend

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def reachable(nodes):
    seen, todo = set(), [0]
    while todo:
        q = todo.pop()
        if q in seen: continue
        seen.add(q)
        for e in nodes[q]:
            if e.startswith('ENode '): todo.append(int(e.split()[1]))
    return seen

def canonical(machine, path):
    states = {q for q, _ in machine.states}
    ordered = [machine.start] + sorted(states - {machine.start})
    rename = {q: i for i, q in enumerate(ordered)}
    lines, missing = ['#! start 0'], []
    for q in ordered:
        for bit in '01':
            row = machine.states.get((q, bit))
            if row is None:
                write, move, target = bit, 'R', len(ordered)
                missing.append([q, int(bit)])
            else:
                assert row.nextstate in states or row.nextstate == 'halt'
                write, move = row.write, row.direction
                target = rename.get(row.nextstate, len(ordered))
            lines.append(f'{rename[q]} {bit} {write} {move} {target}')
    path.write_text('\n'.join(lines) + '\n')
    parsed = [line.split() for line in path.read_text().splitlines() if not line.startswith('#')]
    assert len(parsed) == 2 * len(states)
    assert {(int(r[0]), int(r[1])) for r in parsed} == {(q, b) for q in range(len(states)) for b in (0, 1)}
    assert all(0 <= int(r[4]) <= len(states) and r[2] in '01' and r[3] in ('L', 'R') for r in parsed)
    return dict(working_states=len(states), rows=len(parsed), missing_source_rows=missing,
                totalized_missing_rows='preserve read bit, move R, halt', sha256=sha(path))

def guard_exact_one(nodes, names, reg):
    # if positive: decrement again; zero now means original value one.
    # Otherwise restore both decrements and return. Zero initially returns.
    n = len(nodes)
    nodes[n] = (f'EDecnz {reg}', f'ENode {n+1}')
    nodes[n+1] = (f'ENode {n+2}', f'ENode {n+4}')
    nodes[n+2] = (f'ENode {n+3}', 'EHalt')
    nodes[n+3] = (f'EDecnz {reg}', 'EBreak 1')
    nodes[n+4] = (f'EInc {reg}', f'EInc {reg}')
    for q in range(n, n+5): names[q] = f'birth_guard_{reg}_{q}.0'
    # reg1 already has the literal pair of increment instructions at node159.
    if reg == 1:
        nodes[n+1] = (f'ENode {n+2}', 'ENode 159')
    return n

def variant(original, onames, label):
    nodes, names = dict(original), dict(onames)
    if label == 'baseline': return nodes, names
    assert nodes[147] == ('ENode 148', 'ENode 152')
    assert nodes[152] == ('EInc 6', 'ENode 153')
    assert nodes[153] == ('ENode 132', 'ENode 170')
    nodes[147] = ('ENode 148', 'ENode 153')
    nodes[153] = ('ENode 199', 'ENode 170')
    reg = 1 if 'top' in label else 4
    guard = guard_exact_one(nodes, names, reg)
    n = len(nodes)
    copy = 167 if 'no_dummy' in label else 166
    nodes[n] = ((f'ENode {copy}', f'ENode {guard}') if reg == 1
                else (f'ENode {guard}', f'ENode {copy}'))
    names[n] = f'mp_birth_{label}.0'
    assert nodes[130] == ('ENode 123', 'ENode 166')
    nodes[130] = ('ENode 123', f'ENode {n}')
    return nodes, names

def run_tree(nodes, root, registers, fuel=100000):
    """Literal zero-padded path semantics, with a return sentinel after root.

    Break strips zeros and carries; continue strips ones. Counting enclosing
    call frames instead is incorrect for shared sequences on right edges.
    """
    regs, path = list(registers), []
    wrapper = max(nodes) + 1
    def inc(p):
        p=list(p); i=len(p)-1
        while i>=0 and p[i]: p[i]=0; i-=1
        if i>=0: p[i]=1
        return p
    def strip(p,bit,k):
        p=list(p)
        while k and p:
            if p.pop()==bit: k-=1
        return p
    for ticks in range(fuel):
        q,depth=wrapper,0
        while True:
            bit=path[depth] if depth<len(path) else 0
            e=((f'ENode {root}','EReturn') if q==wrapper else nodes[q])[bit]
            depth+=1
            if e.startswith('ENode '): q=int(e.split()[1])
            else: break
        consumed=path[:depth]+[0]*max(0,depth-len(path))
        if e=='EReturn': return regs,ticks
        if e=='EHalt': return None,ticks+1
        kind,arg=e.split(); arg=int(arg)
        if kind=='EInc': regs[arg]+=1; path=inc(consumed)
        elif kind=='EDecnz':
            if regs[arg]: regs[arg]-=1; path=inc(consumed)
            else: path=inc(strip(consumed,0,1))
        elif kind=='EBreak': path=inc(strip(consumed,0,arg))
        elif kind=='EContinue': path=strip(consumed,1,arg)
        else: raise AssertionError(e)
    raise RuntimeError('fuel')

def main():
    OUT.mkdir(exist_ok=True)
    source = REF / 'Dag254.v'
    assert sha(source) == recover.SOURCE_SHA256['ZF/m254/coq/prog/Dag254.v']
    original, onames = recover.parse_dag(source.read_text())
    assert len(original) == 219
    results = {}
    for label in ['baseline', 'top_preserve', 'param_preserve', 'top_no_dummy', 'param_no_dummy']:
        nodes, names = variant(original, onames, label)
        active = reachable(nodes)
        tm = recover.compile_dag(backend, nodes, names)
        recover.reextract(tm, {q:nodes[q] for q in active}, {q:names[q] for q in active})
        path = OUT / (label + '.tm')
        count = canonical(tm, path)
        framework = {q for q, _ in tm.states if q[0].isdigit()}
        count.update(decision_states=len(active), framework_states=len(framework),
                     source_reextraction=True, changed_original_nodes=[q for q in original if nodes[q] != original[q]],
                     graph_reachable_source_nodes=len(active))
        assert count['working_states'] == len(active) + len(framework)
        if label != 'baseline':
            reg = 1 if 'top' in label else 4
            for v in range(101):
                initial = [11,13,17,19,23,29,31,37,41]; initial[reg]=v
                out, _ = run_tree(nodes, 219, initial)
                assert out == (None if v == 1 else initial), (label,v,out)
            for h in range(50):
                initial = [0]*9; initial[5]=h; initial[2]=1000
                expected = list(initial)
                # Same H-erasure as NIP's old failed compare, now unconditional.
                expected[5]=0
                # Compare actual new clear-and-pop with clear then old pop.
                out, _ = run_tree(nodes, 153, initial)
                ref, _ = run_tree(original, 170, expected)
                assert out == ref, (label,h,out,ref)
            count['literal_structured_checks'] = dict(exact_one_guard=101, unconditional_nip=50)
        results[label] = count
        (OUT/(label+'-dag.json')).write_text(json.dumps(dict(nodes=nodes,names=names),indent=2)+'\n')
    assert results['baseline']['working_states'] == 281
    data = dict(status='COMPLETE_CONTROL_MEASURED', upstream_commit=recover.COMMIT,
                exact_reference_source_sha256=sha(source), original_full_logic_retained=True,
                proof_status='ordinary first-falsity-birth lemma; no new compiled-machine theorem',
                results=results, limitations=['Generated blank initialization not verified.',
                    'This generic Wade control cannot be subtracted from the optimized 252-state table.',
                    'Finite structured checks are supplementary to the stated ordinary guard proof.'],
                source_sha256={str(p.relative_to(BASE)):sha(p) for p in [Path(__file__), source, REF/'recover_wade_dag.py', BACKEND/'TMBuilder.py', BACKEND/'tm.py', BACKEND/'tmdb.py']})
    (OUT/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__ == '__main__': main()
