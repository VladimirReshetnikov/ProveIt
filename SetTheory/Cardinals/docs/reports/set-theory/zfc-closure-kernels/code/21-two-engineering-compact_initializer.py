"""A complete binary finite-gap initializer for the clean Mira assembler.

Author: OpenAI, for Vladimir Reshetnikov, 2026-10-16.
New initialization code only. The attributed upstream engine and research
assembler are unmodified in vendor/. This is a locally certified compiler
component, not a new ZFC-consistency-machine bound.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import sys

PHYSICAL_ORDER = (2, 4, 3, 7, 6, 8, 0, 1, 5)


def choose_parameters(minimum_gap):
    """Minimize our explicit state formula; break ties by time then gap."""
    if type(minimum_gap) is not int or minimum_gap < 1:
        raise ValueError('minimum_gap must be positive')
    candidates = []
    for n in range(1, max(2, minimum_gap + 1)):
        m = max(1, (max(0, minimum_gap-2)+n-1)//n-2)
        gap = n*(m+2)+2
        candidates.append((28+2*n+m, 28+6*n+(m+2)*n*(n+2), gap, n, m))
    _, _, _, n, m = min(candidates)
    return n, m


def make_initializer(initial, n, m, target='return'):
    """Return a total labeled binary transition table and exact contract.

    Tape initially blank, state i:0, head 0. On exit target, tape has a
    marker, gap zeros, a header, and exactly nine encoded unary registers.
    The head is immediately right of the marker. No scratch marks remain.
    """
    initial = tuple(initial)
    if len(initial) != 9 or any(type(x) is not int or x < 0 for x in initial):
        raise ValueError('exactly nine natural initial registers required')
    if type(n) is not int or type(m) is not int or n < 1 or m < 1:
        raise ValueError('positive counter count and stride required')
    if target.startswith('i:'):
        raise ValueError('exit label must not collide with initializer labels')
    registers = [b for j in PHYSICAL_ORDER for b in [0]+[1]*(initial[j]+1)]
    wire = list(reversed(registers)) + [1,1] + [0,1]*n + [0,1]
    table = {}

    def put(q, b, w, direction, dest):
        if (q,b) in table: raise ValueError('duplicate row')
        table[q,b] = w,direction,dest

    for j, w in enumerate(wire):
        last = j+1 == len(wire)
        for b in (0,1):
            put(f'i:{j}', b, w, 'R' if last else 'L',
                'i:right' if last else f'i:{j+1}')
    # The first remaining isolated 1 is a counter; adjacent 11 is the end.
    put('i:right',0,0,'R','i:right')
    put('i:right',1,1,'R','i:test')
    put('i:test',0,0,'L','i:consume')
    put('i:test',1,1,'L','i:finish_erase')
    for b in (0,1): put('i:consume',b,0,'L','i:left')
    put('i:left',0,0,'L','i:left')
    put('i:left',1,0,'L','i:stride0')
    for j in range(m):
        last = j+1 == m
        for b in (0,1):
            put(f'i:stride{j}',b,1 if last else 0,'R' if last else 'L',
                'i:right' if last else f'i:stride{j+1}')
    for b in (0,1): put('i:finish_erase',b,0,'L','i:finish_left')
    put('i:finish_left',0,0,'L','i:finish_left')
    put('i:finish_left',1,1,'R',target)
    S = sum(initial)
    contract = dict(counter_count=n, stride=m, gap=n*(m+2)+2,
                    initializer_states=S+28+2*n+m,
                    blank_steps=S+28+6*n+(m+2)*n*(n+2),
                    initial_registers=list(initial), physical_order=list(PHYSICAL_ORDER),
                    scratch_marks_on_exit=0, spare_register_blocks=0)
    assert len(table) == 2*contract['initializer_states']
    assert all(direction in ('L','R') and w in (0,1)
               for w,direction,dest in table.values())
    return table, contract


def simulate_initializer(table, contract, target='return'):
    """Independent literal transition replay and exact whole-tape check."""
    q, head, tape = 'i:0', 0, set()
    for steps in range(contract['blank_steps'] + 1):
        if q == target: break
        w, direction, q = table[q,int(head in tape)]
        if w: tape.add(head)
        else: tape.discard(head)
        head += 1 if direction == 'R' else -1
    else: raise AssertionError('initializer exceeded proved step count')
    initial = contract['initial_registers']
    bits = [1]+[0]*contract['gap']+[1]
    bits += [b for j in PHYSICAL_ORDER for b in [0]+[1]*(initial[j]+1)]
    expected = {head-1+i for i,b in enumerate(bits) if b}
    assert q == target and steps == contract['blank_steps']
    assert tape == expected
    assert head == -(18+sum(initial)+contract['gap'])
    # Serialize the entire finite support, not a finite window of the tape.
    digest = hashlib.sha256(json.dumps(dict(head=head,ones=sorted(tape)),
                           sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return dict(passed=True,steps=steps,head=head,ones=len(tape),
                configuration_sha256=digest)


def integrate(machine, n, m):
    """Replace exactly the direct initializer; preserve every runtime row."""
    new_init, contract = make_initializer(machine.initial_registers,n,m,'d:0')
    assert contract['gap'] == machine.gap
    inverse = {v:k for k,v in machine.labels.items()}
    runtime = {(inverse[q],b):(w,d,inverse[t])
               for (q,b),(w,d,t) in machine.table.items()
               if not inverse[q].startswith('i:')}
    assert not any(t.startswith('i:') for w,d,t in runtime.values())
    named = runtime | new_init
    names = {q for q,b in named}
    assert not ({q for q,b in runtime} & {q for q,b in new_init})
    order = ['i:0']+sorted(names-{'i:0'})
    labels = {q:i for i,q in enumerate(order)} | {'halt':len(order)}
    machine.table = {(labels[q],b):(w,d,labels[t])
                     for (q,b),(w,d,t) in named.items()}
    machine.labels = labels
    old = machine.evidence['states_by_role']['initializer']
    machine.evidence['direct_initializer_states_same_gap'] = old
    machine.evidence['states_by_role']['initializer'] = contract['initializer_states']
    machine.evidence['working_states'] = len(order)
    machine.evidence['transition_rows'] = len(named)
    machine.evidence['compact_initializer_contract'] = contract
    machine.evidence['compact_initializer_replay'] = simulate_initializer(new_init,contract,'d:0')
    machine.evidence['runtime_rows_preserved_under_renaming'] = len(runtime)
    machine.evidence['machine_sha256'] = hashlib.sha256(machine.encoded()).hexdigest()
    # Re-extract the complete runtime by names after numeric relabeling.
    invnew = {v:k for k,v in labels.items()}
    actual = {(invnew[q],b):(w,d,invnew[t])
              for (q,b),(w,d,t) in machine.table.items()
              if not invnew[q].startswith('i:')}
    assert actual == runtime
    # Replay complete assembled table, independently of the labeled run.
    q, h, tape = 0,0,set()
    for _ in range(contract['blank_steps']):
        assert q != machine.root
        w,d,q = machine.table[q,int(h in tape)]
        if w: tape.add(h)
        else: tape.discard(h)
        h += 1 if d == 'R' else -1
    assert q == machine.root
    bits = [1]+[0]*machine.gap+[1]
    bits += [b for j in PHYSICAL_ORDER
             for b in [0]+[1]*(machine.initial_registers[j]+1)]
    assert tape == {h-1+i for i,b in enumerate(bits) if b}
    return machine


def main():
    if not __debug__: raise RuntimeError('run without -O/-OO')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'results')
    parser.add_argument('--skip-engine-cases',action='store_true')
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    cases = 0
    vectors = [(0,)*9,(2,)+(0,)*8,tuple(range(9))]
    for n in range(1,13):
        for m in range(1,25):
            for initial in vectors:
                table,contract = make_initializer(initial,n,m)
                simulate_initializer(table,contract)
                cases += 1
    parameter_cases = 0
    for required in range(1,301):
        n,m = choose_parameters(required)
        assert n*(m+2)+2 >= required
        # Independent exhaustive comparison within a sufficient finite bound.
        best = min(2*a+b for a in range(1,required+2)
                   for b in range(1,required+2) if a*(b+2)+2 >= required)
        assert 2*n+m == best
        parameter_cases += 1
    root = Path(__file__).parent/'vendor/ProveIt'
    source = root/'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0,str(source))
    assembler = importlib.import_module('mira_backend')
    recover = importlib.import_module('recover_wade_dag')
    nodes,names = recover.parse_dag(recover.git_bytes(None,assembler.DAG_PATH).decode())
    records = {}
    for label,initial in [('zero',(0,)*9),('nextproof2',(2,)+(0,)*8)]:
        direct = assembler.compile_dag(nodes,names,initial_registers=initial)
        n,m = choose_parameters(direct.gap)
        selected = assembler.compile_dag(nodes,names,initial_registers=initial,
                                        gap=n*(m+2)+2)
        machine = integrate(selected,n,m)
        machine.evidence['direct_reference_states_minimum_gap'] = direct.halt
        machine.evidence['direct_reference_gap'] = direct.gap
        if not args.skip_engine_cases:
            machine.check_sites()
        path = args.output/f'dag219-compact-{label}.tm'
        machine.save(path)
        # Reparse every emitted literal row and compare numeric identities.
        parsed = {}
        for line in path.read_text().splitlines():
            if line.startswith('#'): continue
            q,b,w,d,t = line.split()
            parsed[int(q),int(b)] = int(w),d,int(t)
        assert parsed == machine.table
        records[label] = machine.evidence
    evidence = dict(initializer_exact_replay_cases=cases,
                    parameter_minimization_cases=parameter_cases,
                    machine_variants=records,
                    whole_binary_compiler_formally_proved=False,
                    new_ZFC_consistency_machine_bound_claimed=False)
    (args.output/'compact-initializer-results.json').write_text(
        json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(exact_cases=cases,parameter_cases=parameter_cases,
          variants={k:dict(states=v['working_states'],
                    initializer=v['states_by_role']['initializer'],
                    gap=v['gap'],boot_steps=v['compact_initializer_contract']['blank_steps'])
                    for k,v in records.items()}),indent=2))


if __name__ == '__main__': main()
