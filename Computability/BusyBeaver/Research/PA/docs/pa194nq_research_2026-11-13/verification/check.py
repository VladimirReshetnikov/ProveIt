#!/usr/bin/env python3
"""Independent literal-tape refinement for every PA194NQ source outcome.

This driver adapts the attributed PA194Q independent verification harness.
It imports neither the optimizing compiler nor its arithmetic-block oracle.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

PACKAGE = Path(__file__).resolve().parent.parent
REFERENCE = Path(__file__).resolve().parent/'reference'
sys.path.insert(0, str(REFERENCE))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE = 48
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def read(path, halt, count):
    table = {}
    for line in path.read_text().splitlines():
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0,1) and write in (0,1) and direction in ('L','R')
        assert (q,bit) not in table
        table[q,bit] = (write, 1 if direction == 'R' else -1, target)
    states = {q for q,bit in table}
    assert len(states) == count and halt not in states
    assert set(table) == {(q,b) for q in states for b in (0,1)}
    assert {n for w,d,n in table.values()}-states == {halt}
    return table, states


def check(machine, output):
    assert __debug__, 'Run with assertions enabled.'
    output.mkdir(parents=True, exist_ok=True)
    rec = json.loads((machine/'receipt.json').read_text())
    count, steps = rec['states'], rec['seed']['steps']
    table, states = read(machine/'machine.native.tm', 254, count)
    dense, dense_states = read(machine/'machine.tm', count, count)
    assert dense_states == set(range(count))
    labels = json.loads((machine/'labels.json').read_text())
    assert len(labels) == len(set(labels)) == count+1
    assert labels[0] == 74 and labels[-1] == 254
    assert {(labels[q],b):(w,d,labels[n]) for (q,b),(w,d,n) in dense.items()} == table
    seen, order = {74}, [74]
    for q in order:
        for bit in (0,1):
            target = table[q,bit][2]
            if target != 254 and target not in seen:
                seen.add(target)
                order.append(target)
    assert order+[254] == labels
    sites = json.loads((machine/'sites.json').read_text())
    opmap = {'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped = [[p,opmap[op],a] for p,op,a in sites]
    graph, _ = source.graph_arithmetic(mapped)
    assert graph == source.graph_intervals(mapped)
    names = {'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    ins = [[names[e[0]]]+e[1:]+targets for e,targets in graph]
    assert ins == json.loads((machine/'instructions.json').read_text())
    assert max(len(p) for p,op,a in sites) <= 48
    mapping = {int(k):v for k,v in json.loads((REFERENCE/'legacy_mapping.json').read_text()).items()}
    for q in states|{254}:
        mapping.setdefault(q,q+10000)
    assert len({mapping[q] for q in states|{254}}) == count+1
    assert mapping[84] == 96 and mapping[254] == 254
    symbolic = {(mapping[q],b):(w,d,mapping[n]) for (q,b),(w,d,n) in table.items()}
    runtime.PHY = PHY
    lemmas, blocks = sym.prove_blocks(symbolic)
    assert len(blocks) == 4
    contracts, total, maximum = [], 0, 0
    for i,site in enumerate(mapped):
        for positive in ([False,True] if site[1] == 'CD' else [False]):
            result = sym.case(symbolic,lemmas,site,positive)
            total += result['symbolic_steps']
            maximum = max(maximum,result['symbolic_steps'])
            contracts.append({'site':i,'positive':positive,'duration':result['duration'],
                              'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
        if (i+1)%500 == 0:
            print('Checked source sites:',i+1,flush=True)
    assert len(contracts) == rec['contracts']
    # Independent startup uses a finite support set, so there is no hidden tape boundary.
    ones, head, q = set(), 0, 74
    for _ in range(steps):
        assert q != 254
        w,d,q = table[q,int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += d
    assert q == 84 and head == -2
    path = sites[25][0]
    expected = {head-1,head+48}
    expected.update(head+i for i,b in enumerate(path) if b == '1')
    logical, physical = [2]+[0]*8, [None]*9
    for i,j in enumerate(PHY):
        physical[j] = logical[i]
    position = head+49
    for value in physical+[1]*26:
        position += 1
        expected.update(range(position,position+value+1))
        position += value+1
    assert ones == expected
    encoded = (json.dumps(contracts,separators=(',',':'))+'\n').encode()
    (output/'contracts.json').write_bytes(encoded)
    (output/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
    minimum = min(case['duration'][0] for case in contracts)
    assert minimum > 0
    receipt = {'status':'PASS','states':count,'transition_rows':2*count,
               'sha256':hashlib.sha256((machine/'machine.tm').read_bytes()).hexdigest(),
               'source_sites':len(sites),'universal_source_outcomes':len(contracts),
               'independent_resolvers_agree':True,'dense_conjugacy_exact':True,
               'symbolic_steps':total,'maximum_symbolic_steps':maximum,
               'minimum_positive_duration_constant':minimum,
               'four_list_lemmas_rederived_from_literal_table':True,
               'arithmetic_box_oracles':False,
               'register_scope':'nine arbitrary natural values and both decrement branches',
               'spare_scope':'arbitrary finite nonempty list of arbitrary natural values',
               'gap_scope':'header distance 48+n for every natural n',
               'startup_steps':steps,'complete_blank_tape_equal':True,
               'contracts_sha256':hashlib.sha256(encoded).hexdigest(),'kernel_checked':False}
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--machine',type=Path,default=PACKAGE/'machine')
    parser.add_argument('--output',type=Path,default=PACKAGE/'evidence/independent')
    args = parser.parse_args()
    check(args.machine,args.output)
