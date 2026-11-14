#!/usr/bin/env python3
"""Build PA194H5: coefficient five, visible-result no-push MP, cached Shift.

Composition of the supplied M5 multiplier and PA194H fixed controller.
Neither constituent mechanism is claimed as new.  All source outcomes and
the complete blank startup are checked on the final simultaneously folded
table; the logical calibration is an ordinary PA-formalizable proof.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, sys
import compiler as c
import support as s

HERE = Path(__file__).resolve().parent
INC = ('leaf', 'inc', 1)
BASE_NODES = c.raw_nodes
H_EDITS = {
    (38,0):(0,True,11), (38,1):(1,True,122),
    (164,1):(1,True,114), (214,0):(0,True,312),
    (214,1):(1,True,20), (312,0):(0,True,188),
}

def sha(data): return hashlib.sha256(data).hexdigest()
def dump(path, data): path.write_text(json.dumps(data, indent=2)+'\n')

def build(out):
    assert __debug__ and not sys.flags.optimize
    c.raw_nodes = BASE_NODES
    c.MACROS[(INC,INC)] = 99
    c.MACROS[((INC,INC),(INC,INC))] = 190
    grammar = c.read_grammar(HERE/'inputs/pa194.grammar.json')
    original, _ = c.machine()
    raw, index, shape = c.build(grammar)
    assert len(raw) == 402 and len(shape) == 67
    # M5's three-plus-two multiplier uses the same 67 AX reader states.
    raw.update({(190,0):(0,True,330), (190,1):(1,True,99),
                (330,0):(0,True,61), (330,1):(1,True,99)})
    folds = json.loads((HERE/'inputs/pa194.folds.json').read_text())
    folds += [[41,99,[[0,False,30],[1,False,2035]]]]
    m5, _ = s.apply_folds(raw, folds)
    m5dense, _ = s.dense_table(m5,194)
    assert s.table_text(m5dense) == (HERE/'inputs/parent5.machine.tm').read_text()
    # Independent H controller changes: no-push MP and cache-only Shift.
    raw.update(H_EDITS)
    child, aliases = s.apply_folds(raw, folds)
    local = s.check_local_folds(raw, child, aliases, folds)
    assert len(raw) == 404 and len(child) == 388
    assert len(folds) == 8 and len(local['cases']) == 32
    assert all(child[q,b] == original[q,b] for q in c.BOXSTATES for b in (0,1))
    ns = BASE_NODES()
    ns['node61'] = ((INC,'node60'),'node60')
    parent5nodes = json.loads((HERE/'inputs/parent5.nodes.json').read_text())
    assert json.loads(json.dumps(ns)) == parent5nodes
    ns['node163'] = ('node6','node54')
    ns['node170'] = (('node36',('node167','node145')),'node57')
    c.raw_nodes = lambda: ns
    sites, instructions, contracts = c.source(grammar)
    runtime = c.validate(child, contracts)
    assert runtime['ok'], runtime
    startup = s.startup(child, sites[25][0])
    dense, labels = s.dense_table(child,194)
    out.mkdir(parents=True, exist_ok=True)
    for name, rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
        (out/name).write_text(s.table_text(rows))
    for name, data in [('labels.json',labels),('nodes.json',ns),('folds.json',folds),
                       ('local_fold_cases.json',local),('instructions.json',instructions),
                       ('sites.json',[[''.join(map(str,p)),op,arg] for p,op,arg in sites])]:
        dump(out/name,data)
    receipt = {
        'family':'PA194H5', 'formula_coefficient':5,
        'working_states':194, 'rows':388, 'unfolded_states':202,
        'fixed_controls':135, 'AX_readers':67, 'simultaneous_folds':8,
        'local_fold_cases':32, 'source_sites':len(sites), 'source_outcomes':len(contracts),
        'source_instruction_counts':dict(Counter(row[0] for row in instructions)),
        'native_start':74, 'native_halt':254, 'dense_start':0, 'dense_halt':194,
        'runtime':runtime, 'startup':startup,
        'dense_sha256':sha(s.table_text(dense).encode()),
        'native_sha256':sha(s.table_text(child).encode()),
        'native_edits_from_M5':[[q,b,list(m5[q,b]),list(child[q,b])] for q,b in sorted(child) if m5[q,b]!=child[q,b]],
        'arithmetic_box_rows_unchanged':True, 'kernel_checked':False,
        'scope':'Every symbolic physical source contract, simultaneous folds, and complete blank startup. Source binding, independent physical replay, logical calibration and novelty are checked separately.'
    }
    dump(out/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
    return receipt

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE.parent/'machine')
    build(parser.parse_args().output)
