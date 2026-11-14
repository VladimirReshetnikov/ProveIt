#!/usr/bin/env python3
"""Reproduce the 196-state top-only Shift research prototype.

Python standard library only. This uses the inherited arithmetic-block
interface, unlike the separately verified main QN6 artifact.
"""
from pathlib import Path
import argparse, collections, hashlib, itertools, json, sys
import compiler as c
import support as s

HERE = Path(__file__).resolve().parent
def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x
def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def build(out):
    assert __debug__ and not sys.flags.optimize
    parent = s.read_table(HERE/'inputs/primary.raw.native.tm')
    nodes = {k:tup(v) for k,v in json.loads((HERE/'inputs/base.nodes.json').read_text()).items()}
    assert nodes['node163'] == ('node6','node55')
    # Keep old T in X, transfer old H to T without also copying it to X,
    # then transfer X into H. The inherited comparison now tests old T=1.
    nodes['node168'] = ('node37', ((('leaf','dec',5),'node38'),'node19'))
    nodes['node163'] = ('node6','node54')
    c.machine = lambda: (parent, [])
    c.raw_nodes = lambda: nodes
    inc = ('leaf','inc',1)
    c.MACROS[(inc,inc)] = 99
    c.MACROS[((inc,inc),(inc,inc))] = 190
    grammar = c.read_grammar(HERE/'inputs/primary.grammar.json')
    raw, index, shape = c.build(grammar)
    raw[38,1] = (1,True,340)
    raw[340,0] = (0,True,341)
    raw[340,1] = (1,True,31)
    raw[341,0] = (0,True,45)
    raw[341,1] = (1,True,57)
    raw[164,1] = (1,True,114)
    assert len(raw) == 406 and len(shape) == 67
    folds = json.loads((HERE/'inputs/primary.folds.json').read_text())
    final, aliases = s.apply_folds(raw, folds)
    assert len(final) == 392 and len(folds) == 7
    local = s.check_local_folds(raw, final, aliases, folds)
    assert len(local['cases']) == 28
    assert all(final[q,b] == parent[q,b] for q in c.BOXSTATES for b in (0,1))
    sites, instructions, contracts = c.source(grammar)
    assert len(sites) == 3653 and len(contracts) == 4754
    print('Checking 4,754 source outcomes', flush=True)
    validation = c.validate(final, contracts)
    assert validation['ok'], validation
    startup = s.startup(final, sites[25][0])
    dense, labels = s.dense_table(final, 196)
    incoming = collections.defaultdict(set)
    for (q,bit),(w,d,target) in final.items():
        incoming[target].add((w,d))
    eligible = {q for q in incoming if incoming[q] in ({(0,True)},{(1,True)}) and q not in {74,254}}
    opportunities = c.opportunities_fast(final, eligible)
    accepted = []
    for a,b,choices in opportunities:
        for actions in itertools.product(*choices):
            try:
                candidate, projection = s.apply_folds(final, [(a,b,actions)])
                s.check_local_folds(final, candidate, projection, [(a,b,actions)])
                accepted.append([a,b,actions])
            except (AssertionError,KeyError):
                pass
    assert not accepted
    out.mkdir(parents=True, exist_ok=True)
    for name,table in [('machine.tm',dense),('machine.native.tm',final),('raw.native.tm',raw)]:
        (out/name).write_text(s.table_text(table))
    for name,value in [('nodes.json',nodes),('labels.json',labels),('instructions.json',instructions),
                       ('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),
                       ('folds.json',folds),('local_fold_cases.json',local)]:
        dump(out/name,value)
    receipt = {
        'status':'PASS', 'family':'Top-only Shift196 research prototype',
        'working_states':196, 'transition_rows':392, 'raw_controls':203,
        'fixed_controls':136, 'axiom_readers':67, 'folds':7,
        'source_sites':len(sites), 'source_outcomes':len(contracts),
        'shift_test':'t=1', 'nonhalting_shift':'(h,tail(w),d,head(w))',
        'MP_success':'(b,w,b,0), b=d+x', 'formula_coefficient':4,
        'validation':validation, 'local_fold_cases':len(local['cases']),
        'arithmetic_box_rows_unchanged':True,
        'startup':startup,
        'native_sha256':hashlib.sha256(s.table_text(final).encode()).hexdigest(),
        'dense_sha256':hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
        'local_search':{'eligible_controls':len(eligible),'opportunity_pairs':len(opportunities),
                        'accepted_additional_folds':accepted},
        'scope':'Inherited arithmetic-block interface plus full symbolic source outcomes and complete literal startup. No separate independent block replay, full consistency endpoint, novelty claim, or state lower bound for this research prototype.'
    }
    dump(out/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output',type=Path,default=HERE/'machine')
    build(p.parse_args().output)
