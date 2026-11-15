#!/usr/bin/env python3
"""Construct PA194AX11GH with exact source and local tape certificates.

The pinned AX11G emitter is retained. Five controller rows implement
cache-only Shift. This is a relative construction, not an absolute iPRA
calibration to PA consistency. Run with assertions enabled.
"""
from pathlib import Path
import sys, json, hashlib, argparse

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'vendor'))
import compiler as c
import support as s

def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def build(out, full=True):
    assert __debug__ and not sys.flags.optimize
    parent = s.read_table(ROOT / 'inputs/raw.native.tm')
    nodes = {k:tup(v) for k,v in json.loads((ROOT/'inputs/nodes.json').read_text()).items()}
    assert nodes['node170'] == ('node36', 'node169')
    changes = {(38,0):(0,True,11),(38,1):(1,True,122),
               (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
    rawbase = dict(parent)
    rawbase.update(changes)
    nodes['node170'] = (('node36', ('node167','node145')), 'node57')
    c.machine = lambda: (rawbase, [])
    c.raw_nodes = lambda: nodes
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc,inc)] = 99
    c.MACROS[((inc,inc),(inc,inc))] = 190
    grammar = tup(json.loads((ROOT/'inputs/grammar.tree.json').read_text()))
    raw, idx, shape = c.build(grammar)
    assert raw == rawbase
    folds = json.loads((ROOT/'inputs/folds.json').read_text())
    child, aliases = s.apply_folds(raw, folds)
    cases = s.check_local_folds(raw, child, aliases, folds)
    assert len(raw)==402 and len(shape)==67 and len(folds)==7
    assert len(cases['cases'])==28
    sites, ins, contracts = c.source(grammar)
    runtime = c.validate(child, contracts) if full else None
    if full:
        assert runtime['ok']
    blank = s.startup(child, sites[25][0])
    dense, labels = s.dense_table(child,194)
    assert all(child[q,b]==parent[q,b] for q in c.BOXSTATES for b in (0,1))
    out.mkdir(parents=True, exist_ok=True)
    for name, rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
        (out/name).write_text(s.table_text(rows))
    for name,x in [('labels.json',labels),('nodes.json',nodes),('grammar.tree.json',grammar),
                   ('folds.json',folds),('local_folds.json',cases),
                   ('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),
                   ('instructions.json',ins)]:
        dump(out/name,x)
    receipt = dict(family='PA194AX11GH',working_states=194,transitions=388,
                   native_start=74,native_halt=254,dense_start=0,dense_halt=194,
                   fixed_controls=134,raw_readers=67,simultaneous_folds=7,
                   fixed_edits_from_AX11G=[[q,b,list(parent[q,b]),list(v)] for (q,b),v in sorted(changes.items())],
                   source_sites=len(sites),source_outcomes=len(contracts),
                   local_fold_cases=len(cases['cases']),runtime=runtime,startup=blank,
                   dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),
                   native_sha256=hashlib.sha256(s.table_text(child).encode()).hexdigest(),
                   arithmetic_box_rows_unchanged=True,kernel_checked=False,
                   absolute_ipra_calibration_complete=False)
    dump(out/'receipt.json',receipt)
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'machine')
    ap.add_argument('--quick',action='store_true')
    a=ap.parse_args()
    build(a.output,not a.quick)
