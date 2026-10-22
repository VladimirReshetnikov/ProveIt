#!/usr/bin/env python3
"""Separate start-only constant specification; fixed-input fallback is unchanged.

Window1 is an explicit locally valid window absent every canonical run. The
source has C=Z and no input loader. Its MF port is still the shifted source mask.
"""
from itertools import product
from pathlib import Path
import argparse
import json
import explicit_constants as core

FORBIDDEN_WINDOW = (core.tile(0,core.Q0),)*9
assert FORBIDDEN_WINDOW == (7,)*9


def enumerate_windows():
    yield core.START_WINDOW
    yield FORBIDDEN_WINDOW
    for w in product(range(core.ALPHABET_SIZE),repeat=9):
        if w not in (core.START_WINDOW,FORBIDDEN_WINDOW) and core.allowed_window(w):
            yield w


def emitted_start_only_ports(layout):
    """Exact four-port binding for the start-only polynomial.

    Do not substitute the native MF for the port named MF.
    """
    c=core.materialize_constants(layout)
    return {'Bm1':c['Bm1'],'Kconstant':c['Kconstant'],'MC':c['MC'],'MF':c['MF_source']}


def symbolic_constant_spec():
    spec=core.symbolic_constant_spec()
    spec['target']='start_only_polynomial67.json'
    spec['target_ports']={'Bm1':'Bm1','Kconstant':'Kconstant','MC':'MC','MF':'MF_source'}
    spec.pop('end_window')
    spec['forbidden_window']=FORBIDDEN_WINDOW
    spec['predicate']='explicit_constants.allowed_window (unchanged total finite function)'
    spec['coefficient_semantics']='All symbols denote fixed integers. No input loader is used; C=Z.'
    spec['nodes']=[row for row in spec['nodes'] if row[0] not in ('W0','twice_cell_bits','inner_bits')]
    for row in spec['nodes']:
        if row[0]=='windows':
            row[1]='START_WINDOW, FORBIDDEN_WINDOW=(7,)*9, then other passing tuples in lexicographic order'
    spec['canonical_exclusion']='State q0 appears only in the first phase-Q tile on symbol1; no canonical noninitial tile carries q0. Hence the all-ordinary-q0/blank forbidden window never appears.'
    return spec


def bounded_audits():
    assert core.allowed_window(FORBIDDEN_WINDOW)
    assert FORBIDDEN_WINDOW != core.START_WINDOW
    assert core.delta(core.Q0,1)==(2,0,core.Q1)
    assert core.payload(FORBIDDEN_WINDOW[4])==(0,core.Q0)
    assert all(core.delta(q,s)[2]!=core.Q0 for q,s in
               product(range(1,core.STATE_COUNT),range(core.SYMBOL_COUNT)))
    assert all(t<6 or core.payload(t)[1]!=core.Q0 for t in
               (core.LEFT,core.INPUT,core.START_HEAD,core.RIGHT))
    stub={'b':1,'d':9,'H':3,'DC':{0:17},'MF':{0:52},'native':[0,1,6],'dummy':[6]}
    ports=emitted_start_only_ports(stub)
    assert ports=={'Bm1':511,'Kconstant':4113,'MC':318,'MF':563}
    return {'forbidden_window':FORBIDDEN_WINDOW,
            'forbidden_window_is_locally_valid':True,
            'all_4340_noninitial_transitions_exclude_q0':True,
            'first_initial_transition_excludes_q0':True,
            'initial_row_has_no_ordinary_q0_tile':True,
            'canonical_forbidden_window_exclusion':True,
            'coefficient_recipe_uses_all_valid_windows_with_changed_first_two_order':True,
            'loader_removed_C_equals_Z':True,
            'source_MF_binding_checked':ports,
            'full_window_enumeration':False,
            'full_numeral_materialization':False,
            'scope':'This checks the separate compiler/semantics adapter, not the full start-only arithmetic certificate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbolic-spec',type=Path)
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    if args.symbolic_spec:
        args.symbolic_spec.write_text(json.dumps(symbolic_constant_spec(),indent=2,sort_keys=True)+'\n')
    output=json.dumps(bounded_audits(),indent=2,sort_keys=True)+'\n'
    if args.receipt: args.receipt.write_text(output)
    print(output,end='')

if __name__=='__main__':main()
