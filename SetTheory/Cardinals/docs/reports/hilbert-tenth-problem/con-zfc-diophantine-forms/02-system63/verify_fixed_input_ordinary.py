#!/usr/bin/env python3
"""Exact arithmetic/source verification for the ordinary-strong variant."""
import contextlib
import io
import json
from pathlib import Path
import random
import verify_fixed_input as base

HERE=Path(__file__).resolve().parent

def main():
    captured=io.StringIO()
    with contextlib.redirect_stdout(captured): base.main()
    parent_validation=json.loads(captured.getvalue())
    normalized=json.loads((HERE/'fixed_input73.json').read_text())
    ordinary=json.loads((HERE/'fixed_input75_ordinary.json').read_text())
    system=json.loads((HERE/'fixed_input63_ordinary_system.json').read_text())
    expected=[]
    for row in normalized['source']:
        if row[0]=='aux_coefficient_root':
            expected.extend([
                ['f2_minus_one','-','L16',1],['R16','*','A','f2_minus_one'],
                ['ordinary_ic2','*','i','c2'],
                ['ordinary_ic2_square','*','ordinary_ic2','ordinary_ic2'],
                ['ordinary_strong_sum','+','ordinary_ic2_square',1],
                ['norm_strong','-','ordinary_strong_sum','R16']])
        elif row[0] in ['R16','scaled_f_square','norm_strong']: continue
        elif row[0]=='polynomial':expected.append(['polynomial','-','all_with_marker',1])
        else:expected.append(row)
    base.require(ordinary['source']==expected,'ordinary source replacement differs')
    ledger=base.validate_source(ordinary,['polynomial'])
    outputs=[v for pair in system['comparisons'] for v in pair if isinstance(v,str)]
    system_ledger=base.validate_source(system,outputs)
    needed=set(outputs); expected_system=[]
    for row in reversed(expected):
        if row[0] in needed:
            expected_system.append(row)
            needed.update(v for v in row[2:] if isinstance(v,str))
    base.require(system['source']==expected_system[::-1],'ordinary system pruning differs')
    rng=random.Random(2026102201)
    for trial in range(64):
        values={k:rng.randrange(-3,7) for k in normalized['fixed_numerals']+normalized['witnesses']}
        n=base.evaluate(normalized['source'],values)
        lifted=dict(values);lifted['i']=n['A']*values['i']
        o=base.evaluate(ordinary['source'],lifted)
        error=n['norm_strong']-n['A']
        base.require(o['norm_strong']==1-error,'strong-factor identity')
        base.require(o['norm_aux']==n['norm_aux']+error*n['aux_square_gap'],
                     'auxiliary-factor identity')
        common=1
        for f in ['norm_first','norm_main','norm_index','norm_transport','marker_unit']:
            base.require(n[f]==o[f],'retained factor differs')
            common*=n[f]
        base.require(o['polynomial']+1==common*(n['norm_aux']+error*n['aux_square_gap'])*(1-error),
                     'whole polynomial identity')
    constants={'Bm1':15,'Kconstant':11,'MC':2,'MF':19,'W0':8192}
    d=base.diagonal(ordinary['source'],ordinary['witnesses'],constants)
    expected_leader=8*(15**55)*(2**9)*(-14)*(11**2)
    base.require(len(d['polynomial'])-1==101,'wrong exact polynomial degree')
    base.require(d['polynomial'][-1]==expected_leader,'wrong degree101 leader')
    factor_degrees=[len(d[x])-1 for x in ['norm_first','norm_main','norm_aux','norm_index',
        'norm_transport','norm_strong','marker_unit']]
    base.require(factor_degrees==[22,18,28,7,2,22,2],'factor degrees differ')
    s=base.diagonal(system['source'],system['witnesses'],constants)
    sos=[0]
    residual_degrees=[]
    for left,right in system['comparisons']:
        a=s[left] if isinstance(left,str) else [left]
        b=s[right] if isinstance(right,str) else [right]
        r=base.add(a,b,-1);residual_degrees.append(len(r)-1)
        sos=base.add(sos,base.mul(r,r))
    base.require(len(sos)-1==56,'wrong system SOS degree')
    base.require(sos[-1]==16*(15**28),'wrong SOS leading coefficient')
    print(json.dumps({'status':'pass','normalized_parent_validation':'pass',
        'upstream_f84_git_blob':parent_validation['upstream_f84_git_blob'],
        'polynomial_ledger':ledger,'system_ledger':system_ledger,
        'positive_unknowns':16,'exact_polynomial_degree':101,
        'factor_degrees':factor_degrees,'system_residual_degrees':residual_degrees,
        'system_SOS_degree':56,'system_SOS_gates':83,
        'signed_whole_source_identity_fixtures':64,
        'diagnostic_constants_are_not_a_compiled_ZFC_program':True,
        'scope':'Literal source and arithmetic checks. Semantic proof imports the stated generic strong-rank theorem.'},indent=2))

if __name__=='__main__':main()
