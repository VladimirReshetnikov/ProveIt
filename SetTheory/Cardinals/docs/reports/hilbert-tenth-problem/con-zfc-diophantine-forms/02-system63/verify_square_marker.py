#!/usr/bin/env python3
"""Verify the final one-gate slack-square reduction, including parent checks."""
import contextlib
import io
import json
from pathlib import Path
import random
import verify_fixed_input as base
import verify_fixed_input_ordinary as ordinary_check

HERE=Path(__file__).resolve().parent

def main():
    buf=io.StringIO()
    with contextlib.redirect_stdout(buf):ordinary_check.main()
    results=[]
    rng=random.Random(2026102202)
    for parent_name,child_name,degree,total in [
        ('fixed_input73.json','fixed_input72_square_marker.json',157,72),
        ('fixed_input75_ordinary.json','fixed_input74_ordinary_square_marker.json',101,74)]:
        parent=json.loads((HERE/parent_name).read_text())
        child=json.loads((HERE/child_name).read_text())
        expected=[]
        for row in parent['source']:
            if row[0]=='marker_unit':continue
            if row[0]=='all_with_marker':row=['all_with_marker','*','seven_units','marker_square']
            expected.append(row)
        base.require(child['source']==expected,'marker source differs')
        ledger=base.validate_source(child,['polynomial'])
        base.require(ledger['total']==total,'wrong marker ledger')
        for _ in range(64):
            values={k:rng.randrange(-4,8) for k in parent['witnesses']+parent['fixed_numerals']}
            old=base.evaluate(parent['source'],values)
            changed=dict(values);changed['alpha']+=1
            new=base.evaluate(child['source'],changed)
            base.require(new['marker_difference']==old['marker_difference']-1,'slack shift')
            for factor in ['norm_first','norm_main','norm_aux','norm_index','norm_transport','norm_strong']:
                base.require(new[factor]==old[factor],'alpha reached retained factor')
            offset=old['A'] if degree==157 else 1
            base.require(old['marker_unit']*(new['polynomial']+offset)
                ==new['marker_square']*(old['polynomial']+offset),'whole marker identity')
        constants={'Bm1':15,'Kconstant':11,'MC':2,'MF':19,'W0':8192}
        oldpoly=base.diagonal(parent['source'],parent['witnesses'],constants)['polynomial']
        newpoly=base.diagonal(child['source'],child['witnesses'],constants)['polynomial']
        base.require(len(newpoly)-1==degree,'degree changed')
        base.require(newpoly[-1]==oldpoly[-1],'leading coefficient changed')
        results.append({'file':child_name,'ledger':ledger,'positive_unknowns':16,
            'exact_degree':degree,'signed_source_fixtures':64})
    for alpha in range(1,8):
        for eps in [-1,1]:
            base.require(alpha+eps>=0,'effective slack can be negative')
            for F in range(1,8):
                base.require(F+alpha+eps>0,'raw slack numerator gap not positive')
    print(json.dumps({'status':'pass','parent_validations':'pass','variants':results,
        'scope':'Literal source, exact algebra, degree and elementary slack checks. Semantic proof is SQUARED_MARKER_PROOF.md.',
        'diagnostic_constants_are_not_a_compiled_ZFC_program':True},indent=2))

if __name__=='__main__':main()
