#!/usr/bin/env python3
"""Replay the portable logical certificates and the exact 250-state audit.

Python 3.10+ standard library only. The literal machine is reconstructed
and required to match the retained canonical table byte-for-byte. This
does not run an unbounded Turing-machine computation or a proof assistant.
"""
import argparse
from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
EXPECTED_TM='125b42fb7ac3db95e43f74e20d75cbfde543de71354e8ee488152ecd2e90dcc1'
def read(name):return json.loads((ROOT/name).read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--logic-only',action='store_true',help='Skip the finite 250-state source/runtime/boot audit')
    ap.add_argument('--searches',action='store_true',help='Also rerun the finite 1296-basis and 264-bundle cost searches; about two minutes')
    args=ap.parse_args()
    for row in read('vendor_manifest.json')['files']:
        assert sha(ROOT/row['path'])==row['sha256'],row['path']
    import prove_ksp_lukasiewicz as ksp
    import prove_flat_bundle as flat
    import check_upstream_lukasiewicz as old
    import generic_proof_macros as macros
    import propositional_countermodels as counter
    result=dict(vendored_files=len(read('vendor_manifest.json')['files']))
    result['KSP_to_L']=ksp.check(read('ksp_to_lukasiewicz.json'))
    result['L_to_KSP']=old.run(ROOT/'vendor/busy-beaver/ZF/m254/coq/logic/CD254.v')
    cert=read('flat_bundle_equivalence.json')
    result['nested_to_flat']=flat.check(cert['nested_to_flat'],flat.C(flat.old,flat.flat))
    result['flat_to_nested']=flat.check(cert['flat_to_nested'],flat.C(flat.flat,flat.old))
    with redirect_stdout(io.StringIO()):
        macros.main()
        counter.main()
    result['generic_stack_macros']=read('generic_proof_macros_check.json')
    result['fixed_f_countermodel']=read('propositional_countermodels_check.json')
    counts=read('bundle_shapes_results.json')
    assert counts['shapes']==11 and counts['cases']==len(counts['results'])==264
    assert min(x['grammar_rules'] for x in counts['results'])==128
    assert counts['best']['shape']=='((C,G),(R,E))'
    result['retained_bundle_costs']=dict(cases=264,best_grammar=128,best_working=245)
    if not args.logic_only:
        table=ROOT/'routing_KSP_best/machine/ksp_250.tm'
        assert sha(table)==EXPECTED_TM
        import emit_basis_table
        with redirect_stdout(io.StringIO()):emit_basis_table.main()
        assert sha(table)==EXPECTED_TM
        audit=read('routing_KSP_best/machine/new_source_machine_audit.json')
        assert audit['status']=='PASS_NEW_SOURCE_AFFINE_AND_BOOT'
        assert audit['working_states']==250 and audit['literal_transition_rows']==500
        assert audit['affine_instruction_audit']['new_program_cases']==8794
        assert audit['blank_boot']['blank_steps']==407915
        result['new_source_machine']=dict(status=audit['status'],working_states=250,
             exact_table_sha256=EXPECTED_TM,bisimulation_pairs=3171,guarded_instruction_cases=8794,
             blank_steps=407915,proof_assistant_endpoint_closed=False)
    if args.searches:
        for name in ('search_basis_orientations.py','search_bundle_shapes.py'):
            subprocess.run([sys.executable,str(ROOT/name)],cwd=ROOT,check=True)
        result['finite_searches']='RECOMPUTED'
    result['status']='PASS_WITH_STATED_SCOPE'
    (ROOT/'portable_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
