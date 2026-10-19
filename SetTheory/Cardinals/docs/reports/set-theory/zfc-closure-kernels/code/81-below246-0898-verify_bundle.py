#!/usr/bin/env python3
"""Replay the positive proofs and expected negative compilation diagnostic.

This is not a theorem that any new <246-state machine is a consistency machine.
All programs use the Python standard library. Search benchmarks are optional.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'sources/context246/zfc-context246'
LOG=ROOT/'_recheck'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if not __debug__:
        raise SystemExit('Assertions are required: run without -O.')
    LOG.mkdir(exist_ok=True)
    assert sha(BASE/'sources/Prog254.v')=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
    assert sha(BASE/'machine/zfc_prefix246_old.tm')=='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
    assert sha(ROOT/'agent_logic/rotation_zero_candidate_24.json')=='90d15a0fb69606e080a5fa5d2ce5179f2642958546a4f1203b259b2804eb76af'
    records=[]
    def run(label, script, *args):
        start=time.monotonic()
        result=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],
                              cwd=ROOT,text=True,capture_output=True)
        (LOG/(label+'.log')).write_text(result.stdout+result.stderr)
        records.append(dict(check=label,returncode=result.returncode,
                            seconds=round(time.monotonic()-start,3)))
        print(label, 'PASS' if result.returncode==0 else 'FAIL',flush=True)
        if result.returncode:
            raise SystemExit(f'{label} failed; see _recheck/{label}.log')
    run('reference_rebuild',BASE/'code/rebuild_machines.py','--check')
    run('reference_macro_inductions',BASE/'code/check_macro_inductions.py')
    run('reference_affine',BASE/'code/review_affine_source.py',
        '--program',BASE/'sources/Prog254.v',
        '--sites',BASE/'sources/instruction-sites-physical.json',
        '--table',BASE/'machine/zfc_prefix246_old.tm',
        '--checker',BASE/'sources/prior/prefix_affine.py',
        '--output',LOG/'reference_affine.json')
    run('source_reassociation',ROOT/'agent_logic/rotation245_source_audit.py')
    run('source_zero_six',ROOT/'agent_logic/rotation_zero_source_audit.py')
    run('protected_source_frontier',ROOT/'agent_logic/protected_frontier_audit.py')
    run('colored_context_source',ROOT/'agent_logic/colored_context_source_audit.py')
    run('rocq_source_data_export',ROOT/'export_sources.py')
    run('arbitrary_root_phase',ROOT/'agent_logic/audit_phase.py')
    run('phase_erasure',ROOT/'agent_logic/erase_known_zero_loops.py')
    run('neutral_macro_inductions',ROOT/'agent_macros/check_neutral_macros.py',BASE)
    run('neutral_affine_sites',ROOT/'agent_macros/check_neutral_sites.py',BASE)
    run('expected_counterexample',ROOT/'agent_states/rotation_counterexample.py')
    run('expected_scanner_obstruction',ROOT/'agent_macros/check_short_scanner.py',
        '--table',ROOT/'agent_macros/scanner8_baseline245.tm',
        '--baseline',BASE,'--output',LOG/'scanner8_baseline245_audit.json')
    scanner=json.loads((LOG/'scanner8_baseline245_audit.json').read_text())
    assert scanner['status']=='FAIL'
    assert scanner['register_inductions']['status']=='PASS'
    assert scanner['instruction_frames']['universally_verified_cases']==8355
    assert len(scanner['instruction_frames']['failures'])==36
    run('compiled_zero_six_runtime',ROOT/'agent_macros/check_short_scanner.py',
        '--table',ROOT/'agent_macros/compiled24_scanner250.tm',
        '--graph',ROOT/'agent_logic/rotation_zero_candidate_24.json',
        '--baseline',BASE,'--output',LOG/'compiled24_scanner250_audit.json')
    compiled=json.loads((LOG/'compiled24_scanner250_audit.json').read_text())
    assert compiled['status']=='PASS' and compiled['working_states']==250
    assert compiled['instruction_frames']['universally_verified_cases']==8391
    run('colored_context_runtime',ROOT/'agent_macros/check_colored_runtime.py',
        '--table',ROOT/'agent_states/colored_context_candidate_003.tm',
        '--graph',ROOT/'agent_states/colored_context_candidate_003.json',
        '--baseline',BASE,'--output',LOG/'colored_context246_audit.json')
    colored=json.loads((LOG/'colored_context246_audit.json').read_text())
    assert colored['status']=='PASS' and colored['working_states']==246
    assert colored['instruction_frames']['universally_verified_cases']==8391
    run('expected_colored_scanner_obstruction',ROOT/'agent_macros/check_colored_runtime.py',
        '--table',ROOT/'agent_states/colored_context003_scanner245.tm',
        '--graph',ROOT/'agent_states/colored_context_candidate_003.json',
        '--scanner-zeros','8','--baseline',BASE,
        '--output',LOG/'colored_context245_audit.json')
    colored_short=json.loads((LOG/'colored_context245_audit.json').read_text())
    assert colored_short['status']=='FAIL' and colored_short['working_states']==245
    assert colored_short['instruction_frames']['universally_verified_cases']==8361
    assert len(colored_short['instruction_frames']['failures'])==30
    run('new_constructions_blank_prefixes',ROOT/'agent_states/check_blank_prefix.py',
        '--reference',BASE/'machine/zfc_prefix246_old.tm',
        '--table',ROOT/'agent_states/colored_context_candidate_003.tm',
        '--table',ROOT/'agent_macros/compiled24_scanner250.tm',
        '--output',LOG/'blank_prefix_results.json')
    prefixes=json.loads((LOG/'blank_prefix_results.json').read_text())
    assert prefixes['status']=='PASS'
    for row,states,steps in zip(prefixes['outcomes'],(246,250),(410735,407983)):
        assert row['status']=='PASS' and row['working_states']==states
        assert row['first_exact_frame']==steps and row['complete_tape_equals_target']
        assert row['safe_root']['zero_everywhere_else']
    sys.path.insert(0,str(ROOT/'agent_states'))
    import audit245_dense as dense
    boot=dense.bootstrap(dense.read_table(dense.TABLE))
    assert boot['steps']==410735 and boot['modified_state178_never_visited']
    (LOG/'rejected245_blank_prefix.json').write_text(json.dumps(boot,indent=2)+'\n')
    print('rejected245_blank_prefix PASS (initialization only)',flush=True)
    counter=json.loads((ROOT/'agent_states/rotation_counterexample.json').read_text())
    assert counter['status']=='COUNTEREXAMPLE_TO_ADVERTISED_INSTRUCTION_CONTRACT'
    output=dict(status='PASS_RESEARCH_CERTIFICATES_AND_EXPECTED_COUNTEREXAMPLE',
        new_sub246_consistency_machine_claim=False,
        proof_assistant_endpoint_built=False,
        checks=records,
        source_result=dict(unique_pairs=202,maximum_zero_run=6,instruction_leaves=6460,guarded_cases=8391),
        rejected_candidate=dict(working_states=245,blank_prefix_steps=410735,
            runtime_status=counter['status']),
        short_scanner=dict(proved_instruction_cases=8355,failed_instruction_cases=36,
            whole_machine_certified=False),
        compiled_source_runtime=dict(working_states=250,proved_instruction_cases=8391,
            register_inductions='PASS',blank_initializer_certified=True,
            blank_prefix_steps=407983,blank_halting_equivalent_to_reference=True),
        colored_context_runtime=dict(working_states=246,proved_instruction_cases=8391,
            register_inductions='PASS',blank_initializer_certified=True,
            blank_prefix_steps=410735,blank_halting_equivalent_to_reference=True),
        colored_short_scanner=dict(working_states=245,proved_instruction_cases=8361,
            failed_instruction_cases=30,whole_machine_certified=False))
    (LOG/'verification_summary.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
