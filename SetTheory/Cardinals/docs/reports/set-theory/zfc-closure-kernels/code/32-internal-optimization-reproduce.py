#!/usr/bin/env python3
"""Offline finite replay of the optimization evidence; no unbounded proof search.

The default command verifies the selected artifacts. It does not repeat the
50,000-rotation heuristic or any 100-million/billion-step bootstrap search.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def run(args,cwd=None):
    result=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=cwd or ROOT,
                          check=True,capture_output=True,text=True)
    return result.stdout
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    parser.add_argument('--bootstrap-four-million',action='store_true',
                        help='also replay the literal 4,000,000-step Python diagnostic')
    args=parser.parse_args()
    if not __debug__:
        parser.error('run without -O or -OO; the checks use assertions')
    manifest=json.loads((ROOT/'source_manifest.json').read_text())
    for rec in manifest['files']:
        path=ROOT/rec['path']
        assert path.stat().st_size==rec['bytes'], rec['path']
        assert digest(path)==rec['sha256'], rec['path']
    evidence={'source_manifest_files_verified':len(manifest['files']),
              'no_network_required':True,'new_consistency_machine_bound':False}
    for script,output,key in [
        ('search_tail_entries.py','tail_entry_results.json','tail_entry_search'),
        ('audit_tail252.py','tail252_audit.json','decrement_macro'),
        ('runtime252_site_replay.py','runtime252_site_check.json','runtime_sites')]:
        expected=(ROOT/output).read_bytes()
        run([ROOT/script])
        assert (ROOT/output).read_bytes()==expected, output
        evidence[key]=json.loads(expected)
    evidence['bootstrap_inputs']=json.loads(run([ROOT/'bootstrap/verify_inputs.py']))
    with tempfile.TemporaryDirectory(prefix='zfc-opt-replay-') as temp:
        temp=Path(temp)
        control=temp/'control268'
        run([ROOT/'vendor/source19/full_logic_search.py',
             '--repo',ROOT/'vendor/proveit','--prior',ROOT/'vendor/one_schema_machine',
             '--output',control,'--iterations','0'])
        names=['full_logic_best.named.tm','full_logic_best.tm',
               'full_logic_best.labels.json','full_logic_best.dag.json',
               'full_logic_reference.dag.json','full_logic_rm_certificate.json']
        for name in names:
            assert (control/name).read_bytes()==(ROOT/'control268'/name).read_bytes(),name
            assert (ROOT/'schema_search'/name).read_bytes()==(ROOT/'control268'/name).read_bytes(),name
        expected=json.loads((ROOT/'control268/full_logic_results.json').read_text())
        actual=json.loads((control/'full_logic_results.json').read_text())
        variable={'elapsed_seconds','generator_sha256','prior_repair_sha256'}
        assert {k:v for k,v in expected.items() if k not in variable}=={
            k:v for k,v in actual.items() if k not in variable}
        assert actual['generator_sha256']==digest(ROOT/'vendor/source19/full_logic_search.py')
        assert actual['prior_repair_sha256']==digest(ROOT/'vendor/one_schema_machine/rebracket_axioms.py')
        assert expected['generator_sha256']==hashlib.sha256((ROOT/'vendor/source19/full_logic_search.py').read_bytes()+b'\n').hexdigest()
        assert expected['prior_repair_sha256']==hashlib.sha256((ROOT/'vendor/one_schema_machine/rebracket_axioms.py').read_bytes()+b'\n').hexdigest()
        independent=json.loads(run([
            ROOT/'vendor/source19/verify_schema_rm_certificate.py',
            '--prior-machine-dir',ROOT/'vendor/one_schema_machine',
            '--reference',control/'full_logic_reference.dag.json',
            '--candidate',control/'full_logic_best.dag.json',
            '--certificate',control/'full_logic_rm_certificate.json']))
        evidence['control268']={
            'working_states':actual['table']['working_states'],
            'transition_rows':actual['table']['transition_rows_after'],
            'numeric_table_sha256':digest(control/'full_logic_best.tm'),
            'exact_artifacts_reproduced':names,
            'independent_rm_certificate':independent,
            'packaged_driver_sha256':actual['generator_sha256'],
            'packaged_prior_helper_sha256':actual['prior_repair_sha256'],
            'historical_driver_sha256':expected['generator_sha256'],
            'historical_prior_helper_sha256':expected['prior_repair_sha256'],
            'metadata_note':'Historical driver and helper each had one extra trailing LF; exact pinned originals give identical emitted artifacts.'}
        rotations=temp/'rotations0'
        run([ROOT/'rotate_slp.py','--input',ROOT/'control268/full_logic_best.dag.json',
             '--output',rotations,'--iterations','0','--seed','20261016'])
        assert (rotations/'best.dag.json').read_bytes()==(ROOT/'rotations268/best.dag.json').read_bytes()
        evidence['rotation_selected_artifact']={
            'best_dag_sha256':digest(rotations/'best.dag.json'),
            'states_predicted':json.loads((rotations/'search.json').read_text())['records'][0]['states_predicted'],
            'heuristic_iterations_replayed':0,
            'historical_search_iterations':50000}
    if args.bootstrap_four_million:
        expected=(ROOT/'bootstrap/candidate252_tail_boot.json').read_bytes()
        run([ROOT/'bootstrap/candidate252_tail.py'])
        assert (ROOT/'bootstrap/candidate252_tail_boot.json').read_bytes()==expected
        evidence['literal_bootstrap_four_million']=json.loads(expected)
    else:
        evidence['literal_bootstrap_four_million']='optional; not rerun by this invocation'
    text=json.dumps(evidence,indent=2,sort_keys=True)+'\n'
    if args.record:
        args.record.write_text(text)
    print(json.dumps({
        'source_files':evidence['source_manifest_files_verified'],
        'tail_entries_tested':evidence['tail_entry_search']['candidates_checked'],
        'macro_cases':evidence['decrement_macro']['cases'],
        'symbolic_site_cases':sum(evidence['runtime_sites']['results'].values()),
        'control_working_states':evidence['control268']['working_states'],
        'independent_rm_pairs':evidence['control268']['independent_rm_certificate']['related_pairs'],
        'rotation_search_repeated':False,
        'new_consistency_machine_bound':False},indent=2))
if __name__=='__main__':
    main()
