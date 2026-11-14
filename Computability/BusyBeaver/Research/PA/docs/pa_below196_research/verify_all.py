#!/usr/bin/env python3
"""Run portable finite checks without mutating the supplied evidence."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def manifest_check():
    p=HERE/'SHA256SUMS.json'
    if not p.exists():return {'status':'NOT_PRESENT_DURING_INITIAL_BUILD'}
    d=json.loads(p.read_text())
    for name,digest in d['files'].items():
        f=HERE/name
        need(f.is_file(),f'missing file: {name}')
        need(hashlib.sha256(f.read_bytes()).hexdigest()==digest,f'changed bytes: {name}')
    return {'status':'PASS','files':len(d['files'])}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    need(__debug__ and not sys.flags.optimize,'Run with Python assertions enabled, without -O or -OO.')
    integrity=manifest_check()
    tasks=[
      ('census','census',['verify_census.py']),
      ('gate_spelling_and_minimum','theory',['gate_variants.py','--output','gate_variants.json']),
      ('membership_config','theory',['membership_transpose_config.py']),
      ('orientation_recoding','theory',['orientation_recoding.py']),
      ('direct_reversed_pair_macro','theory',['transposed_implication_macro.py','--output','transposed_implication_macro.json']),
      ('transposed_implication_prefix','theory',['implication_transpose_words.py','--output','implication_transpose_words.json']),
      ('head_counterinterpretation','theory',['head1_countermodel.py']),
      ('guard_source_transport','physical_search',['verify_guard.py']),
      ('eight_gate_reader_scores','gate_search',['verify_gate_score.py']),
      ('membership_reader_scores','membership_search',['verify_membership_score.py']),
    ]
    results=[]
    with tempfile.TemporaryDirectory(prefix='pa196-portable-check-') as td:
        root=Path(td)
        for name in sorted({t[1] for t in tasks}):
            shutil.copytree(HERE/name,root/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for label,directory,cmd in tasks:
            cp=subprocess.run([sys.executable,'-B',*cmd],cwd=root/directory,text=True,capture_output=True)
            if cp.returncode:
                print(cp.stdout,file=sys.stderr);print(cp.stderr,file=sys.stderr)
                raise RuntimeError(f'Check failed: {label}')
            results.append({'check':label,'status':'PASS'})
            print(label+': PASS',flush=True)
        spec=importlib.util.spec_from_file_location('physical_replay',root/'physical_search/replay.py')
        mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
        controls=mod.independent_controls()
        need(controls=={'two_row_seven_cell_cases':512,'displaced_five_cell_cases':160},'control case census changed')
        results.append({'check':'independent_local_fold_controls','status':'PASS','cases':controls})
    result={'status':'PASS','integrity':integrity,'checks':results,
            'scope':'Finite table census, source identities, local formula/macro transcription, exact emitter ASTs, reader-score verification and independent synthetic controls. No new sub-196 machine, full Lean build, complete physical-search rerun or PA consistency biconditional.'}
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
