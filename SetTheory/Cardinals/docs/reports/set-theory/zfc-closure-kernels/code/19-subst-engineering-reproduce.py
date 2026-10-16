#!/usr/bin/env python3
"""Regenerate and independently verify the selected268-state control offline.

Default is one fixed recipe, taking only seconds. --full-grid repeats the
53,760-choice source search; --psc-controls additionally repeats8,192 PSC
grammar choices. No network, Git checkout, theorem prover or pip package is
used. Only the selected output directory (or a temporary directory) is written.
"""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys, tempfile, time
from pathlib import Path
import verify

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--full-grid',action='store_true')
    ap.add_argument('--psc-controls',action='store_true')
    args=ap.parse_args()
    if not __debug__:ap.error('run without -O; finite checking uses assertions')
    verify.pinned_inputs()
    temp=None
    if args.output:
        out=args.output.resolve()
        if out==HERE or HERE in out.parents:
            ap.error('output must be outside the packaged engineering directory')
        out.mkdir(parents=True,exist_ok=True)
    else:
        temp=tempfile.TemporaryDirectory(prefix='zfc-engineering268-')
        out=Path(temp.name)
    begin=time.monotonic()
    command=[sys.executable,'-B',str(HERE/'full_logic_search.py'),'--output',str(out),
             '--iterations','0']
    if args.full_grid:command.extend(['--conjunction-grid','--original-baseline'])
    subprocess.run(command,cwd=HERE,check=True)
    compared=[]
    for name in ('full_logic_best.tm','full_logic_best.named.tm','full_logic_best.labels.json',
                 'full_logic_best.dag.json','full_logic_reference.dag.json','full_logic_rm_certificate.json'):
        if (out/name).read_bytes()!=(HERE/'artifacts'/name).read_bytes():
            raise ValueError('regeneration differs from stored artifact: '+name)
        compared.append(name)
    result=verify.verify(out,False)
    if args.psc_controls:
        psc_out=out/'psc_controls'
        subprocess.run([sys.executable,'-B',str(HERE/'full_logic_psc_controls.py'),
            '--repo',str(HERE/'vendor/proveit'),'--prior',str(HERE/'vendor/one_schema_machine'),
            '--output',str(psc_out),'--seeds','512'],cwd=HERE,check=True)
        actual=json.loads((psc_out/'full_logic_psc_results.json').read_text())
        expected=json.loads((HERE/'artifacts/full_logic_psc_results.json').read_text())
        for name,row in actual['results'].items():
            for field in ('minimum_working_states','grammar_seed','grammar_alpha','search_cases',
                          'cost_distribution','macro_word','table'):
                if row[field]!=expected['results'][name][field]:
                    raise ValueError('PSC control differs: '+name+'/'+field)
        result['PSC_controls_reproduced']=True
    result.update({'regenerated_files_identical':compared,
                   'full_grid_repeated':args.full_grid,'elapsed_seconds':time.monotonic()-begin,
                   'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
    (out/'offline_reproduction.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
    if temp:temp.cleanup()

if __name__=='__main__':main()
