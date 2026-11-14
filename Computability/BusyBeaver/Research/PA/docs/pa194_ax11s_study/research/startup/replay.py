#!/usr/bin/env python3
"""Replay scoped finite startup-repair searches; no consistency claim is inferred."""
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile, time

ROOT=Path(__file__).resolve().parent

def run(command):
    result=subprocess.run([str(x) for x in command],text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed:\n{result.stdout}\n{result.stderr}')
    return result

def summary(log):
    line=next(line for line in reversed(log.splitlines()) if line.startswith('DONE '))
    words=line.split()[1:]
    return {words[i]:float(words[i+1]) if words[i]=='seconds' else int(words[i+1]) for i in range(0,len(words),2)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=['pairs74','pairs-all','triples74','helper','helper-window','source-helper','positive-control'],default='pairs-all')
    ap.add_argument('--output',type=Path,required=True,help='Fresh directory for replay logs and receipt.')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    provenance=json.loads((ROOT/'PROVENANCE.json').read_text())
    for name,digest in provenance['hashes'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    source={'positive-control':'search_pairs.cpp','pairs74':'search_pairs.cpp','pairs-all':'search_pairs_all.cpp','triples74':'search_triples.cpp',
            'helper':'synth_merge_helper.cpp','helper-window':'synth_helper_window.cpp','source-helper':'synth_source_helper.cpp'}[a.mode]
    started=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='pa-startup-replay-') as tmp:
        binary=Path(tmp)/'search'
        run(['g++','-O3','-std=c++17',ROOT/source,'-o',binary])
        if a.mode=='positive-control':
            args=[binary,ROOT/'inputs/primary.native.tm',ROOT/'inputs/positive_control.tsv',200000,0,100000,ROOT/'inputs/startup_any_frame_templates.tsv']
        elif a.mode.startswith('pairs') or a.mode.startswith('triples'):
            args=[binary,ROOT/'inputs/runtime193.native.tm',ROOT/'inputs/edits.tsv',200000,0,100000,ROOT/'inputs/startup_any_frame_templates.tsv']
        elif a.mode=='helper':args=[binary,ROOT/'inputs/primary.native.tm']
        elif a.mode=='helper-window':args=[binary,ROOT/'inputs/primary.native.tm',4,100]
        else:args=[binary,ROOT/'inputs/primary.native.tm',ROOT/'inputs/primary_contexts_k4.txt',4,100]
        result=run(args)
    (a.output/'stdout.txt').write_text(result.stdout)
    (a.output/'stderr.txt').write_text(result.stderr)
    receipt={'mode':a.mode,'elapsed_seconds':round(time.monotonic()-started,3),
             'source_sha256':hashlib.sha256((ROOT/source).read_bytes()).hexdigest(),
             'kernel_checked':False,'scope':'Finite bounded search only; no machine correctness or optimality conclusion.'}
    if a.mode=='positive-control' or a.mode.startswith('pairs') or a.mode.startswith('triples'):
        receipt['counts']=summary(result.stderr)
        frozen={'positive-control':'positive_control.log','pairs74':'log.txt','pairs-all':'log_all.txt','triples74':'log_triple.txt'}[a.mode]
        expected=summary((ROOT/'recorded'/frozen).read_text())
        assert {k:v for k,v in receipt['counts'].items() if k!='seconds'}=={k:v for k,v in expected.items() if k!='seconds'}
        if a.mode=='positive-control':
            assert result.stdout==(ROOT/'recorded/positive_control.jsonl').read_text()
        else:
            assert result.stdout=='','A new candidate needs independent review; do not infer a consistency theorem.'
    else:
        frozen={'helper':'helper_solutions.tsv','helper-window':'window_helper_solutions_k4.tsv','source-helper':'source_helper_solutions_k4.tsv'}[a.mode]
        assert result.stdout==(ROOT/'recorded'/frozen).read_text()
        receipt['solutions']=len(result.stdout.splitlines())
    receipt['status']='PASS'
    (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
