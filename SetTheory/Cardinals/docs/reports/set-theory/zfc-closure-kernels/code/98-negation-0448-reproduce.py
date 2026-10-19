#!/usr/bin/env python3
"""Portable certificate replay, with optional bounded search reruns.

The --fine path is explicit: historical absolute paths in JSON are provenance,
never a reason to import a stale checkout. Full binary-frame validation is a
separate driver in ../runtime/validate_emitted.py.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys

HERE=Path(__file__).resolve().parent

def run(args):
    subprocess.run([str(x) for x in args],check=True)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--fine',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--search',action='store_true',help='rerun the timed main searches with the fixed route checker; results need not be byte-identical')
    a=p.parse_args();fine=a.fine.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    assert (fine/'runtime/code/audit_fine_grammar.py').is_file()
    for candidate,backend,name in [
        ('lm-control/grammar.json','lm-backend/backend.json','control-finite.json'),
        ('lm-warm/search0.json','lm-backend/backend.json','lm-final-finite.json'),
        ('lm-dne32-warm/search1.json','lm-dne32-backend/backend.json','lm-dne32-final-finite.json'),
        ('lm-church8-repaired/search0.json','lm-church8-backend/backend.json','lm-church8-final-finite.json')]:
        run([sys.executable,HERE/'audit_lm_grammar.py','--candidate',HERE/candidate,'--backend',HERE/backend,'--fine',fine,'--output',out/name])
    run([sys.executable,HERE/'audit_trace_ideal.py','--candidate',HERE/'dne32/search0.json','--inputs',HERE/'dne32','--fine',fine,'--output',out/'trace-final-finite.json'])
    run([sys.executable,HERE/'audit_router_collection.py','--output',out/'routing-regression.json'])
    run([sys.executable,HERE/'emit_lm_machine.py','--candidate',HERE/'lm-control/grammar.json','--backend',HERE/'lm-backend/backend.json','--fine',fine,'--output',out/'control'])
    names=['machine.tm','machine_old.tm','sites_physical.json','sites_logical.json','allocation.json','renumbering.json','register_bisimulation.json','blank_boot.json']
    hashes={}
    for name in names:
        data=(out/'control'/name).read_bytes()
        assert data==(HERE/'lm-control'/name).read_bytes(),name
        hashes[name]=hashlib.sha256(data).hexdigest()
    report=dict(status='PASS_GRAMMAR_AND_FROZEN_CONTROL_REPLAY',compared_hashes=hashes,scope='Exact archived grammar, changed-source reassociation and literal blank-start replay. Run the separate all-values frame validator for the complete runtime gate.')
    (out/'replay-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    if a.search:
        run(['g++','-O3','-std=c++17',HERE/'anneal_fine_routing_closed.cpp','-o',out/'anneal_fine'])
        run(['g++','-O3','-std=c++17',HERE/'anneal_trace_ideal.cpp','-o',out/'anneal_trace_ideal'])
        for folder,backend,seconds,seed,stem in [('lm-warm','lm-backend',360,130237218,'lm'),('lm-dne32-warm','lm-dne32-backend',180,32218237,'lm-dne32'),('lm-church8-repaired','lm-church8-backend',90,82004238,'lm-church8')]:
            base=HERE/folder
            args=[out/'anneal_fine',base/'grammar.txt',base/'constraints.txt',out/(stem+'-search.json'),seconds,seed,127,base/'locks.txt',base/'resume.txt']
            with (out/(stem+'-search.log')).open('w') as log:
                subprocess.run(list(map(str,args)),stdout=log,stderr=subprocess.STDOUT,check=True)
            run([sys.executable,HERE/'audit_lm_grammar.py','--candidate',out/(stem+'-search.json'),'--backend',HERE/backend/'backend.json','--fine',fine,'--output',out/(stem+'-search-audit.json')])
        base=HERE/'dne32'
        args=[out/'anneal_trace_ideal',base/'trace-grammar.txt',base/'constraints.txt',out/'trace-search.json',360,61018132,127,base/'locks.txt',base/'resume.txt',base/'trace-info.txt',base/'pairs.txt']
        with (out/'trace-search.log').open('w') as log:
            subprocess.run(list(map(str,args)),stdout=log,stderr=subprocess.STDOUT,check=True)
        run([sys.executable,HERE/'audit_trace_ideal.py','--candidate',out/'trace-search.json','--inputs',HERE/'dne32','--fine',fine,'--output',out/'trace-search-audit.json'])
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
