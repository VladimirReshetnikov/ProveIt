#!/usr/bin/env python3
"""Fast, offline checks of the stored268-state engineering artifacts.

The RM verification subprocess uses only the prior independent path engine,
not the formula emitter, grammar generator or TMBuilder. The format/hash
checks here likewise do not import those components. Python3.10+; no packages.
"""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
TABLE_SHA='77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def pinned_inputs():
    manifest=json.loads((HERE/'PINNED_INPUTS.json').read_text())
    for rel,digest in manifest.items():
        path=HERE/rel
        if not path.is_file() or sha(path)!=digest:
            raise ValueError('pinned input differs: '+rel)
    return len(manifest)

def run_json(command):
    result=subprocess.run(command,cwd=HERE,text=True,capture_output=True,check=True)
    return json.loads(result.stdout)

def verify(artifacts,check_stored_manifest=True):
    if not __debug__:raise RuntimeError('run without -O; the independent engine uses assertions')
    input_count=pinned_inputs()
    if check_stored_manifest:
        for rel,digest in json.loads((HERE/'ARTIFACT_SHA256.json').read_text()).items():
            if sha(HERE/rel)!=digest:raise ValueError('stored artifact differs: '+rel)
    table=artifacts/'full_logic_best.tm'
    if sha(table)!=TABLE_SHA:raise ValueError('selected numeric table differs')
    rows={};start=None
    for lineno,line in enumerate(table.read_text().splitlines(),1):
        if line.startswith('#!'):
            if start is not None or line!='#! start 0':raise ValueError('invalid start directive')
            start=0;continue
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,target=line.split()
        q,target=int(q),int(target)
        if (q,b) in rows:raise ValueError('duplicate transition')
        if b not in ('0','1') or w not in ('0','1') or d not in ('L','R'):
            raise ValueError('nonstandard binary transition')
        if not 0<=target<=268:raise ValueError('target out of range')
        rows[q,b]=(w,d,target)
    if start!=0 or set(rows)!={(q,b) for q in range(268) for b in ('0','1')}:
        raise ValueError('table is not exactly total on268 working states')
    rm=run_json([sys.executable,'-B',str(HERE/'verify_schema_rm_certificate.py'),
        '--prior-machine-dir',str(HERE/'vendor/one_schema_machine'),
        '--reference',str(artifacts/'full_logic_reference.dag.json'),
        '--candidate',str(artifacts/'full_logic_best.dag.json'),
        '--certificate',str(artifacts/'full_logic_rm_certificate.json')])
    if not rm['verified'] or rm['related_pairs']!=4533:
        raise ValueError('unexpected independent RM result')
    with tempfile.TemporaryDirectory(prefix='psc-identity-check-') as tmp:
        identity=run_json([sys.executable,'-B',str(HERE/'psc_identity_model.py'),
            '--repo',str(HERE/'vendor/proveit'),'--output',str(Path(tmp)/'identity.json')])
    return {'verified':True,'pinned_input_files':input_count,
            'working_states':268,'transition_rows':536,'start':0,'halt':268,
            'numeric_table_sha256':sha(table),'independent_rm':rm,
            'PSC_identity_model':identity,'binary_TM_compiler_proved':False,
            'new_ZFC_state_bound_claimed':False}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--artifacts',type=Path,default=HERE/'artifacts')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    result=verify(args.artifacts.resolve(),args.artifacts.resolve()==(HERE/'artifacts').resolve())
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(encoded)
    print(encoded,end='')

if __name__=='__main__':main()
