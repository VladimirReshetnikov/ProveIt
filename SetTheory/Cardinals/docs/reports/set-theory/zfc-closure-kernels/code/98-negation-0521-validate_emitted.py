#!/usr/bin/env python3
"""Run both exact-table dynamic runtime audits on an emitted source candidate.

All paths are supplied explicitly. This orchestration does not alter any proof
rule, source reference, machine table, or inherited input file.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime',required=True,type=Path)
    p.add_argument('--machine',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--padding',type=int,default=64)
    a=p.parse_args();assert __debug__
    here=Path(__file__).resolve().parent;m=a.machine.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    files={name:m/name for name in ('machine_old.tm','machine.tm','renumbering.json','sites_logical.json','sites_physical.json','blank_boot.json')}
    for f in files.values():assert f.is_file(),f
    whole=[sys.executable,'-B',str(here/'whole_frame_dynamic.py'),'--runtime',str(a.runtime.resolve()),'--table',str(files['machine_old.tm']),'--sites',str(files['sites_physical.json']),'--padding',str(a.padding),'--output',str(out/'whole-frame.json')]
    if (m/'modified_source.json').is_file():whole+=['--source-reference',str(m/'modified_source.json')]
    independent=[sys.executable,'-B',str(here/'audit_frame_dynamic.py'),'--old-table',str(files['machine_old.tm']),'--table',str(files['machine.tm']),'--renumbering',str(files['renumbering.json']),'--logical-sites',str(files['sites_logical.json']),'--physical-sites',str(files['sites_physical.json']),'--bootstrap',str(files['blank_boot.json']),'--padding',str(a.padding),'--whole-frame-report',str(out/'whole-frame.json'),'--output',str(out/'independent-frame-audit.json')]
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';runs=[]
    for name,cmd in (('whole-frame',whole),('independent-frame-audit',independent)):
        print('Running',name,flush=True)
        log=out/(name+'.log')
        with log.open('w') as stream:result=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT,env=env)
        runs.append(dict(name=name,argv=cmd,returncode=result.returncode,log=str(log)))
        manifest=dict(status='PASS' if len(runs)==2 and result.returncode==0 else 'INCOMPLETE',runs=runs,input_sha256={name:hashlib.sha256(f.read_bytes()).hexdigest() for name,f in files.items()})
        (out/'validation-reproduction.json').write_text(json.dumps(manifest,indent=2)+'\n')
        if result.returncode:
            print(log.read_text()[-10000:]);raise SystemExit(result.returncode)
    print(json.dumps(manifest,indent=2))

if __name__=='__main__':main()
