#!/usr/bin/env python3
"""Validate and reproduce this release without modifying its delivered files."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile

ROOT=Path(__file__).resolve().parent

def need(condition,message):
    if not condition:raise ValueError(message)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--report',type=Path)
    args=parser.parse_args()
    manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
    for rel,digest in manifest['files'].items():
        path=ROOT/rel
        need(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==digest,'release integrity: '+rel)
    receipt={'status':'PASS','manifest_files':len(manifest['files']),
             'scope':'finite reproduction and transcription checks; see ordinary proofs for semantics',
             'checks':[]}
    with tempfile.TemporaryDirectory(prefix='conzfc-shared-') as tmp:
        work=Path(tmp)/'release'
        shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.aux','*.log','*.toc','*.out'))
        commands=[
            ('direct complete coefficient/restoration/text audit', ['direct/verify.py']),
            ('direct smaller-height companion', ['direct/verify.py','--equation','direct/equation320']),
            ('direct semantic regression', ['direct/check_semantics.py']),
            ('direct regeneration', ['direct/reproduce.py']),
            ('direct optimized regeneration', ['-O','direct/reproduce.py']),
            ('norm finite identities and numeral reconstruction', ['norm/check.py']),
            ('norm optimized finite identities', ['-O','norm/check.py']),
            ('product finite identities and degrees', ['lowops/check.py']),
            ('product optimized finite identities', ['-O','lowops/check.py']),
        ]
        for label,cmd in commands:
            result=subprocess.run([sys.executable,'-B',*cmd],cwd=work,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
            need(result.returncode==0,label+' failed:\n'+result.stdout[-12000:])
            receipt['checks'].append({'name':label,'status':'PASS',
                'output_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()})
        # Rebuild the new integer DAGs and compare all declared outputs.
        for part in ('norm','lowops'):
            directory=work/part
            before={p.name:p.read_bytes() for p in directory.glob('*.json')
                    if p.name not in ('CHECK.json','CHECK_OPTIMIZED.json','CHECKS.json','CHECKS_OPTIMIZED.json')}
            result=subprocess.run([sys.executable,'-B','build.py'],cwd=directory,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
            need(result.returncode==0,part+' rebuild failed: '+result.stdout[-5000:])
            for name,data in before.items():
                need((directory/name).read_bytes()==data,part+' byte-identical rebuild: '+name)
            receipt['checks'].append({'name':part+' complete DAG rebuild','status':'PASS','json_files_compared':len(before)})
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
