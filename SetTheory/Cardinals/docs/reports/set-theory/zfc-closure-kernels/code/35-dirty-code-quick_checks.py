#!/usr/bin/env python3
"""Run the small, portable executable checks, without Lean or the large search."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time

def main():
    if not __debug__:raise SystemExit('Run without -O: checked contracts use assertions.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=Path)
    a=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    output=(a.output_dir or root/'replay/quick').resolve();output.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((root/'source_manifest.json').read_text())
    for e in manifest['sources']:
        f=root/e['bundle_path']
        if hashlib.sha256(f.read_bytes()).hexdigest()!=e['sha256']:
            raise SystemExit('Source hash mismatch: '+e['bundle_path'])
    jobs=[
        ('dirty-prefix',[sys.executable,str(root/'code/check_dirty_prefix.py'),
          str(root/'vendor/busy-beaver/ZF/m254/coq/prog/Dag254.v'),'--output',str(output/'dirty-prefix.json')],root),
        ('direction-variant',[sys.executable,str(root/'optimization/verify_direction_variant.py'),
          str(root/'machines/zfc_253.tm'),str(root/'machines/zfc_253_direction_rewrite.tm'),
          str(root/'optimization/direction_rewrite_certificate.json'),'--output',str(output/'direction-variant.json')],root),
        ('adversarial-tests',[sys.executable,'-m','unittest','test_edge_replacement.py','-v'],root/'optimization'),
    ]
    audit={'scope':'Executable finite checks; proof scopes are documented separately.','checks':[]}
    for name,command,cwd in jobs:
        start=time.monotonic()
        r=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (output/(name+'.log')).write_text(r.stdout)
        audit['checks'].append({'name':name,'returncode':r.returncode,'seconds':round(time.monotonic()-start,3)})
        (output/'quick_audit.json').write_text(json.dumps(audit,indent=2)+'\n')
        print(f'{name}: exit {r.returncode}',flush=True)
        if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
    audit['status']='PASS'
    (output/'quick_audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    print('PASS: source hashes, 5096 exact prefix cases, variant certificate and nine adversarial tests.')

if __name__=='__main__':main()
