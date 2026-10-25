#!/usr/bin/env python3
"""Portable independent replay and optional byte-for-byte reconstruction."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile

ROOT=Path(__file__).resolve().parents[1]
CODE=ROOT/'code'
FLAGS=['-B']+(['-O'] if sys.flags.optimize else [])

def need(b,m):
    if not b:raise ValueError(m)

def run(script,*args):
    p=subprocess.run([sys.executable,*FLAGS,str(CODE/script),*map(str,args)],capture_output=True,text=True,cwd=ROOT)
    need(p.returncode==0,p.stdout+'\n'+p.stderr)
    return p.stdout

def check_pins():
    pins=json.loads((ROOT/'upstream/SOURCE_PINS.json').read_text())
    hashes=[('upstream/parent/source.json',pins['parent_source_sha256']),('upstream/parent/transform_certificate.json',pins['parent_transform_sha256'])]
    hashes.extend((p['local_path'],p['sha256']) for p in pins['retained_proof_closure'])
    for path,digest in hashes:need(hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,'Upstream pin mismatch: '+path)
    return len(hashes)

def compare_dir(fresh,stored):
    fs=sorted(p.name for p in fresh.glob('*.json'));ss=sorted(p.name for p in stored.glob('*.json'))
    need(fs==ss,'JSON file census differs')
    for n in fs:need((fresh/n).read_bytes()==(stored/n).read_bytes(),'Byte mismatch: '+str(stored/n))
    return len(fs)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path)
    a=p.parse_args()
    output={'status':'PASS','optimized':bool(sys.flags.optimize),'upstream_pinned_files':check_pins()}
    output['independent_audit']=json.loads(run('check.py'))
    output['negative_controls']=json.loads(run('check_controls.py','--source-dir',ROOT/'data','--endpoint-dir',ROOT/'equation'))
    if a.rebuild:
        with tempfile.TemporaryDirectory(prefix='normalized_conzfc_rebuild_') as tmp:
            tmp=Path(tmp);data=tmp/'data';end=tmp/'equation'
            run('build.py',data,'--scale-digits')
            run('center_integer.py',data,end)
            count=compare_dir(data,ROOT/'data')+compare_dir(end,ROOT/'equation')
            fresh=json.loads(run('check.py','--source-dir',data,'--endpoint-dir',end))
            output['rebuild']={'identical_json_files':count,'independent_audit_status':fresh['status']}
    output['equation_sha256']=hashlib.sha256((ROOT/'equation/equation.json').read_bytes()).hexdigest()
    output['expanded_polynomial_sha256']=hashlib.sha256((ROOT/'equation/expanded_polynomial.json').read_bytes()).hexdigest()
    text=json.dumps(output,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
