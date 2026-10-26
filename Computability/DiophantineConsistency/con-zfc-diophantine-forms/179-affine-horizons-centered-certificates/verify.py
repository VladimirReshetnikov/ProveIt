#!/usr/bin/env python3
"""Authenticate and replay the sealed release in independent disposable copies."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
EXCLUDED={'MANIFEST_SHA256.json','FINAL_REPLAY.json','ZIP_REPLAY.json'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file() and str(p.relative_to(root)) not in EXCLUDED}
def integrity(root,manifest):
    actual=inventory(root)
    if actual!=manifest:
        missing=sorted(set(manifest)-set(actual));extra=sorted(set(actual)-set(manifest))
        changed=sorted(k for k in set(actual)&set(manifest) if actual[k]!=manifest[k])
        raise ValueError(f'Integrity failure: missing={missing[:8]}, extra={extra[:8]}, changed={changed[:8]}')
def controls(root,manifest):
    target=root/'README.md';original=target.read_bytes();passed=[]
    for label,change,restore in [
        ('changed byte',lambda:target.write_bytes(original+b'\ncorrupt'),lambda:target.write_bytes(original)),
        ('missing file',lambda:target.unlink(),lambda:target.write_bytes(original)),
        ('unlisted file',lambda:(root/'UNLISTED.txt').write_text('x'),lambda:(root/'UNLISTED.txt').unlink())]:
        change()
        try:
            try:integrity(root,manifest)
            except ValueError:passed.append(label)
            else:raise ValueError('Corruption accepted: '+label)
        finally:restore()
    integrity(root,manifest);return passed
PLAN=[
 ('integer','verify.py','--parent'),
 ('natural','verify.py'),
 ('natural','inherited/verify.py','--rebuild'),
 ('positive','build.py','--check'),
 ('positive','verify.py'),
 ('positive','start_marker4177/build.py','--check'),
 ('positive','start_marker4177/verify.py'),
 ('positive','build_variants.py','--check'),
 ('positive','verify_variants.py'),
 ('roots','build.py','--check'),
 ('roots','check.py'),
 ('roots','reconstruct_coefficients.py'),
 ('positive','late172/build.py','--check'),
 ('positive','late172/verify.py','--deep','--mutations'),
 ('positive','late172/parent/build.py','--check'),
 ('positive','late172/parent/verify.py','--deep','--mutations'),
 ('reviews','check_printed_coefficient_recipes.py'),
 ('reviews','check_article_metrics.py'),
]

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['both','normal','optimized'],default='both');p.add_argument('--receipt',type=Path);a=p.parse_args()
    manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text());integrity(ROOT,manifest)
    modes=['normal','optimized'] if a.mode=='both' else [a.mode]
    result={'status':'PASS','sealed_files':len(manifest),'modes':{},'scope':'Exact artifact and finite algebra replay; unbounded arithmetic and logical calibration are proved separately in the report and retained sources.'}
    for mode in modes:
        with tempfile.TemporaryDirectory(prefix='conzfc-affine-centered-') as td:
            copy=Path(td)/'release';shutil.copytree(ROOT,copy);integrity(copy,manifest)
            records=[];env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
            for component,script,*args in PLAN:
                command=[sys.executable,'-B']+(['-O'] if mode=='optimized' else [])+[str(copy/component/script)]+args
                start=time.monotonic();r=subprocess.run(command,cwd=copy/component,env=env,text=True,capture_output=True)
                if r.returncode:
                    raise RuntimeError(f'{mode}/{component}/{script} exited {r.returncode}\n{r.stdout[-16000:]}\n{r.stderr[-16000:]}')
                records.append({'component':component,'script':script,'arguments':args,'exit_code':r.returncode,'stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'elapsed_seconds':round(time.monotonic()-start,3)})
                print(mode,component,script,'PASS',flush=True)
            integrity(copy,manifest)
            rejected=controls(copy,manifest)
            result['modes'][mode]={'stages':records,'all_sealed_bytes_unchanged':True,'integrity_controls_rejected':rejected}
    integrity(ROOT,manifest)
    result['successful_stages']=sum(len(x['stages']) for x in result['modes'].values())
    text=json.dumps(result,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
