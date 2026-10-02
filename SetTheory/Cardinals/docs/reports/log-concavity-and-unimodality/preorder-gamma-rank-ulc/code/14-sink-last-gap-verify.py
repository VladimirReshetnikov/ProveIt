#!/usr/bin/env python3
"""Check package integrity and freshly replay both exact sanity checkers.
The article contains an ordinary proof; finite checks do not replace it.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile, time
ROOT=Path(__file__).resolve().parent

def hashes():
    manifest=ROOT/'SHA256SUMS'
    count=0
    for line in manifest.read_text().splitlines():
        expected,name=line.split('  ',1)
        p=ROOT/name
        if not p.is_file():raise AssertionError('Missing file: '+name)
        actual=hashlib.sha256(p.read_bytes()).hexdigest()
        if actual!=expected:raise AssertionError('Hash mismatch: '+name)
        count+=1
    return count

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=['checks','hashes'],default='checks')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.time()
    report={'integrity_files':hashes(),'mode':args.mode,
            'scope':'Ordinary proof in article; exact finite checks corroborate it.'}
    if args.mode=='checks':
        fresh={}
        with tempfile.TemporaryDirectory(prefix='universal-sink-replay-') as tmp:
            tmp=Path(tmp)
            for label,script,receipt in [('producer','verify_universal_sink.py','universal_sink_verification.json'),('independent','audit.py','receipt.json')]:
                dest=tmp/label;dest.mkdir()
                shutil.copy2(ROOT/'checker'/label/script,dest/script)
                result=subprocess.run([sys.executable,str(dest/script)],cwd=dest,text=True,capture_output=True,timeout=600)
                if result.returncode:
                    raise RuntimeError(label+' failed\n'+result.stdout+'\n'+result.stderr)
                data=json.loads((dest/receipt).read_text())
                assert data['status']=='PASS',data
                fresh[label]=data
                print(label+': fresh exact replay PASS',flush=True)
        report['fresh_receipts']=fresh
    report['status']='PASS';report['elapsed_seconds']=round(time.time()-start,3)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
