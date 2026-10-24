#!/usr/bin/env python3
"""Offline isolated finite replay, not an internal-ZFC or consistency proof."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise RuntimeError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def authenticate(root):
    manifest=json.loads((root/'SHA256SUMS.json').read_text())
    for name,h in manifest.items():
        p=root/name
        need(p.resolve().is_relative_to(root.resolve()),'Unsafe manifest path: '+name)
        need(p.is_file() and digest(p)==h,'Manifest mismatch: '+name)
    return manifest

def extract_inputs(root):
    pins=json.loads((root/'INCOMING_PINS.json').read_text())
    for entry in pins['archives']:
        p=root/'incoming'/entry['file'];raw=p.read_bytes()
        need(len(raw)==entry['bytes'] and digest(p)==entry['sha256'],'Original archive SHA256: '+entry['file'])
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==entry['git_blob'],'Original archive Git blob: '+entry['file'])
        destination=root/'sources'/Path(entry['file']).stem;destination.mkdir(parents=True,exist_ok=True)
        with zipfile.ZipFile(p) as z:
            need(z.testzip() is None,'Original archive CRC: '+entry['file'])
            need(sum(e.file_size for e in z.infolist())<=200_000_000,'Original archive size limit')
            for e in z.infolist():
                name=Path(e.filename)
                need(not name.is_absolute() and '..' not in name.parts and not stat.S_ISLNK(e.external_attr>>16),'Unsafe ZIP member: '+e.filename)
            z.extractall(destination)
    return len(pins['archives'])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only',action='store_true')
    parser.add_argument('--replay-originals',action='store_true',help='Also rerun all fifteen original-archive normal/optimized root phases in further clean copies.')
    args=parser.parse_args()
    need(not sys.flags.optimize,'Run this root driver normally; its command list includes explicit optimized checker phases.')
    manifest=authenticate(ROOT)
    if args.manifest_only:print('PASS',len(manifest),'sealed files');return
    stages=json.loads((ROOT/'REPLAY_COMMANDS.json').read_text())
    rebuild=json.loads((ROOT/'REBUILD_FILES.json').read_text())
    fixed=json.loads((ROOT/'REBUILD_NUMERALS.json').read_text())
    if args.replay_originals:stages=stages+[['baseline/replay_archives.py']]
    records=[]
    with tempfile.TemporaryDirectory(prefix='conzfc-wave11-') as td:
        work=Path(td)/'release'
        shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('sources','__pycache__','*.pyc'))
        original_count=extract_inputs(work)
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONOPTIMIZE',None)
        for stage in stages:
            result=subprocess.run([sys.executable,*stage],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=1800)
            if result.returncode:
                print(result.stdout);raise RuntimeError('Replay failed: '+' '.join(stage))
            records.append({'stage':stage,'status':'PASS','stdout_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()})
            print('PASS '+' '.join(stage),flush=True)
        for name in rebuild:
            need((work/name).read_bytes()==(ROOT/name).read_bytes(),'Nonidentical rebuilt artifact: '+name)
        import gzip
        for name in fixed:
            need(gzip.decompress((work/name).read_bytes())==gzip.decompress((ROOT/name).read_bytes()),'Nonidentical rebuilt numeral: '+name)
    print(json.dumps({'status':'PASS','stages':records,'stage_count':len(records),'sealed_files':len(manifest),'byte_identical_rebuilt_files':len(rebuild),'raw_byte_identical_rebuilt_numerals':len(fixed),'original_archives_authenticated_and_extracted':original_count,'scope':'Exact finite algebra, reconstruction, metrics, payloads, and integrity. Ordinary unbounded proofs and named inherited calibration remain separate. No consistency search, global simplicity minimum, new Lean build or encoded internal-ZFC endpoint.'},indent=2))
if __name__=='__main__':main()
