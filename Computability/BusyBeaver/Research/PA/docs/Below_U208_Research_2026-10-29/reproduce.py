#!/usr/bin/env python3
"""Offline research replay; no new207 construction is asserted."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,shutil,stat,subprocess,sys,tempfile,time,zipfile
P=Path(__file__).resolve().parent

def need(x,m):
    if not x:raise ValueError(m)
def inventory(root):
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file() and p!=root/'MANIFEST.json' and '__pycache__' not in p.parts}
def verify(root):
    got=inventory(root);need(got==json.loads((root/'MANIFEST.json').read_text()),'Payload integrity mismatch');return got

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--quick',action='store_true',help='Explicitly skip full symbolic projections/runtime and offset-neutral synthesis');ap.add_argument('--receipt',type=Path);ap.add_argument('--integrity-only',action='store_true');a=ap.parse_args()
    before=verify(P)
    if a.integrity_only:print('INTEGRITY_PASS');return
    need(__debug__ and not sys.flags.optimize,'Use normal Python; applicable finite checks also run under -O')
    if a.receipt:need(not a.receipt.resolve().is_relative_to(P),'Receipt must be outside sealed package')
    start=time.monotonic();env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'};env.pop('PYTHONOPTIMIZE',None)
    with tempfile.TemporaryDirectory(prefix='below-u208-') as directory:
        temp=Path(directory)
        with zipfile.ZipFile(P/'reference/U208_ConPA_Conditional_Context_2026-10-29.zip') as z:
            for i in z.infolist():
                n=Path(i.filename);need(not n.is_absolute() and '..' not in n.parts and not stat.S_ISLNK(i.external_attr>>16),'Unsafe reference member')
            z.extractall(temp/'upstream')
        upstream=temp/'upstream/u208_conpa_2026-10-29'
        jobs=[]
        def add(name,script,args=(),opt=False):jobs.append((name,[sys.executable,'-B']+(['-O'] if opt else [])+[str(script),*map(str,args)]))
        for opt in(False,True):
            tag='optimized' if opt else 'normal'
            add('nine-table comparison '+tag,P/'comparison/check.py',opt=opt)
            add('closed source pruning '+tag,P/'source_pruning/check_pruning.py',opt=opt)
            add('bounded layout receipts '+tag,P/'source_pruning/check_receipts.py',opt=opt)
            add('708 neutral identities '+tag,P/'local_search/replay.py',opt=opt)
        add('source-category induction',P/'source_guards/replay.py')
        add('conditional/offset synthesis',P/'synthesis/replay.py',[] if a.quick else ['--full'])
        add('boundary-window projections',P/'boundary/replay.py',[] if a.quick else ['--full'])
        add('inherited primary208 release',upstream/'reproduce.py',['--quick'] if a.quick else [])
        if not a.quick:add('independent alternative208 runtime',P/'code/replay_alternative.py',[upstream])
        def run(job):
            name,cmd=job;q=subprocess.run(cmd,cwd=P,env=env,capture_output=True,text=True)
            need(q.returncode==0,name+'\n'+q.stdout[-12000:]+'\n'+q.stderr[-12000:])
            return {'name':name,'status':'PASS','stdout':q.stdout,'stderr':q.stderr}
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
            results=list(ex.map(run,jobs))
        # Full exact-set manifest controls: changed, missing and extra payloads.
        controls=[]
        for kind in('changed','missing','extra'):
            copy=temp/('negative-'+kind);shutil.copytree(P,copy)
            target=copy/'comparison/records.json'
            if kind=='changed':target.write_bytes(target.read_bytes()+b'\n')
            elif kind=='missing':target.unlink()
            else:(copy/'unexpected.txt').write_text('negative integrity control\n')
            try:verify(copy)
            except ValueError:controls.append(kind)
            else:raise ValueError('Integrity control accepted: '+kind)
            shutil.rmtree(copy)
    need(verify(P)==before,'Sealed payload changed')
    out={'status':'PASS','target':'207 states or fewer','target_achieved':False,'full_replay':not a.quick,'command_stages':len(results),'results':results,'negative_integrity_controls':controls,'sealed_files_unchanged':len(before),'seconds':time.monotonic()-start,'scope':('Quick finite subset; fresh runtime/projection derivations and offset-neutral synthesis skipped.' if a.quick else 'Inherited208 runtime and new research checks; no new smaller machine, no kernel certificate, no state lower bound.')}
    if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
if __name__=='__main__':main()
