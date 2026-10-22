#!/usr/bin/env python3
"""Fresh baseline/candidate source-closure checks; not a whole machine build."""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, shutil, subprocess, time

HERE=Path(__file__).resolve().parent
PIN='57541fe0cfe3af62b4cb58747d8d1d7c16b338d5'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args(); repo=args.repo.resolve();lean=args.lean.resolve();dest=args.out.resolve()
    assert not dest.exists(),'Use a new output directory'
    head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    assert head==PIN,(head,PIN)
    version=subprocess.check_output([str(lean),'--version'],text=True).strip()
    assert 'version 4.32.0,' in version,version
    roots={'BusyBeaver':repo/'Computability/BusyBeaver/Lean','FirstOrder':repo/'Logic/FirstOrder/Lean'}
    dest.mkdir(parents=True);record={'source_commit':head,'lean_version':version,'lean_sha256':sha(lean),'scope':'Fresh focused logic closures and typed clients; not the full K215 endpoint.','runs':{},'status':'RUNNING'}
    def save(): (dest/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    for variant in ['baseline','candidate']:
        work=dest/variant;work.mkdir();(work/'logs').mkdir()
        modules={};order=[]
        def visit(n):
            if n in modules:return
            rel=Path(n.replace('.','/')+'.lean')
            candidate=HERE/rel
            if n in ['BasisPublicAudit','DownstreamPublicAudit']:
                data=candidate.read_bytes()
                if variant=='baseline':data=data.replace(b'import BusyBeaver.ZFC.ImplicationalBasis',b'import BusyBeaver.ZFC.Lukasiewicz')
                origin='packet/'+str(rel)
            elif variant=='candidate' and candidate.is_file():
                data=candidate.read_bytes();origin='packet/'+str(rel)
            else:
                src=roots[n.split('.')[0]]/rel;data=src.read_bytes()
                origin=str(src.relative_to(repo))
                assert data==subprocess.check_output(['git','-C',str(repo),'show',head+':'+origin]),origin
            imports=[]
            for line in data.decode().splitlines():
                if line.startswith('import '):
                    imports.extend(x for x in line[7:].split() if x.split('.')[0] in roots)
            modules[n]={'source':origin,'data':data,'imports':imports,'rel':rel}
            for dep in imports:visit(dep)
            order.append(n)
        targets=['BusyBeaver.ZFC.DominatedImplication','BusyBeaver.ZFC.Lukasiewicz','BusyBeaver.ZFC.KCodeDom','BasisPublicAudit','DownstreamPublicAudit']
        if variant=='candidate':targets.insert(1,'BusyBeaver.ZFC.ImplicationalBasis')
        for n in targets:visit(n)
        run={'targets':targets,'project_modules':len(order)-2,'total_compilations':len(order),'order':order,'records':[],'status':'RUNNING'}
        record['runs'][variant]=run;save()
        env=dict(os.environ,LEAN_PATH=str(work));env.pop('LEAN_SYSROOT',None)
        for i,n in enumerate(order):
            m=modules[n];src=work/m['rel'];src.parent.mkdir(parents=True,exist_ok=True);src.write_bytes(m['data'])
            log=work/'logs'/(n+'.log');out=src.with_suffix('.olean')
            command=[str(lean),'-t','1000000','-o',str(out.relative_to(work)),str(m['rel'])]
            inputs={d:sha(work/Path(d.replace('.','/')+'.olean')) for d in m['imports']}
            with Path('/tmp/proveit-k215-proof-build.lock').open('a') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic()
                with log.open('w') as f:proc=subprocess.run(command,cwd=work,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=600)
                seconds=time.monotonic()-start
            stdout=log.read_text()
            item={'module':n,'source_origin':m['source'],'source_sha256':sha(src),'direct_import_objects':inputs,'seconds':seconds,'exit_code':proc.returncode,'log':str(log.relative_to(dest)),'log_sha256':sha(log)}
            if out.exists():item['object_sha256']=sha(out)
            item['sorry_warning']='declaration uses \'sorry\'' in stdout
            run['records'].append(item);save();print(variant,n,proc.returncode,round(seconds,3),flush=True)
            if proc.returncode or item['sorry_warning']:
                run['status']='FAIL';record['status']='FAIL';save();print(stdout);raise SystemExit(1)
        run['status']='PASS';save()
    record['status']='PASS';save();print('PASS: fresh focused baseline and candidate checks',flush=True)

if __name__=='__main__':main()
