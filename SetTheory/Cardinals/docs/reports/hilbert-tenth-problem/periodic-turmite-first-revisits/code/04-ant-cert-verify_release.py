#!/usr/bin/env python3
"""Authenticated isolated replay for recovered Report44. Authenticate externally first."""
import argparse,hashlib,json,os,pathlib,shutil,stat,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parent

def need(p,m):
    if not p:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict_object(pairs):
    out={}
    for k,v in pairs:
        need(k not in out,'Duplicate JSON key');out[k]=v
    return out
def load(p):return json.loads(p.read_text(),object_pairs_hook=strict_object,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def snapshot(root):
    out={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsafe nonregular path: '+str(p))
        out[p.relative_to(root).as_posix()]=(sha(p) if stat.S_ISREG(s.st_mode) else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return out

def authenticate(expected):
    need(type(expected)is str and len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'Invalid trusted manifest hash')
    p=ROOT/'MANIFEST.json';need(p.is_file() and not p.is_symlink(),'Missing regular manifest')
    need(sha(p)==expected,'Manifest SHA256 differs from trusted value')
    data=load(p);need(set(data)=={'schema','files'} and data['schema']=='report44-recovered-inventory-v1' and type(data['files'])is dict,'Bad manifest schema')
    actual=snapshot(ROOT);files={n for n,v in actual.items() if v[0] is not None}
    need(files==set(data['files'])|{'MANIFEST.json'},'Missing or unexpected release file')
    dirs={'.'}
    for name,e in data['files'].items():
        q=pathlib.PurePosixPath(name)
        need(not q.is_absolute() and all(x not in ('..','.') for x in q.parts) and q.as_posix()==name,'Unsafe inventory path')
        need(set(e)=={'sha256','bytes','mode'} and type(e['bytes'])is int and type(e['mode'])is int,'Bad inventory entry')
        f=ROOT/name;s=f.stat();need(sha(f)==e['sha256'] and s.st_size==e['bytes'] and stat.S_IMODE(s.st_mode)==e['mode'],'Inventory mismatch: '+name)
        dirs.update(x.as_posix() for x in q.parents)
    need({n for n,v in actual.items() if v[0] is None}==dirs,'Unexpected directory')
    return data

def external_new(raw):
    raw=pathlib.Path(raw);need(not os.path.lexists(raw),'Output already exists')
    parent=raw.parent.resolve(strict=True);out=parent/raw.name
    need(out!=ROOT and ROOT not in out.parents,'Output must be external to release')
    need(not os.path.lexists(out),'Output already exists');return out

def command(script,args=(),optimized=False,local_import=False):
    flags=['-I','-B']+(['-O'] if optimized else [])
    if local_import:
        launch="import sys,runpy;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name='__main__')"
        return [sys.executable,*flags,'-c',launch,str(script.parent),str(script),*map(str,args)]
    return [sys.executable,*flags,str(script),*map(str,args)]

def run(cmd,cwd,log,guard=False):
    env=dict(os.environ);env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',LC_ALL='C.UTF-8')
    p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=600)
    log.with_suffix('.stdout').write_text(p.stdout);log.with_suffix('.stderr').write_text(p.stderr)
    if guard:
        need(p.returncode!=0 and 'Optimized Python' in p.stderr and not p.stdout,'Missing early optimized-mode guard')
        return {'status':'guarded rejection before scientific work','returncode':p.returncode}
    need(p.returncode==0,'Replay failed: '+str(log)+'\n'+p.stderr[-2000:]);return p.stdout

def replay(target):
    target.mkdir();work=target/'certificate';shutil.copytree(ROOT/'certificate',work);before=snapshot(work)
    records={}
    records['complete']=json.loads(run(command(work/'verify_packet.py'),target,target/'complete'))
    need(records['complete']['status']=='PASS_FRESH_RECOVERED_PACKET_REPLAY','Complete replay status')
    records['boundaries']=json.loads(run(command(work/'check_output_boundaries.py'),target,target/'boundaries'))
    need(records['boundaries']==load(ROOT/'certificate/output-boundary-receipt.json'),'Boundary replay differs')
    records['guards']={}
    for name in ['merged_source.py','verify_packet.py','check_output_boundaries.py']:
        records['guards'][name]=run(command(work/name,optimized=True),target,target/('guard-'+name),guard=True)
    need(snapshot(work)==before,'Complete replay mutated isolated certificate')
    records['history']={}
    for optimized in [False,True]:
        mode='optimized' if optimized else 'normal';h=target/('history-'+mode);shutil.copytree(ROOT/'certificate/history',h)
        old=snapshot(h)
        run(command(h/'reconstruct_history.py',optimized=optimized),target,target/('history-construction-'+mode))
        out=json.loads(run(command(h/'audit_history.py',optimized=optimized,local_import=True),target,target/('history-audit-'+mode)))
        need(out==load(ROOT/'certificate/history/audit_receipt.json'),'History audit differs: '+mode)
        for rel in ['history174.json','verification.json','audit_receipt.json']:
            need((h/rel).read_bytes()==(ROOT/'certificate/history'/rel).read_bytes(),'History generated bytes differ: '+mode+'/'+rel)
        new=snapshot(h);need(set(new)==set(old),'Unexpected history replay file')
        for name,value in old.items():
            need(value[:2]==new[name][:2],'History bytes/modes changed: '+name)
            if name not in ['history174.json','verification.json','audit_receipt.json']:need(value==new[name],'Unexpected history timestamp mutation')
        records['history'][mode]={'exact_reference_bytes':True,'bounded_histories':out['bounded_histories_verified'],'mutations_rejected':len(out['mutation_rejections'])}
    return {'status':'PASS','authenticated_isolated_replay':True,'upstream_code_or_schedule_execution':False,'records':records}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--verify-only',action='store_true');p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    data=authenticate(a.manifest_sha256);before=snapshot(ROOT)
    if a.verify_only:
        need(a.output is None,'--verify-only takes no output');r={'status':'PASS','authenticated_inventory':True,'files':len(data['files'])}
    else:
        need(a.output is not None,'Supply a fresh external --output directory');target=external_new(a.output);r=replay(target)
    need(snapshot(ROOT)==before,'Release bytes/modes/mtimes changed');r['release_bytes_modes_mtimes_preserved']=True
    if a.output:(target/'replay_receipt.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))
if __name__=='__main__':main()
