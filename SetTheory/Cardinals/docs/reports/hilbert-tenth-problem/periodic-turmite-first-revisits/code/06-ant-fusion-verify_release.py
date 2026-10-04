#!/usr/bin/env python3
"""Authenticate Report48 and replay in a new external directory without mutating it.
Authenticate this script by an external trusted release before execution.
"""
import argparse,hashlib,json,os,pathlib,shutil,stat,subprocess,sys,zipfile
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
    data=load(p);need(set(data)=={'schema','files'} and data['schema']=='report48-inventory-v1' and type(data['files'])is dict,'Bad manifest schema')
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

def command(script,args=(),local_import=False):
    flags=['-I','-B']
    if local_import:
        launch="import sys,runpy;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name='__main__')"
        return [sys.executable,*flags,'-c',launch,str(script.parent),str(script),*map(str,args)]
    return [sys.executable,*flags,str(script),*map(str,args)]

def run(cmd,cwd,log):
    env=dict(os.environ);env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',LC_ALL='C.UTF-8')
    p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=1800)
    log.with_suffix('.stdout').write_text(p.stdout);log.with_suffix('.stderr').write_text(p.stderr)
    need(p.returncode==0,'Replay failed: '+str(log)+'\n'+p.stderr[-3000:]);return p.stdout

def baseline(out,provenance):
    archive=ROOT/'references/Research_Report47_reproducibility.zip'
    need(sha(archive)==provenance['report47_archive_sha256'],'Report47 archive identity failed')
    with zipfile.ZipFile(archive) as z:
        names=set()
        for info in z.infolist():
            p=pathlib.PurePosixPath(info.filename)
            need(not p.is_absolute() and len(p.parts)>1 and p.parts[0]=='Research_Report47' and all(v not in ('.','..') for v in p.parts),'Unsafe archive member')
            need(info.filename not in names and not info.is_dir(),'Duplicate or directory archive member');names.add(info.filename)
            mode=info.external_attr>>16
            need(stat.S_ISREG(mode),'Nonregular archive member')
            target=out/p.as_posix();target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as f:f.write(z.read(info))
            target.chmod(stat.S_IMODE(mode))
    base=out/'Research_Report47'
    # Validate every baseline member against the authenticated prior inventory.
    need(sha(base/'MANIFEST.json')==provenance['report47_manifest_sha256'],'Baseline manifest failed')
    data=load(base/'MANIFEST.json')
    need(data['schema']=='report47-inventory-v1','Unexpected baseline schema')
    need({p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}==set(data['files'])|{'MANIFEST.json'},'Baseline inventory differs')
    for name,e in data['files'].items():
        p=base/name;s=p.stat()
        need(sha(p)==e['sha256'] and s.st_size==e['bytes'] and stat.S_IMODE(s.st_mode)==e['mode'],'Baseline file differs: '+name)
    return base

def replay(target,independent=True):
    need(__debug__,'Optimized Python is not allowed for scientific replay')
    target.mkdir();work=target/'science';shutil.copytree(ROOT/'science',work)
    before=snapshot(work);records={}
    fresh=target/'fresh-fused.json'
    run(command(work/'fusion_source.py',['--out',fresh]),target,target/'fused')
    records['fused']=load(fresh)
    need(records['fused']==load(ROOT/'science/fused-receipt.json'),'Fused receipt differs')
    fresh=target/'fresh-checks.json'
    run(command(work/'checks.py',['--out',fresh],local_import=True),target,target/'checks')
    records['checks']=load(fresh)
    need(records['checks']==load(ROOT/'science/checks-receipt.json'),'Supplementary checks differ')
    if independent:
        base=baseline(target,load(ROOT/'verification/provenance.json'))
        # The separately pinned adapter authenticates unchanged independent checker bytes.
        args=['--candidate-dir',work,'--audit-dir',ROOT/'independent_audit','--report47-dir',base,'--out-dir',target/'independent-replay']
        run(command(ROOT/'audit_replay/replay_independent_audit.py',args),target,target/'independent')
        records['independent_adapter']=load(target/'independent-replay/replay-receipt.json')
        need(records['independent_adapter']['status']=='PASS_RELOCATED_FROZEN_INDEPENDENT_AUDITS','Independent relocation failed')
    need(snapshot(work)==before,'Scientific source copy changed during replay')
    return {'status':'PASS','author_receipts_equal':True,'independent_requested':independent,'records':records,'upstream_physical_recipe_or_saved_schedule_execution':False,'owned_arithmetic_generators_only':True}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--verify-only',action='store_true');p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    data=authenticate(a.manifest_sha256);before=snapshot(ROOT)
    if a.verify_only:
        need(a.output is None,'--verify-only takes no output');r={'status':'PASS','authenticated_inventory':True,'files':len(data['files'])}
    else:
        need(a.output is not None,'Supply a new external --output directory');target=external_new(a.output);r=replay(target)
    need(snapshot(ROOT)==before,'Release bytes/modes/mtimes changed');r['release_bytes_modes_mtimes_preserved']=True
    if a.output:(target/'replay_receipt.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))
if __name__=='__main__':main()
