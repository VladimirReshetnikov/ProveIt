#!/usr/bin/env python3
"""Guarded union and bounded Lean check of the 94-graph model bridge."""
from pathlib import Path
from hashlib import sha256
import json, os, shutil, subprocess, tempfile, time
H=Path(__file__).resolve().parent; D=H.parents[1]; B=D/'research/ordinary12-ipra-bridge'
C=D/'research/ordinary12-sum-of-squares-candidate'; P=B/'compact44-byte-ports-model-iff-prototype'
BASE=P/'observations/prepare-attempt01/manifest.json'; BR=P/'observations/attempt03/terminal.json'; SR=C/'observations/attempt03/terminal.json'
LEAN='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'; PACKAGE='/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
OBS=H/'observations'/os.environ.get('ATTEMPT','attempt01')
SFX=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
def rec(p):
    p=Path(p)
    if not os.path.lexists(p):return None
    need(p.is_file(),'dangling '+str(p))
    return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def checkrecords(r):
    return all(rec(p)==v for p,v in r.items())
def selected(m):
    lib=Path(m['project'])/'lib'; actual={p.relative_to(lib).as_posix():rec(p) for p in lib.rglob('*') if p.is_file()}
    return set(actual)==set(m['files']) and all(actual[k]['sha256']==m['files'][k]['sha256'] and actual[k]['resolved']==m['files'][k]['resolved'] for k in actual)
def valid_prior():
    need(sha(BASE)=='d45af4289b21b8d4f18a4eab385d8a39bfe6d4d2690a59fe7cc1c5f83f818abe','base manifest pin')
    m=json.loads(BASE.read_text()); byte=json.loads(BR.read_text()); sq=json.loads(SR.read_text())
    need(m['unchanged'] and selected(m) and not m['suppressed_companions'],'selected base union')
    for key in ('model_before','model_guards','byte_guards'):need(checkrecords(m[key]),'base guard drift '+key)
    need(byte['exit_code']==0 and byte['guards_unchanged'] and byte['selected_unchanged'] and byte['providers_unchanged'],'byte result')
    need(sq['exit_code']==0 and sq['guards_unchanged'] and sq['provider_unchanged'],'square result')
    need(checkrecords(byte['guards_before']) and checkrecords(sq['guards_before']) and checkrecords(sq['provider_before']),'producer guard drift')
    for key in ('byte','model'):
        rp=Path(m[key+'_receipt_path']);need(sha(rp)==m[key+'_receipt_sha256'],'base producer receipt '+key)
        r=json.loads(rp.read_text()); op=Path(r['command'][-1]);need(r['exit_code']==0 and sha(op)==r['object_sha256'],'base producer object '+key)
    bm=Path(m['byte_manifest_path']);need(sha(bm)==m['byte_manifest_sha256'],'byte manifest drift')
    bm=json.loads(bm.read_text());need(checkrecords(bm['guards_before']),'byte manifest guards')
    for item in bm['prior_manifests'].values():
        need(sha(item['path'])==item['sha256'] and checkrecords(item['providers_before']),'prior provider drift')
    bobj=Path(byte['command'][-1]);sobj=Path(sq['command'][-1])
    need(sha(bobj)==byte['object_sha256']=='6feb5a290fa5d15e5f9b539fcd3a5ce7e233e3783cc0115ed6dde63b42515e6a','byte object')
    need(sha(sobj)==sq['object_sha256']=='86cfbe3b171f01602e88b6687a74e8946b5d4c8f53b3b24848e9c2272cd2e1d0','square object')
    need(sha(C/'FreeJSumSquares.lean')==sq['source_sha256']=='77f22764b45732e2f7b837bf98caf40e6563c232f48ba682c421889b396b7794','square source')
    roots=[Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib'),Path('/tmp/ipra-freej-power-finish-pair-01/author/lib')]
    inventory={str(p):rec(p) for root in roots for p in root.rglob('*') if p.is_file()}
    need(inventory==sq['provider_before'],'square provider inventory')
    overlap=0
    for path,record in inventory.items():
        for root in roots:
            try:name=Path(path).relative_to(root).as_posix()
            except ValueError:continue
            need(name in m['files'] and record['sha256']==m['files'][name]['sha256'],'provider overlap '+name)
            overlap+=1;break
    need(overlap==167,'unexpected overlap count')
    # Both direct imports of the 94 theorem have to resolve to identical bytes.
    need(m['files']['FreeJCompletenessFactorBridge.olean']['sha256']==sha('/tmp/free-j-completeness-factor-author-q9rapr3k/FreeJCompletenessFactorBridge.olean'),'factor bridge mismatch')
    need(m['files']['DiophantineConsistency/ModelDifferenceRing.olean']['sha256']==sha('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib/DiophantineConsistency/ModelDifferenceRing.olean'),'difference ring mismatch')
    return m,byte,sq,bobj,sobj,overlap
need(not OBS.exists(),'refusing to overwrite observation')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'less than 4 GiB free')
m,byte,sq,bobj,sobj,overlap=valid_prior();OBS.mkdir(parents=True)
run=Path(tempfile.mkdtemp(prefix='free-j-square-model-iff-'));lib=run/'lib';lib.mkdir()
for name,v in m['files'].items():
    dest=lib/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(v['resolved'])
for name,obj in [('CompactBytePortsModelIff',bobj),('FreeJSumSquares',sobj)]:
    dest=lib/(name+'.olean');need(not dest.exists(),'duplicate producer '+name);dest.symlink_to(obj.resolve(strict=True))
union={p.relative_to(lib).as_posix():rec(p) for p in lib.rglob('*') if p.is_file()}
need(len(union)==1288,'union size')
source=H/'SumSquaresModelIff.lean';copy=run/source.name;shutil.copyfile(source,copy);shutil.copyfile(source,OBS/'source.lean');sourcehash=sha(source)
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{lib}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
deps=subprocess.run([LEAN,'--deps',str(copy)],env=env,capture_output=True,text=True,timeout=120)
(OBS/'deps').write_text(deps.stdout);(OBS/'deps.stderr').write_text(deps.stderr)
need(deps.returncode==0 and not deps.stderr,'deps failed')
guards={}
for line in deps.stdout.splitlines():
    p=Path(line);need(p.is_absolute() and p.is_file() and p.suffix=='.olean','bad dep '+line)
    stem=str(p)[:-len('.olean')]
    for suffix in SFX:guards[stem+suffix]=rec(stem+suffix)
cmd=[LEAN,'-M3000','-j1','-DElab.async=false',f'--root={run}',str(copy),'-o',str(run/'SumSquaresModelIff.olean')]
t0=time.monotonic()
try:
    proc=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=180);code=proc.returncode;output=proc.stdout+proc.stderr
except subprocess.TimeoutExpired as e:
    code=None;output=str(e.stdout or '')+str(e.stderr or '')
(OBS/'compile.log').write_text(output)
obj=run/'SumSquaresModelIff.olean'; valid_prior()
after={p.relative_to(lib).as_posix():rec(p) for p in lib.rglob('*') if p.is_file()}
result={'command':cmd,'exit_code':code,'elapsed_seconds':round(time.monotonic()-t0,3),
 'source_sha256':sourcehash,'workspace_source_sha256_after':sha(source),'log_sha256':sha(OBS/'compile.log'),
 'object_sha256':sha(obj) if obj.is_file() else None,'base_manifest_sha256':sha(BASE),
 'base_receipt_sha256':sha(BR),'square_receipt_sha256':sha(SR), 'prior_overlap_count':overlap,
 'union':union,'union_unchanged':union==after,'direct_guards':guards,'guards_unchanged':checkrecords(guards),
 'scope':'model-level Lean bridge; external file/PDF bindings and iPRA derivation remain open'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit_code','elapsed_seconds','object_sha256','prior_overlap_count','union_unchanged','guards_unchanged')},sort_keys=True))
need(code==0 and obj.is_file() and union==after and checkrecords(guards) and sha(source)==sourcehash and not any(w in output for w in ('error:','warning:','sorryAx')),'compile did not pass')
