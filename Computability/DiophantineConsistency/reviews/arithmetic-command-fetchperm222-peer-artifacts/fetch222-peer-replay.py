#!/usr/bin/env python3
"""Private two-leaf independent replay from a frozen successful author inventory."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
TARGETS=['ArithmeticCommandFetchPerm222','ArithmeticCommandFetchPerm222Checks']

def require(b,m):
    if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return {'path':str(p),'sha256':sha(p)}
def check(r):require(sha(r['path'])==r['sha256'],'changed pin '+r['path'])
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

require(len(sys.argv)==2,'supply final author directory')
author=Path(sys.argv[1]);inp=author/'inputs.json';run=author/'run.json'
i=json.loads(inp.read_text());a=json.loads(run.read_text())
require(a['status']=='PASS','author not terminal PASS')
require(sha(inp)==a['inputs_sha256'],'author input receipt pin')
require(len(i['modules'])==102,'expected cached closure size')
require(len(i['external'])==37,'expected explicit external boundary')
require(sha(i['compiler'])==i['compiler_sha256'],'compiler pin')
require([r['module'] for r in a['records']]==['DiophantineConsistency.'+t for t in TARGETS],'author target list')
pins=list(i['pins'])+[rec(inp),rec(run),rec(__file__)]
for e in i['modules']:
    pins.append({'path':e['source'],'sha256':e['source_sha256']})
    pins.extend(e['objects'])
for e in i['external']:pins.append(e['object'])
for e in a['records']:
    require(e['exit_code']==0,'author leaf failed')
    pins.extend([e['source'],e['object'],e['log']])
# Duplicated provenance records are harmless, but hash one unique pair once.
pins=list({(r['path'],r['sha256']):r for r in pins}.values())
for r in pins:check(r)
require(shutil.disk_usage(ROOT).free>=512*1024**2,'disk reserve')
private=Path(tempfile.mkdtemp(prefix='fetch222-independent-peer-'))
lib=private/'lib';lib.mkdir()
for e in i['modules']:
    require(e['module'] not in ['DiophantineConsistency.'+t for t in TARGETS],'fresh leaf already cached')
    for o in e['objects']:
        dest=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name
        dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(o['path'])
roots=i['lean_path'].split(':')[1:]
require(all('/.lake/build/lib/lean' not in p or '/.lake/packages/' in p for p in roots),'unexpected project cache root')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*roots]);env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','scope':'102 exact-source authenticated cached modules; two fresh leaves; 37 explicit package boundary imports',
   'parent_inputs':rec(inp),'parent_run':rec(run),'pins':pins,'cached_modules':i['modules'],'external':i['external'],
   'compiler':rec(i['compiler']),'driver':rec(__file__),'lean_path':env['LEAN_PATH'],'records':[]}
save(private/'replay.json',s);Path('/tmp/fetch222-independent-peer-location.txt').write_text(str(private))
for name,parent in zip(TARGETS,a['records']):
    for r in pins:check(r)
    require(shutil.disk_usage(ROOT).free>=512*1024**2,'disk reserve')
    src=Path(parent['source']['path']);out=lib/'DiophantineConsistency'/(name+'.olean')
    out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists(),'fresh target output exists')
    snap=private/(name+'.lean');shutil.copyfile(src,snap);log=private/(name+'.log')
    cmd=[i['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
    start=time.monotonic()
    with log.open('w') as f:
        code=subprocess.run(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
    r={'module':parent['module'],'source':rec(src),'snapshot':rec(snap),'command':cmd,'exit_code':code,
       'seconds':time.monotonic()-start,'log':rec(log),'object':rec(out) if code==0 else None}
    s['records'].append(r);save(private/'replay.json',s);print(json.dumps(r),flush=True)
    if code:
        s['status']='FAILED';save(private/'replay.json',s);raise SystemExit(code)
    reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
    for title,ax in reports:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'unexpected axiom '+title)
    r['axiom_reports']=reports;r['byte_identical_to_author']=r['object']['sha256']==parent['object']['sha256']
    require(r['byte_identical_to_author'],'fresh object differs from author')
    for p in pins:check(p)
require(len(s['records'][0]['axiom_reports'])==0,'unexpected main report count')
require(len(s['records'][1]['axiom_reports'])==8,'focused audit count')
s['status']='PASS';save(private/'replay.json',s);print('PASS '+str(private),flush=True)
