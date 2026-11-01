#!/usr/bin/env python3
"""Two focused Lean replays with direct input/companion guards; ancestry is inherited."""
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
SRC = ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PARENT = Path('/tmp/ipra-aq31-final-peer-2y9kq11h')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq31-native-final-replay/receipt.json'
PARENT_OBS = PARENT_RECEIPT.parent/'terminal-observation.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq30-model-replay'
modules = ['AdaptiveAQ30Literal', 'AdaptiveAQ30Zeros', 'AdaptiveAQ31Zeros', 'AdaptiveAQ30Facts', 'AdaptiveAQ30Positive', 'AdaptiveAQ30Maps', 'AdaptiveAQ30Transport', 'AdaptiveAQ30', 'AdaptiveAQ30Checks']
source_pins = {'AdaptiveAQ30Literal': 'd00d15854c5c8a72a6e39571c5fcfb894db50e99c11c123a7599d5677ad19cc5', 'AdaptiveAQ30Zeros': '5a083f559d05bf695057f905ac7f4743b2a435529b657ff2409d37d6adadfbd3', 'AdaptiveAQ31Zeros': '31a4041a45629e68ed01809b07f778c58d0db0b5519ed4ed591f69b522fec01f', 'AdaptiveAQ30Facts': '0906989a2226292e0864481c7babaf6559c0b3284da444c45fa130fb563b3105', 'AdaptiveAQ30Positive': '66fad1406bb238efd4eae5273fb5eda9c82e1c881a4c1f5d279061a18f7d0dd0', 'AdaptiveAQ30Maps': '3d85aa2f778d2f4224f0bbcb8150c871cd469f493a7d4b85dfb5013b5f8dff05', 'AdaptiveAQ30Transport': 'a5d6bd7d3261b68be0ca5749e9aab666d47e035d33679df5d987bec25dcca64b', 'AdaptiveAQ30': '1c32ceafe73cfe412d1700b012abee6a994014b943cbe395bb2b338d91d9f7c5', 'AdaptiveAQ30Checks': '3637464a99b3db4f3108908c80a393786a0d13956af592c3e6589eaea8e5f0f0'}
suffixes = ('.olean','.olean.private','.olean.server','.ir','.ilean',
            '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')

def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def scan(stem):
    d = {}
    for suffix in suffixes:
        p = Path(str(stem)+suffix)
        if os.path.lexists(p):
            require(p.is_file(), ('bad input companion',str(p)))
            d[str(p)] = {'realpath':str(p.resolve()), 'sha256':digest(p)}
        else:
            d[str(p)] = None
    return d

def check_guard(guard):
    for path,record in guard.items():
        p=Path(path)
        if record is None:
            require(not os.path.lexists(p), ('new companion',path))
        else:
            require(p.is_file() and str(p.resolve())==record['realpath'] and digest(p)==record['sha256'], ('changed dependency',path))

require(not OUT.exists(), 'refusing to overwrite prior replay')
OUT.mkdir(parents=True)
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'parent_observation':digest(PARENT_OBS), 'candidate':digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums30-degree8/candidate.json'), 'literal_verifier':digest(D/'verify_literal.py'),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
require(base['sources']==source_pins and base['literal_verifier']=='95764160563a5d642c20bc47bba085aade2136441d0f751fe97357a55996efe7', 'source or verifier identity')
require(base['candidate']=='f6c88de69011dc070c3cb642cf12bc27bb20c6ee92eaabb56dc1ccd884f685ad', 'candidate identity')
check=subprocess.run(['python3',str(D/'verify_literal.py')],capture_output=True,text=True); require(check.returncode==0 and check.stdout.strip()=='PASS: 30 variables, four ports and all 138 Lean literal gates match the pinned graph', ('literal verification',check.stdout,check.stderr))
require(base['parent_state']=='7f3c891f4a0e80d0226ea533cd4daad7317d846a9090dc126eaa28a14d4bfc3f', 'parent receipt identity')
require(base['parent_observation']=='453bc4214b8f63dba8fd8164f2c97d4387e1bd9f48e77d4a29935ec152dc0cda', 'parent observation identity')
parent_obs=json.loads(PARENT_OBS.read_text())
require(parent_obs['tool_session']==21337 and parent_obs['observed_exit_code']==0 and parent_obs['observed_stdout']=='MATCHED_PASS 23 rows' and parent_obs['receipt_sha256']==base['parent_state'], 'parent observed exit')
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(parent_receipt['status']=='MATCHED_PASS' and len(parent_receipt['runs'])==2 and parent_receipt['runs'][0]['rows']==parent_receipt['runs'][1]['rows'] and len(parent_receipt['runs'][1]['rows'])==23 and parent_receipt['runs'][1]['run']==str(PARENT), 'parent receipt')
parent_fixed={}
for row in parent_receipt['runs'][1]['rows']:
    n=row['module']
    for path,h in ((PARENT/'lib'/'DiophantineConsistency'/(n+'.olean'),row['object_sha256']), (PARENT_RECEIPT.parent/'peer/src/DiophantineConsistency'/(n+'.lean'),row['source_sha256']), (PARENT_RECEIPT.parent/'peer/logs'/(n+'.log'),row['log_sha256'])):
        require(digest(path)==h, ('parent row',n,str(path)));parent_fixed[str(path)]=h
fallback={}
for n in modules:
    for name,record in scan(PKG/'DiophantineConsistency'/n).items():
        require(record is None, ('unexpected target fallback',name));fallback[name]=record
records=[]
try:
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-aq30-'+label+'-'))
        lib=run/'lib';lib.mkdir()
        subprocess.run(['cp','-as',str(PARENT/'lib')+'/.',str(lib)+'/'],check=True)
        snap=OUT/label/'src'/'DiophantineConsistency';snap.mkdir(parents=True)
        logs=OUT/label/'logs';logs.mkdir()
        for name in modules:
            shutil.copyfile(SRC/(name+'.lean'),snap/(name+'.lean'))
            require(digest(snap/(name+'.lean'))==base['sources'][name], 'source snapshot')
        env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1')
        env.pop('LEAN_SRC_PATH',None)
        guards={};rows=[]
        for name in modules:
            source=snap/(name+'.lean')
            deps=subprocess.run([str(LEAN),'--deps',str(source)],env=env,capture_output=True,text=True)
            require(deps.returncode==0 and not deps.stderr, ('deps failed',name,deps.stderr))
            depinfo={}
            for line in deps.stdout.splitlines():
                path=Path(line)
                require(path.is_absolute() and path.is_file() and str(path).endswith('.olean'), ('bad dependency',name,line))
                require(any(path.is_relative_to(r) for r in (lib,PKG,TOOL)), ('unapproved dependency root',name,line))
                stem=Path(str(path)[:-len('.olean')]);companions=scan(stem)
                for key,value in companions.items():
                    require(key not in guards or guards[key]==value, ('changed direct input',key))
                    guards[key]=value
                depinfo[str(path.relative_to(lib)) if path.is_relative_to(lib) else str(path)] = digest(path)
            check_guard(guards)
            obj=lib/'DiophantineConsistency'/(name+'.olean')
            require(not os.path.lexists(obj), ('output already exists',name))
            cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(snap.parent),str(source),'-o',str(obj)]
            log=logs/(name+'.log')
            with log.open('x') as out:
                proc=subprocess.run(cmd,env=env,stdout=out,stderr=subprocess.STDOUT)
            output=log.read_text()
            require(proc.returncode==0 and obj.is_file(), ('lean failure',name,proc.returncode,output))
            require('error:' not in output and 'sorryAx' not in output and 'warning:' not in output, ('bad log',name,output))
            reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output,re.M|re.S)
            expected={'AdaptiveAQ30Literal':0,'AdaptiveAQ30Zeros':1,'AdaptiveAQ31Zeros':1,'AdaptiveAQ30Facts':1,'AdaptiveAQ30Positive':1,'AdaptiveAQ30Maps':2,'AdaptiveAQ30Transport':4,'AdaptiveAQ30':2,'AdaptiveAQ30Checks':12}[name]
            require(len(reports)==expected, ('unexpected axiom report count',name,len(reports),expected))
            for report in reports:
                require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('unexpected axiom',name,report))
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(PARENT_OBS)==base['parent_observation'] and digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums30-degree8/candidate.json')==base['candidate'] and digest(D/'verify_literal.py')==base['literal_verifier'], 'fixed input changed')
        require(all(digest(SRC/(name+'.lean'))==base['sources'][name] for name in modules),'workspace source drift')
        require(all(digest(path)==h for path,h in parent_fixed.items()), 'parent row drift')
        check_guard(fallback)
        check_guard(guards)
        records.append({'label':label,'run':str(run),'rows':rows,'guarded_companion_paths':len(guards),'guards':guards})
    for a,b in zip(records[0]['rows'],records[1]['rows']):
        require(a==b, ('replay mismatch',a,b))
    report={'status':'MATCHED_PASS','base':base,'parent_fixed':parent_fixed,'fallback':fallback,'runs':records,
            'scope':'Two focused same-provider source/object/log and direct dependency companion replays; transitive project ancestry, package transitive ancestry and dynamic imports are inherited. These point-in-time source checks are not a full current-source closure.'}
    (OUT/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('MATCHED_PASS',len(modules),'rows',flush=True)
except BaseException as e:
    (OUT/'failure.txt').write_text(repr(e)+'\n')
    raise
