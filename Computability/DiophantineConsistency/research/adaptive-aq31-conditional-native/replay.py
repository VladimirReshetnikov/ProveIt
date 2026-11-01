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
PARENT = Path('/tmp/ipra-aq32-native-peer-lsc99cro')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq32-native-replay/receipt.json'
MODEL_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq31-oriented-replay/receipt.json'
MODEL_OBS = MODEL_RECEIPT.parent/'terminal-observation.json'
PARENT_OBS = PARENT_RECEIPT.parent/'terminal-observation.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq31-conditional-native-replay'
modules = ['AdaptiveAQ31Context', 'AdaptiveAQ31Literal', 'AdaptiveAQ31Maps', 'AdaptiveAQ31Transport', 'AdaptiveAQ31', 'AdaptiveAQ31ConditionalNoZero', 'IPRAAQ31ConditionalBridge']
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
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'parent_observation':digest(PARENT_OBS), 'model_receipt':digest(MODEL_RECEIPT), 'model_observation':digest(MODEL_OBS), 'candidate':digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums31-degree6/candidate.json'), 'literal_verifier':digest(D.parent/'adaptive-aq31-proof/verify_literal.py'),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
require(base['candidate']=='a90ab59a3ab1b3e9b04c2b962ea79c666a3c2dc90e6941c73f5180ab73c5ee67', 'candidate identity')
check=subprocess.run(['python3',str(D.parent/'adaptive-aq31-proof/verify_literal.py')],capture_output=True,text=True); require(check.returncode==0 and check.stdout.strip()=='PASS: 31 variables, four ports and all 141 Lean literal gates match the pinned graph', ('literal verification',check.stdout,check.stderr))
require(base['parent_state']=='d5e55c1b0e876244f08f7cb7fcfc7f6e4932e07f42dc545ca31836a3b075dbc8', 'parent receipt identity')
require(base['parent_observation']=='2c460c1caaa855a059922e17a62a5f916665e66186f1fdf194ef4fe30f670c70', 'parent observation identity')
parent_obs=json.loads(PARENT_OBS.read_text())
require(parent_obs['tool_session']==23581 and parent_obs['observed_exit_code']==0 and parent_obs['observed_stdout']=='MATCHED_PASS 12 rows', 'parent observed exit')
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(parent_receipt['status']=='MATCHED_PASS' and parent_receipt['runs'][1]['run']==str(PARENT), 'parent receipt')
for row in parent_receipt['runs'][1]['rows']:
    require(digest(PARENT/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('parent object',row['module']))
require(base['model_receipt']=='bc4e25c2ee5a80554e72b6afe37a0d6ad9857993170d41ada8b3dc1be46d7669', 'model receipt identity')
require(base['model_observation']=='6de32dab537d9a823aba382cf0f08ec15b64e0f3fdeb912401bee598e3723fd9', 'model observation identity')
model_obs=json.loads(MODEL_OBS.read_text())
require(model_obs['tool_session']==28270 and model_obs['observed_exit_code']==0 and model_obs['observed_stdout']=='MATCHED_PASS 5 rows', 'model observed exit')
model=json.loads(MODEL_RECEIPT.read_text())
require(model['status']=='MATCHED_PASS' and len(model['runs'][1]['rows'])==5, 'model receipt')
modelpeer=Path(model['runs'][1]['run'])
for row in model['runs'][1]['rows']:
    require(digest(SRC/(row['module']+'.lean'))==row['source_sha256'], ('model source mismatch',row['module']))
    require(digest(modelpeer/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('model object mismatch',row['module']))
    require(digest(MODEL_RECEIPT.parent/'peer/logs'/(row['module']+'.log'))==row['log_sha256'], ('model log mismatch',row['module']))
old=model['runs'][1]['guards']
parent_key=next(k for k in old if k.endswith('/AdaptiveAQ32.olean'))
require(old[parent_key]['sha256']==digest(PARENT/'lib/DiophantineConsistency/AdaptiveAQ32.olean'), 'parent model object mismatch')
COND_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq31-conditional-nozero-replay/receipt.json'
COND_OBS = COND_RECEIPT.parent/'terminal-observation.json'
cond=json.loads(COND_RECEIPT.read_text()); cond_obs=json.loads(COND_OBS.read_text())
require(digest(COND_RECEIPT)=='2a43ea68de21735f83f427867e92901125944e6d463cbb1d9a81c3bf7afff234', 'conditional receipt pin')
require(cond['status']=='MATCHED_PASS' and cond_obs['tool_session']==84844 and cond_obs['observed_exit_code']==0 and cond_obs['receipt_sha256']==digest(COND_RECEIPT), 'conditional observed exit')
condrow=cond['runs'][1]['rows'][0]; condpeer=Path(cond['runs'][1]['run'])
require(condrow['module']=='AdaptiveAQ31ConditionalNoZero' and digest(SRC/(condrow['module']+'.lean'))==condrow['source_sha256'] and digest(condpeer/'lib/DiophantineConsistency'/(condrow['module']+'.olean'))==condrow['object_sha256'] and digest(COND_RECEIPT.parent/'peer/logs'/(condrow['module']+'.log'))==condrow['log_sha256'], 'conditional model peer')
condgate={str(COND_RECEIPT):digest(COND_RECEIPT),str(COND_OBS):digest(COND_OBS)}
records=[]
try:
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-aq31-conditional-native-'+label+'-'))
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
            expected={'AdaptiveAQ31Context':0,'AdaptiveAQ31Literal':0,'AdaptiveAQ31Maps':2,'AdaptiveAQ31Transport':2,'AdaptiveAQ31':1,'AdaptiveAQ31ConditionalNoZero':1,'IPRAAQ31ConditionalBridge':3}[name]
            require(len(reports)==expected, ('unexpected axiom report count',name,len(reports),expected))
            for report in reports:
                require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('unexpected axiom',name,report))
            if name in {row['module'] for row in model['runs'][1]['rows']}:
                prior=next(row for row in model['runs'][1]['rows'] if row['module']==name)
                require(digest(obj)==prior['object_sha256'], ('rebuilt model object mismatch',name))
            if name == 'AdaptiveAQ31ConditionalNoZero':
                require(digest(obj)==condrow['object_sha256'], 'rebuilt conditional object mismatch')
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(PARENT_OBS)==base['parent_observation'] and digest(MODEL_RECEIPT)==base['model_receipt'] and digest(MODEL_OBS)==base['model_observation'] and digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums31-degree6/candidate.json')==base['candidate'] and digest(D.parent/'adaptive-aq31-proof/verify_literal.py')==base['literal_verifier'], 'fixed input changed')
        require(all(digest(p)==h for p,h in condgate.items()), 'conditional gate changed')
        require(all(digest(SRC/(name+'.lean'))==base['sources'][name] for name in modules),'workspace source drift')
        check_guard(guards)
        records.append({'label':label,'run':str(run),'rows':rows,'guarded_companion_paths':len(guards),'guards':guards})
    for a,b in zip(records[0]['rows'],records[1]['rows']):
        require(a==b, ('replay mismatch',a,b))
    report={'status':'MATCHED_PASS','base':base,'conditional_gate':condgate,'runs':records,
            'scope':'Two focused same-provider source/object/log and direct dependency companion replays; transitive project ancestry, package transitive ancestry and dynamic imports are inherited. These point-in-time source checks are not a full current-source closure.'}
    (OUT/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('MATCHED_PASS',len(modules),'rows',flush=True)
except BaseException as e:
    (OUT/'failure.txt').write_text(repr(e)+'\n')
    raise
