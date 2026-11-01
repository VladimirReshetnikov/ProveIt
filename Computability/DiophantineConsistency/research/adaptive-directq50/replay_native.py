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
PARENT = Path('/tmp/ipra-named51-native-gh3mz02b')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/ipra-named51-native-verification/receipt.json'
MODEL_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-directq50-model-replay/receipt.json'
MODEL_OBS = MODEL_RECEIPT.parent/'terminal-observation.json'
PARENT_COBS = PARENT_RECEIPT.parent/'terminal-observation.json'
PARENT_AOBS = ROOT/'Computability/DiophantineConsistency/reviews/ipra-named51-native-terminal-observations/author.json'
PARENT_POBS = ROOT/'Computability/DiophantineConsistency/reviews/ipra-named51-native-terminal-observations/peer.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-directq50-native-replay'
modules = ['AdaptiveDirectQ50Strong', 'AdaptiveDirectQ50Context', 'AdaptiveDirectQ50', 'AdaptiveDirectQ50Literal', 'AdaptiveDirectQ50Checks', 'IPRADirectQ50Native', 'IPRADirectQ50NativeChecks']
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
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'model_receipt':digest(MODEL_RECEIPT), 'model_observation':digest(MODEL_OBS), 'native_comparator_observation':digest(PARENT_COBS), 'native_author_observation':digest(PARENT_AOBS), 'native_peer_observation':digest(PARENT_POBS),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(digest(PARENT_RECEIPT)=='83ebda7a5d8f9083f698ea52495825054610703f7f66e9d206b9ef475fa54f5f', 'native comparator receipt identity')
require(digest(PARENT_COBS)=='957e9a33143be261a8175c46ef6445650396ea0f86d5f5a2a2613150ccfaa415', 'native comparator observation identity')
require(digest(PARENT_AOBS)=='c446618abd96c85541d0c18e4bde9c3a82e0af36683f06f4a4916daabb4b6f38', 'native author observation identity')
require(digest(PARENT_POBS)=='eb1e106b9fb596ecf4b4848271568858357333d30de1db08eac02e63290382c6', 'native peer observation identity')
co,ao,po=(json.loads(p.read_text()) for p in (PARENT_COBS,PARENT_AOBS,PARENT_POBS))
require(co['tool_session']==99486 and co['observed_exit_code']==0 and co['observed_stdout']=='MATCHED_PASS 4 rows 11643 files' and co['receipt_sha256']==digest(PARENT_RECEIPT) and co['author_terminal_sha256']==digest(PARENT_AOBS) and co['peer_terminal_sha256']==digest(PARENT_POBS), 'native comparator observed exit')
require(ao['tool_session']==82792 and ao['observed_exit_code']==0 and ao['observed_stdout']=='PASS '+parent_receipt['author_path'] and ao['state_sha256']==parent_receipt['author_state_sha256'], 'native author observed exit')
require(po['tool_session']==9702 and po['observed_exit_code']==0 and po['observed_stdout']=='PASS '+str(PARENT) and po['state_sha256']==parent_receipt['peer_state_sha256'], 'native peer observed exit')
require(parent_receipt['status']=='MATCHED_PASS' and parent_receipt['peer_path']==str(PARENT), 'native parent receipt')
require(digest(PARENT/'state.json')==parent_receipt['peer_state_sha256'], 'native parent state')
state=json.loads((PARENT/'state.json').read_text()); require(state['status']=='PASS', 'native parent pass')
for row in state['records']:
    require(digest(PARENT/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('native parent object',row['module']))
require(digest(MODEL_RECEIPT)=='da7d1179478384d9d2d888d09ac8daa00769b1a54a5b94d1074780df35a748c7', 'model receipt identity')
require(digest(MODEL_OBS)=='aa7dd9d687b741443f4753a791eff028d090c5d445c88dda2cb6cf346adf4118', 'model observation identity')
observed=json.loads(MODEL_OBS.read_text()); require(observed['tool_session']==11858 and observed['observed_exit_code']==0 and observed['observed_stdout']=='MATCHED_PASS 5 rows', 'model observed exit')
model=json.loads(MODEL_RECEIPT.read_text()); require(model['status']=='MATCHED_PASS' and len(model['runs'][1]['rows'])==5, 'model receipt')
modelpeer=Path(model['runs'][1]['run'])
for row in model['runs'][1]['rows']:
    require(digest(SRC/(row['module']+'.lean'))==row['source_sha256'], ('model source mismatch',row['module']))
    require(digest(modelpeer/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('model object mismatch',row['module']))
    require(digest(MODEL_RECEIPT.parent/'peer/logs'/(row['module']+'.log'))==row['log_sha256'], ('model log mismatch',row['module']))
old=model['runs'][1]['guards']
parent_key=next(k for k in old if k.endswith('/AdaptiveNamedValues51.olean'))
require(old[parent_key]['sha256']==digest(PARENT/'lib/DiophantineConsistency/AdaptiveNamedValues51.olean'), 'parent model object mismatch')
records=[]
try:
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-directq50-native-'+label+'-'))
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
            expected={'AdaptiveDirectQ50Strong':2,'AdaptiveDirectQ50Context':0,'AdaptiveDirectQ50':3,'AdaptiveDirectQ50Literal':1,'AdaptiveDirectQ50Checks':6,'IPRADirectQ50Native':0,'IPRADirectQ50NativeChecks':3}[name]
            require(len(reports)==expected, ('unexpected axiom report count',name,len(reports),expected))
            for report in reports:
                require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('unexpected axiom',name,report))
            if name in {row['module'] for row in model['runs'][1]['rows']}:
                prior=next(row for row in model['runs'][1]['rows'] if row['module']==name)
                require(digest(obj)==prior['object_sha256'], ('rebuilt model object mismatch',name))
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(MODEL_RECEIPT)==base['model_receipt'] and digest(MODEL_OBS)==base['model_observation'] and digest(PARENT_COBS)==base['native_comparator_observation'] and digest(PARENT_AOBS)==base['native_author_observation'] and digest(PARENT_POBS)==base['native_peer_observation'] and digest(PARENT/'state.json')==parent_receipt['peer_state_sha256'], 'fixed input changed')
        require(all(digest(SRC/(name+'.lean'))==base['sources'][name] for name in modules),'workspace source drift')
        check_guard(guards)
        records.append({'label':label,'run':str(run),'rows':rows,'guarded_companion_paths':len(guards),'guards':guards})
    for a,b in zip(records[0]['rows'],records[1]['rows']):
        require(a==b, ('replay mismatch',a,b))
    report={'status':'MATCHED_PASS','base':base,'runs':records,
            'scope':'Two focused same-provider source/object/log and direct dependency companion replays; transitive project ancestry, package transitive ancestry and dynamic imports are inherited. These point-in-time source checks are not a full current-source closure.'}
    (OUT/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('MATCHED_PASS',len(modules),'rows',flush=True)
except BaseException as e:
    (OUT/'failure.txt').write_text(repr(e)+'\n')
    raise
