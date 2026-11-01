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
PARENT = Path('/tmp/ipra-aq30-native-peer-ox0mawlq')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq30-native-replay/receipt.json'
PARENT_OBS = PARENT_RECEIPT.parent/'terminal-observation.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq29-model-replay'
modules = ['AdaptiveAQ29Literal', 'AdaptiveAQ29Zeros', 'AdaptiveAQ29Maps', 'AdaptiveAQ29Transport', 'AdaptiveAQ29', 'AdaptiveAQ29Checks']
source_pins = {'AdaptiveAQ29Literal': 'f833a17d537bbd36336fa228cdb14171ee97539c055747fff8f3b1798f8d09f1', 'AdaptiveAQ29Zeros': 'd83579a4b27e4b55d7ad67afb07a95c0235460d97152c10201e8291de8971be7', 'AdaptiveAQ29Maps': '6b3bf80de89d318a26b14daacf0be8b55f628aef17469725d52eaca55a996fdd', 'AdaptiveAQ29Transport': 'a29adc619090a7348f1d41787d4440954e96163ff849917cdc2d7ff6562381e4', 'AdaptiveAQ29': '4c3501a5d893bf008dfe1f8c517f7b499cb3539a5e035d53bfbae97969534c41', 'AdaptiveAQ29Checks': 'c731095a6f31a21f644b25ca1aaf5bf1fe035f136cc142ee50eea121476ec379'}
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
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'parent_observation':digest(PARENT_OBS), 'candidate':digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums29-degree8/candidate.json'), 'literal_verifier':digest(D/'verify_literal.py'),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
require(base['sources']==source_pins and base['literal_verifier']=='34066712ba385cc6c4c6b8eca8235f7faa88cb8c28d29ef4c57c66b78856e455', 'source or verifier identity')
require(base['candidate']=='894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20', 'candidate identity')
check=subprocess.run(['python3',str(D/'verify_literal.py')],capture_output=True,text=True); require(check.returncode==0 and check.stdout.strip()=='PASS: 29 variables, four ports and all 135 Lean literal gates match the pinned graph', ('literal verification',check.stdout,check.stderr))
require(base['parent_state']=='40464f3ab5094baa741063e853fe1910252b10e8668277450ecc0877580b674a', 'parent receipt identity')
require(base['parent_observation']=='11e095ea2293883eb3a5d9e5fd1b931d4be83f1b21865930fcd93245c50f9f79', 'parent observation identity')
parent_obs=json.loads(PARENT_OBS.read_text())
require(parent_obs['tool_session']==85583 and parent_obs['observed_exit_code']==0 and parent_obs['observed_stdout']=='MATCHED_PASS 11 rows' and parent_obs['receipt_sha256']==base['parent_state'], 'parent observed exit')
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(parent_receipt['status']=='MATCHED_PASS' and len(parent_receipt['runs'])==2 and parent_receipt['runs'][0]['rows']==parent_receipt['runs'][1]['rows'] and len(parent_receipt['runs'][1]['rows'])==11 and parent_receipt['runs'][1]['run']==str(PARENT), 'parent receipt')
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
        run=Path(tempfile.mkdtemp(prefix='ipra-aq29-'+label+'-'))
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
            expected={'AdaptiveAQ29Literal':0,'AdaptiveAQ29Zeros':1,'AdaptiveAQ29Maps':2,'AdaptiveAQ29Transport':4,'AdaptiveAQ29':2,'AdaptiveAQ29Checks':9}[name]
            require(len(reports)==expected, ('unexpected axiom report count',name,len(reports),expected))
            for report in reports:
                require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('unexpected axiom',name,report))
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(PARENT_OBS)==base['parent_observation'] and digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums29-degree8/candidate.json')==base['candidate'] and digest(D/'verify_literal.py')==base['literal_verifier'], 'fixed input changed')
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
