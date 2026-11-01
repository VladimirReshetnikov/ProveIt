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
PARENT = Path('/tmp/ipra-aq35-peer-qensdsgv')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq35-model-replay/receipt.json'
ORIENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-square-sums46-model-replay/receipt.json'
ORIENT_OBS = ORIENT_RECEIPT.parent/'terminal-observation.json'
PARENT_OBS = PARENT_RECEIPT.parent/'terminal-observation.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-aq34-model-replay'
modules = ['AdaptiveZ46Orientation', 'AdaptiveZ46RootAlgebra', 'AdaptiveAQ34Context', 'AdaptiveAQ34Literal', 'AdaptiveAQ34Zeros', 'AdaptiveAQ34Maps', 'AdaptiveAQ34Norm', 'AdaptiveAQ34Rest', 'AdaptiveAQ34First', 'AdaptiveAQ34Root', 'AdaptiveAQ34Extend', 'AdaptiveAQ34', 'AdaptiveAQ34Checks']
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
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'parent_observation':digest(PARENT_OBS), 'orientation_receipt':digest(ORIENT_RECEIPT), 'orientation_observation':digest(ORIENT_OBS), 'candidate':digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums34/candidate.json'), 'literal_verifier':digest(D/'verify_literal.py'),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
require(base['candidate']=='9c7fdcf0289b0407af4bbb9deaef4d52fd37435c162a8d15199d1ec9902e1f77', 'candidate identity')
check=subprocess.run(['python3',str(D/'verify_literal.py')],capture_output=True,text=True); require(check.returncode==0 and check.stdout.strip()=='PASS: 34 variables, four ports and all 144 Lean literal gates match the pinned graph', ('literal verification',check.stdout,check.stderr))
require(base['parent_state']=='47da4410911b4bc5e160e1e0bba3bc3820916b00ce0d780273ef9c962071b693', 'parent receipt identity')
require(base['parent_observation']=='874f52ffee792deff76cfb531ae0d58027cef190c393e0bcffb2e335f63e2edd', 'parent observation identity')
parent_obs=json.loads(PARENT_OBS.read_text())
require(parent_obs['tool_session']==92751 and parent_obs['observed_exit_code']==0 and parent_obs['observed_stdout']=='MATCHED_PASS 8 rows', 'parent observed exit')
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(parent_receipt['status']=='MATCHED_PASS' and parent_receipt['runs'][1]['run']==str(PARENT), 'parent receipt')
for row in parent_receipt['runs'][1]['rows']:
    require(digest(PARENT/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('parent object',row['module']))
require(base['orientation_receipt']=='a71bfe7fea7db1d13cf7847874900d9def232305a1b4282073849e17d0dad402', 'orientation receipt identity')
require(base['orientation_observation']=='ad5c95ec935abb3cf47613efb58752359aecc579c7f35cb85fb0e9c97f013b1d', 'orientation observation identity')
orient_obs=json.loads(ORIENT_OBS.read_text())
require(orient_obs['tool_session']==90791 and orient_obs['observed_exit_code']==0 and orient_obs['observed_stdout']=='MATCHED_PASS 12 rows' and orient_obs['receipt_sha256']==base['orientation_receipt'], 'orientation observed exit')
orient=json.loads(ORIENT_RECEIPT.read_text())
require(orient['status']=='MATCHED_PASS' and orient['runs'][1]['run']=='/tmp/ipra-square-sums46-peer-jtt6nfwj', 'orientation receipt')
orient_peer=Path(orient['runs'][1]['run'])
for name in ('AdaptiveZ46Orientation','AdaptiveZ46RootAlgebra'):
    row=next(r for r in orient['runs'][1]['rows'] if r['module']==name)
    require(digest(SRC/(name+'.lean'))==row['source_sha256'], ('orientation source mismatch',name))
    require(digest(orient_peer/'lib'/'DiophantineConsistency'/(name+'.olean'))==row['object_sha256'], ('orientation object mismatch',name))
    require(digest(ORIENT_RECEIPT.parent/'peer/logs'/(name+'.log'))==row['log_sha256'], ('orientation log mismatch',name))
records=[]
try:
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-aq34-'+label+'-'))
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
            expected={'AdaptiveZ46Orientation':2,'AdaptiveZ46RootAlgebra':1,'AdaptiveAQ34Context':0,'AdaptiveAQ34Literal':0,'AdaptiveAQ34Zeros':1,'AdaptiveAQ34Maps':2,'AdaptiveAQ34Norm':1,'AdaptiveAQ34Rest':2,'AdaptiveAQ34First':1,'AdaptiveAQ34Root':1,'AdaptiveAQ34Extend':1,'AdaptiveAQ34':2,'AdaptiveAQ34Checks':16}[name]
            require(len(reports)==expected, ('unexpected axiom report count',name,len(reports),expected))
            for report in reports:
                require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('unexpected axiom',name,report))
            if name in ('AdaptiveZ46Orientation','AdaptiveZ46RootAlgebra'):
                prior=next(row for row in orient['runs'][1]['rows'] if row['module']==name)
                require(digest(obj)==prior['object_sha256'], ('rebuilt orientation object mismatch',name))
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(PARENT_OBS)==base['parent_observation'] and digest(ORIENT_RECEIPT)==base['orientation_receipt'] and digest(ORIENT_OBS)==base['orientation_observation'] and digest(ROOT/'Computability/DiophantineConsistency/research/adaptive-square-sums34/candidate.json')==base['candidate'] and digest(D/'verify_literal.py')==base['literal_verifier'], 'fixed input changed')
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
