#!/usr/bin/env python3
"""Bounded two-side QM40 replay; provider ancestry remains inherited."""
import hashlib
import json
import re
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
SRC = ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PARENT = Path('/tmp/ipra-qf41-native-peer-ghjxtk23')
PARENT_RECEIPT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-qf41-native-replay/receipt.json'
PKG = Path(os.environ['QM40_PACKAGE_LIB']).resolve(strict=True)
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = ROOT/'Computability/DiophantineConsistency/reviews/adaptive-qm40-native-bounded-replay'
modules = ['AdaptiveQM40Context', 'AdaptiveQM40Zeros', 'AdaptiveQM40Maps', 'AdaptiveQM40Norm', 'AdaptiveQM40Model', 'AdaptiveQM40Checks', 'IPRAQM40Native', 'IPRAQM40NativeChecks']
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
require(shutil.disk_usage(OUT).free >= 4 * 1024**3, 'less than 4 GiB free')
for name in modules:
    for provider in (PARENT/'lib', PKG):
        stem = provider/'DiophantineConsistency'/name
        require(all(not os.path.lexists(str(stem)+suffix) for suffix in suffixes),
                ('candidate module already present in provider',str(stem)))
base = {'driver':digest(__file__), 'lean':digest(LEAN), 'parent_state':digest(PARENT_RECEIPT), 'package_provider':str(PKG), 'candidate':digest(D.parent/'adaptive-square-sums40-quotient-quartic/candidate.json'), 'literal_verifier':digest(D/'verify_literal.py'),
        'sources':{name:digest(SRC/(name+'.lean')) for name in modules}}
require(base['candidate']=='fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d', 'candidate pin')
require(base['parent_state']=='cb0888b2827155534160c44888f929d7277e53a72bbf1f28c7db477fa7ae825a', 'parent receipt pin')
check=subprocess.run(['python3',str(D/'verify_literal.py')],capture_output=True,text=True)
require(check.returncode==0 and check.stdout.strip()=='PASS: 40 named variables, 4 ports and all 166 Lean literal rows match the pinned DAG', ('literal binding',check.stdout,check.stderr))
parent_receipt=json.loads(PARENT_RECEIPT.read_text())
require(parent_receipt['status']=='MATCHED_PASS' and len(parent_receipt['runs'])==2 and parent_receipt['runs'][1]['run']==str(PARENT), 'parent receipt')
for row in parent_receipt['runs'][1]['rows']:
    require(digest(PARENT/'lib'/'DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'], ('parent object',row['module']))
TERMINAL=PARENT_RECEIPT.parent/'terminal-observation.json';term=json.loads(TERMINAL.read_text())
require(term['tool_session']==97560 and term['observed_exit_code']==0 and term['observed_stdout']=='MATCHED_PASS 8 rows' and term['receipt_sha256']==digest(PARENT_RECEIPT), 'parent observed exit')
gate={str(p):digest(p) for p in (TERMINAL,)}
records=[]
try:
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-qm40-native-'+label+'-'))
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
            require(shutil.disk_usage(OUT).free >= 4 * 1024**3, 'less than 4 GiB free')
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
            cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(snap.parent),str(source),'-o',str(obj)]
            log=logs/(name+'.log')
            with log.open('x') as out:
                proc=subprocess.run(cmd,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
            output=log.read_text()
            require(proc.returncode==0 and obj.is_file(), ('lean failure',name,proc.returncode,output))
            require('error:' not in output and 'sorryAx' not in output and 'warning:' not in output, ('bad log',name,output))
            reports=re.findall(r"^'[^']+' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",output,re.M|re.S)
            expected={'AdaptiveQM40Context':0,'AdaptiveQM40Zeros':2,'AdaptiveQM40Maps':2,'AdaptiveQM40Norm':3,'AdaptiveQM40Model':3,'AdaptiveQM40Checks':9,'IPRAQM40Native':0,'IPRAQM40NativeChecks':3}[name]
            require(len(reports)==expected and all({x.strip() for x in axioms.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for axioms in reports),('unexpected axiom reports',name,len(reports),expected))
            rows.append({'module':name,'exit':proc.returncode,'source_sha256':digest(source),
                         'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':depinfo})
            check_guard(guards)
            print(label,name,'exit',proc.returncode,flush=True)
        require(digest(__file__)==base['driver'] and digest(LEAN)==base['lean'] and digest(PARENT_RECEIPT)==base['parent_state'] and digest(D.parent/'adaptive-square-sums40-quotient-quartic/candidate.json')==base['candidate'] and digest(D/'verify_literal.py')==base['literal_verifier'] and all(digest(p)==h for p,h in gate.items()), 'fixed input changed')
        require(all(digest(SRC/(name+'.lean'))==base['sources'][name] for name in modules),'workspace source drift')
        check_guard(guards)
        records.append({'label':label,'run':str(run),'rows':rows,'guarded_companion_paths':len(guards),'guards':guards})
    for a,b in zip(records[0]['rows'],records[1]['rows']):
        require(a==b, ('replay mismatch',a,b))
    report={'status':'MATCHED_PASS','base':base,'parent_gate':gate,'runs':records,
            'scope':'Two focused same-provider source/object/log and direct dependency companion replays; transitive project ancestry, package transitive ancestry and dynamic imports are inherited. These point-in-time source checks are not a full current-source closure.'}
    (OUT/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('MATCHED_PASS',len(modules),'rows',flush=True)
except BaseException as e:
    (OUT/'failure.txt').write_text(repr(e)+'\n')
    raise
