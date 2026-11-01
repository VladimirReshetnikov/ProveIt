#!/usr/bin/env python3
"""Guarded paired focused source rebuild for the no-premise 31 endpoint."""
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

D=Path(__file__).resolve().parent
ROOT=D.parents[1]
SRC=ROOT/'Lean/DiophantineConsistency'
MANIFEST=D/'manifest.json'
PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL=LEAN.parent.parent/'lib/lean'
OUT=ROOT/'reviews/adaptive-aq31-native-final-replay'
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def scan(stem):
    out={}
    for suffix in suffixes:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            require(p.is_file(),('bad companion',str(p)))
            out[str(p)]={'realpath':str(p.resolve()),'sha256':digest(p)}
        else: out[str(p)]=None
    return out
def check_guard(guard):
    for name,rec in guard.items():
        p=Path(name)
        if rec is None: require(not os.path.lexists(p),('new companion',name))
        else: require(p.is_file() and str(p.resolve())==rec['realpath'] and digest(p)==rec['sha256'],('changed companion',name))

require(not OUT.exists(),'refusing to overwrite evidence')
OUT.mkdir(parents=True)
try:
    require(digest(MANIFEST)=='cfb13e933009e7910eb6ad9b875dc3eb7898d4e2980a6074a82626e4294d7bf0','manifest identity')
    m=json.loads(MANIFEST.read_text()); modules=m['modules']; parent=Path(m['parent'])
    require(len(modules)==23 and len(set(modules))==23 and set(modules)==set(m['sources'])==set(m['reports']),'module manifest')
    driver_hash=digest(__file__);lean_hash=digest(LEAN)
    require(all(digest(SRC/(n+'.lean'))==h for n,h in m['sources'].items()),'workspace source drift')
    for path,h in m['candidates'].items(): require(digest(ROOT/path)==h,('candidate drift',path))
    verifier=ROOT/'research/adaptive-aq31-proof/verify_literal.py'
    require(digest(verifier)==m['verifier_sha256'],'verifier drift')
    check=subprocess.run(['python3',str(verifier)],capture_output=True,text=True)
    require(check.returncode==0 and check.stdout.strip()=='PASS: 31 variables, four ports and all 141 Lean literal gates match the pinned graph',('literal check',check.stdout,check.stderr))
    priors={}; fixed={str(MANIFEST):digest(MANIFEST),str(verifier):digest(verifier)}
    for gate in m['gates']:
        packet=ROOT/'reviews'/gate['name']; receipt=packet/'receipt.json';obs=packet/'terminal-observation.json'
        require(digest(receipt)==gate['receipt_sha256'] and digest(obs)==gate['observation_sha256'],('gate hash',gate['name']))
        fixed[str(receipt)]=digest(receipt);fixed[str(obs)]=digest(obs)
        data=json.loads(receipt.read_text()); observed=json.loads(obs.read_text())
        require(data['status']=='MATCHED_PASS' and len(data['runs'])==2 and data['runs'][0]['rows']==data['runs'][1]['rows'],'prior comparison')
        require(observed['tool_session']==gate['session'] and observed['observed_exit_code']==0 and observed['observed_stdout']==f"MATCHED_PASS {gate['rows']} rows",('prior exit',gate['name']))
        if 'receipt_sha256' in observed: require(observed['receipt_sha256']==gate['receipt_sha256'],'observed receipt pin')
        peer=Path(data['runs'][1]['run'])
        if gate is m['gates'][0]: require(peer==parent,'wrong parent')
        for row in data['runs'][1]['rows']:
            n=row['module']; prior_obj=peer/'lib/DiophantineConsistency'/(n+'.olean'); prior_log=packet/'peer/logs'/(n+'.log'); prior_src=packet/'peer/src/DiophantineConsistency'/(n+'.lean')
            require(digest(prior_obj)==row['object_sha256'] and digest(prior_log)==row['log_sha256'] and digest(prior_src)==row['source_sha256'],('prior row',gate['name'],n))
            fixed[str(prior_obj)]=digest(prior_obj);fixed[str(prior_log)]=digest(prior_log);fixed[str(prior_src)]=digest(prior_src)
            if n in gate['rebuild']:
                require(m['sources'][n]==row['source_sha256'],('prior source',n))
                require(n not in priors,'duplicate prior');priors[n]=row['object_sha256']
        require(set(gate['rebuild']) <= set(r['module'] for r in data['runs'][1]['rows']),('missing prior',gate['name']))
    require(len(priors)==16,'prior object coverage')
    fallback={}
    for n in modules:
        for k,v in scan(PKG/'DiophantineConsistency'/n).items():
            require(v is None,('unexpected package fallback',k));fallback[k]=v
    records=[]
    for label in ('author','peer'):
        run=Path(tempfile.mkdtemp(prefix='ipra-aq31-final-'+label+'-'));lib=run/'lib';lib.mkdir()
        subprocess.run(['cp','-as',str(parent/'lib')+'/.',str(lib)+'/'],check=True)
        snap=OUT/label/'src/DiophantineConsistency';snap.mkdir(parents=True);logs=OUT/label/'logs';logs.mkdir()
        for n in modules:
            shutil.copyfile(SRC/(n+'.lean'),snap/(n+'.lean'))
            require(digest(snap/(n+'.lean'))==m['sources'][n],('snapshot source',n))
        env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
        guards={};rows=[]
        for n in modules:
            source=snap/(n+'.lean')
            deps=subprocess.run([str(LEAN),'--deps',str(source)],env=env,capture_output=True,text=True)
            require(deps.returncode==0 and not deps.stderr,('deps',n,deps.stderr))
            inputs={}
            for line in deps.stdout.splitlines():
                path=Path(line)
                require(path.is_absolute() and path.is_file() and str(path).endswith('.olean'),('bad dependency',n,line))
                require(any(path.is_relative_to(r) for r in (lib,PKG,TOOL)),('unapproved root',n,line))
                for k,v in scan(Path(str(path)[:-6])).items():
                    require(k not in guards or guards[k]==v,('dependency drift',k));guards[k]=v
                inputs[str(path.relative_to(lib)) if path.is_relative_to(lib) else str(path)]=digest(path)
            check_guard(guards);check_guard(fallback)
            obj=lib/'DiophantineConsistency'/(n+'.olean');require(not os.path.lexists(obj),('output exists',n))
            log=logs/(n+'.log')
            with log.open('x') as out:
                proc=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(snap.parent),str(source),'-o',str(obj)],env=env,stdout=out,stderr=subprocess.STDOUT)
            output=log.read_text();require(proc.returncode==0 and obj.is_file(),('lean failure',n,proc.returncode,output))
            require(not any(x in output for x in ('error:','warning:','sorryAx')),('bad log',n,output))
            reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output,re.M|re.S)
            require(len(reports)==m['reports'][n],('axiom report count',n,len(reports)))
            for report in reports: require({x.strip() for x in report.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},('unexpected axiom',n,report))
            if n in priors: require(digest(obj)==priors[n],('rebuilt prior mismatch',n))
            rows.append({'module':n,'exit':proc.returncode,'source_sha256':digest(source),'object_sha256':digest(obj),'log_sha256':digest(log),'direct_inputs':inputs})
            check_guard(guards);print(label,n,'exit',proc.returncode,flush=True)
        require(digest(__file__)==driver_hash and digest(LEAN)==lean_hash,'driver or Lean drift')
        require(all(digest(p)==h for p,h in fixed.items()),'fixed gate drift')
        require(all(digest(SRC/(n+'.lean'))==h for n,h in m['sources'].items()),'workspace source drift')
        require(all(digest(ROOT/path)==h for path,h in m['candidates'].items()),'candidate drift')
        check_guard(guards);check_guard(fallback)
        records.append({'label':label,'run':str(run),'rows':rows,'guarded_companion_paths':len(guards),'guards':guards})
    require(records[0]['rows']==records[1]['rows'],'paired row mismatch')
    report={'status':'MATCHED_PASS','manifest_sha256':digest(MANIFEST),'driver_sha256':driver_hash,'lean_sha256':lean_hash,'fixed':fixed,'fallback':fallback,'prior_objects':priors,'runs':records,'scope':m['scope']}
    (OUT/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('MATCHED_PASS',len(modules),'rows',flush=True)
except BaseException as e:
    (OUT/'failure.txt').write_text(repr(e)+'\n')
    raise
