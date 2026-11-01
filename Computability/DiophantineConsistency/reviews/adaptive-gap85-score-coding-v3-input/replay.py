#!/usr/bin/env python3
"""Compile score coding with guarded private overlay and direct resolution."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from common import CHECKS, describe, direct_entries, private_inventory, sha, verify_candidates

D=Path(__file__).resolve().parent;M=D/'manifest.json'
raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==2 and sys.argv[1]==mh
assert sha(D/'replay.py')==m['driver_sha256'] and sha(D/'common.py')==m['common_sha256']
assert sha(D/'prepare.py')==m['preparer_sha256']
R=Path(m['root']);P=Path(m['provider']);RM=Path(m['repair_manifest'])
rr=json.loads(Path(m['repair_receipt']).read_text());rm=json.loads(RM.read_text());rt=json.loads(Path(m['repair_terminal']).read_text())
assert rr['status']=='MATCHED_PASS' and rr['manifest_sha256']==sha(RM)
assert rt['status']=='PASS_EXIT_0_OBSERVED' and rt['manifest_sha256']==sha(RM)
assert rt['comparison_sha256']==sha(m['repair_receipt'])
assert all(rt[x]['exit_code']==0 for x in ('author','peer','comparator','independent_packet_audit'))
assert rr['object_sha256']==rm['expected_olean_sha256'] and rm['score_parent']==str(P)
assert hashlib.sha256(CHECKS).hexdigest()==m['checks_source_sha256']
frozen=D/'sources/DiophantineConsistency'
assert sha(frozen/'AdaptiveGap85ScoreCoding.lean')==m['score_source_sha256']
assert (frozen/'AdaptiveGap85ScoreCodingChecks.lean').read_bytes()==CHECKS

def baseline():
    assert sha(M)==mh
    for path,expected in m['guard'].items():assert describe(path)==expected,('guard changed',path)
    for path,digest in rm['guard'].items():assert Path(path).is_file() and sha(path)==digest,('repair guard changed',path)
    for table in rm['candidates'].values():
        for path,expected in table.items():
            p=Path(path)
            if expected is None:assert not os.path.lexists(p),('repair absence changed',path)
            else:assert p.is_file() and str(p.resolve())==expected['resolved'] and sha(p)==expected['sha256'],('repair candidate changed',path)
    assert direct_entries(P/'lib')==m['provider_root']
    assert direct_entries(P/'lib/DiophantineConsistency')==m['provider_project']
    verify_candidates(m['provider_companions']);verify_candidates(m['score_candidates'])
    assert sha(frozen/'AdaptiveGap85ScoreCoding.lean')==m['score_source_sha256']
    assert (frozen/'AdaptiveGap85ScoreCodingChecks.lean').read_bytes()==CHECKS

baseline()
w=Path(tempfile.mkdtemp(prefix='gap85-score-coding-v3-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in (src/'DiophantineConsistency',lib/'DiophantineConsistency',logs):p.mkdir(parents=True,exist_ok=True)
for p in (P/'lib').iterdir():
    if p.name!='DiophantineConsistency':(lib/p.name).symlink_to(p,target_is_directory=p.is_dir())
for p in (P/'lib/DiophantineConsistency').iterdir():
    if not p.name.startswith('AdaptiveGap85ScoreCoding.') and not p.name.startswith('AdaptiveGap85ScoreCodingChecks.'):
        (lib/'DiophantineConsistency'/p.name).symlink_to(p.resolve(),target_is_directory=p.is_dir())
for name in ('AdaptiveGap85ScoreCoding','AdaptiveGap85ScoreCodingChecks'):
    shutil.copyfile(frozen/(name+'.lean'),src/'DiophantineConsistency'/(name+'.lean'))
shutil.copyfile(M,w/'manifest.json');shutil.copyfile(D/'replay.py',w/'driver.py');shutil.copyfile(D/'common.py',w/'common.py')
initial=private_inventory(lib)
expected_keys={'DiophantineConsistency'}|{x for x in m['provider_root'] if x!='DiophantineConsistency'}|{
    'DiophantineConsistency/'+x for x in m['provider_project']
    if not x.startswith('AdaptiveGap85ScoreCoding.') and not x.startswith('AdaptiveGap85ScoreCodingChecks.')}
assert set(initial)==expected_keys,(set(initial)-expected_keys,expected_keys-set(initial))
for name,entry in m['provider_root'].items():
    if name=='DiophantineConsistency':continue
    x=initial[name];assert x['kind']=='symlink' and x['target']==str(P/'lib'/name) and x['resolved']==entry['resolved'],name
for name,entry in m['provider_project'].items():
    if name.startswith('AdaptiveGap85ScoreCoding.') or name.startswith('AdaptiveGap85ScoreCodingChecks.'):continue
    x=initial['DiophantineConsistency/'+name]
    assert x['kind']=='symlink' and x['target']==entry['resolved'] and x['resolved']==entry['resolved'] and x['sha256']==entry['sha256'],name
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*m['roots'][1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(w),'manifest_sha256':mh,'provider':str(P),'records':[],
       'scope':m['scope'],'overlay_initial':initial,'direct_checks':[],
       'lean_environment':{k:v for k,v in env.items() if k.startswith('LEAN_')}}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def source_audit():
    assert sha(src/'DiophantineConsistency/AdaptiveGap85ScoreCoding.lean')==m['score_source_sha256']
    assert (src/'DiophantineConsistency/AdaptiveGap85ScoreCodingChecks.lean').read_bytes()==CHECKS
    assert sha(w/'manifest.json')==mh and sha(w/'driver.py')==m['driver_sha256'] and sha(w/'common.py')==m['common_sha256']
def deps(name):
    path=src/'DiophantineConsistency'/(name+'.lean')
    result=subprocess.run([m['lean'],'--deps','--root='+str(src),str(path)],cwd=R,env=env,capture_output=True,text=True,check=True)
    assert not result.stderr,result.stderr
    init=rm['selected']['Init']['logical']
    if name=='AdaptiveGap85ScoreCoding':
        expected=[init,init,str(lib/'DiophantineConsistency/AdaptiveGap85BalanceLeast.olean'),
                  str(lib/'BusyBeaver/ZFC/ArithmeticCantor.olean')]
    else:
        expected=[init,init,str(lib/'DiophantineConsistency/AdaptiveGap85ScoreCoding.olean')]
    assert result.stdout.splitlines()==expected,(name,result.stdout,expected)
    return [{'logical':x,'entry':describe(x)} for x in expected]
def audit(stage,outputs):
    baseline();source_audit()
    expected=dict(initial)
    for name,row in outputs.items():
        path=lib/'DiophantineConsistency'/(name+'.olean')
        entry=describe(path);assert entry and entry['kind']=='file' and entry['sha256']==row['object_sha256']
        expected['DiophantineConsistency/'+name+'.olean']=entry
        assert sha(logs/(name+'.log'))==row['log_sha256']
    actual=private_inventory(lib);assert actual==expected,('private overlay changed',stage)
    main=deps('AdaptiveGap85ScoreCoding');checks=deps('AdaptiveGap85ScoreCodingChecks')
    assert main[2]['entry']['resolved']==m['provider_project']['AdaptiveGap85BalanceLeast.olean']['resolved']
    assert main[3]['entry']['resolved']==rm['selected']['BusyBeaver.ZFC.ArithmeticCantor']['resolved']
    if 'AdaptiveGap85ScoreCoding' in outputs:
        assert checks[2]['entry'] and checks[2]['entry']['sha256']==outputs['AdaptiveGap85ScoreCoding']['object_sha256']
    else:assert checks[2]['entry'] is None
    state['direct_checks'].append({'stage':stage,'main':main,'checks':checks,'overlay_entries':len(actual)})
    save()

save();print('ROOT',w,'OVERLAY_ENTRIES',len(initial),flush=True)
try:
    outputs={};audit('before',outputs)
    for name in ('AdaptiveGap85ScoreCoding','AdaptiveGap85ScoreCodingChecks'):
        source=src/'DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=logs/(name+'.log')
        assert not os.path.lexists(obj),name
        with log.open('w') as out:
            result=subprocess.run([m['lean'],'-M6000','-j1','-DElab.async=false','--root='+str(src),str(source),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
        text=log.read_text();row={'module':name,'exit':result.returncode,'source_sha256':sha(source),
             'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'warnings':text.count('warning:')}
        state['records'].append(row);save()
        assert result.returncode==0 and 'error:' not in text and 'warning:' not in text and 'sorryAx' not in text
        if name.endswith('Checks'):
            blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
            assert len(blocks)==3 and all({x.strip() for x in b.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'} for b in blocks),blocks
        outputs[name]=row;audit('after-'+name,outputs)
    state['overlay_final']=private_inventory(lib);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
    state.update(status='FAILED',failure=repr(exc));save();print('FAILED',repr(exc),flush=True);raise
