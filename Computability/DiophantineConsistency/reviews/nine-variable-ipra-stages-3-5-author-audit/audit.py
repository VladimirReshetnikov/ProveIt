#!/usr/bin/env python3
"""Audit three retained author stages and exact warning policies, without Lean."""
from hashlib import sha256
from pathlib import Path
import json
import os
import sys
if not __debug__ or sys.flags.optimize: raise RuntimeError('optimized Python is rejected')
HERE=Path(__file__).resolve().parent;DC=HERE.parents[1];COPY=HERE/'author'
LIVE=Path('/tmp/nine-ipra-guarded-author-20261102-h')
PARENT=Path('/tmp/ipra-standard-qm40-author-run-02')
NATIVE=Path('/tmp/ipra-qm40-incremental-author-20261102-d')
manifest_path=DC/'reviews/nine-variable-ipra-first-two-stages-author-audit/author/manifest.json'
receipt_pins=('871c64b0dd0c52619e3107d3f3dcebdd49a9bab1762e3e30667de320fdc17c92',
              '68e92da770d4ac5ff175531dfe6c334822a0a6d91e9af59f1e8f2ca56f2676e7',
              'a7d20539d164f3d5988a6f67b8ffdf8291f757faa5138a56783a86e2e2afdc16')
names=('DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.ModelArithmetic',
       'DiophantineConsistency.ModelExponentialCongruence')
sourcehashes=('3870325628b4148b2825e1af96bbec91ecbb115e2e57a83d580df97ea53f07aa',
              '2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6',
              'e1c432af6305090e792b8f18d9279693ceabf0bcf15e6368b21be42f6eb77704')
objhashes=('b6b6217f15586efe7f0fec4d2c94e3824e995ae40515d08550968f89b4888dd7',
           '252db63f2ec2494b7c7c25744c6aed5a28ae0b353004f0d197cab7559f82644b',
           'd71fe6b56e3aea8ddc2b5ef27254c742fe18e955232077a8a8b15d569e9134d0')
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p)
    if not os.path.lexists(p):return None
    need(p.is_file(),'nonfile guard: '+str(p))
    return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def check_records(items,label):
    bad=[p for p,v in items.items() if record(p)!=v]
    need(not bad,label+' drift: '+str(bad[:3]))
def check_copy(path):
    need(sha(COPY/path)==sha(LIVE/path),'retained/live mismatch: '+str(path))
need(sha(manifest_path)=='38e40bfb891c8c6a22d772552b4f4fa2a8ce844d99db5505bb84b01bcc478ec5',
     'prior retained manifest')
manifest=json.loads(manifest_path.read_text())
need(manifest['runner_sha256']==sha(DC/'research/nine-variable-ipra/bounded-build-preflight/replay.py')==
     '870ea642c6d494574998d00070c2cc13d10f6432b9775978a45c4d9a783875cf','runner pin')
roots=(LIVE/'lib',PARENT/'lib',Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),
       Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
receipts=[]
for i,(name,srch,objh,pin) in enumerate(zip(names,sourcehashes,objhashes,receipt_pins),3):
    n=f'{i:03d}';recpath=Path('receipts')/(n+'.json');check_copy(recpath)
    need(sha(COPY/recpath)==pin,'receipt pin')
    r=json.loads((COPY/recpath).read_text());receipts.append(r)
    need(r['status']=='PASS' and r['module']==name and r['source_sha256']==srch,'receipt')
    mod=Path(*name.split('.'));source=LIVE/'src'/mod.with_suffix('.lean');target=LIVE/'lib'/mod.with_suffix('.olean')
    frozen=COPY/'src'/(name.split('.')[-1]+'.lean')
    spec=manifest['modules'][i-1]
    need(spec['module']==name and spec['source_sha256']==srch and sha(DC.parents[1]/spec['source'])==srch and
         sha(source)==srch==sha(frozen) and record(target)==r['output'] and sha(target)==objh,'source/object')
    success=Path(r['log']).parent
    need(success.parent==LIVE/'attempts','success attempt location')
    need(sha(success/'object.olean')==objh and os.stat(target).st_ino==os.stat(success/'object.olean').st_ino and
         os.stat(target).st_dev==os.stat(success/'object.olean').st_dev,'published hard link')
    rel=Path('attempts')/success.name
    for file in ('compile.log','deps.stdout','deps.stderr'):check_copy(rel/file)
    need(sha(COPY/rel/'compile.log')==r['log_sha256'] and (COPY/rel/'deps.stderr').read_bytes()==b'',
         'log/dependency stderr')
    check_records(r['direct_guards'],'direct guards');check_records(r['warning_policy_guards'],'warning guards')
    lines=(COPY/rel/'deps.stdout').read_text().splitlines()
    need(set(lines)=={v['path'] for v in r['direct'].values()},'dependency listing')
    for item in r['direct'].values():
        path=Path(item['path']);need(record(path)==item['record'] and
             r['direct_guards'].get(str(path))==item['record'],'selected input')
        owner=next((x for x in roots if path.is_relative_to(x)),None);need(owner is not None,'input root')
        stem=str(path.relative_to(owner))[:-len('.olean')];candidates=[]
        for root in roots:
            for suffix in suffixes:need(str(root/(stem+suffix)) in r['direct_guards'],'companion guard')
            p=str(root/(stem+'.olean'))
            if r['direct_guards'][p] is not None:candidates.append((p,r['direct_guards'][p]))
        need(candidates and candidates[0][0]==str(path) and
             all(v['sha256']==item['record']['sha256'] for _,v in candidates),'input precedence/conflict')
    log=(COPY/rel/'compile.log').read_text()
    need(not any(x in log for x in ('error:','sorryAx')),'error/sorry in successful log')
    if i==5:
        need(r['warning_policy'] is None and log=='','stage 5 warning')
        continue
    policy=json.loads((COPY/'warning-policies'/(n+'.json')).read_text())
    for ext in ('json','log'):check_copy(Path('warning-policies')/(n+'.'+ext))
    baseline=(COPY/'warning-policies'/(n+'.log')).read_text()
    rejected=Path(policy['evidence_attempt']);rejected_rel=Path('attempts')/rejected.name
    for file in ('compile.log','deps.stdout','deps.stderr','failure.json'):check_copy(rejected_rel/file)
    failure=json.loads((COPY/rejected_rel/'failure.json').read_text())
    original=(COPY/rejected_rel/'compile.log').read_text()
    need(r['warning_policy']==policy and policy['source_sha256']==srch and
         policy['warning_count']==(1 if i==3 else 3) and baseline.count('warning:')==policy['warning_count'] and
         log.replace(str(source),'<SOURCE>')==baseline==original.replace(str(source),'<SOURCE>') and
         failure['stage']=='compile' and failure['exit']==0 and failure['object_present'] and
         failure['log_sha256']==sha(COPY/rejected_rel/'compile.log') and
         policy['evidence_object_sha256']==sha(rejected/'object.olean')==objh,
         'warning baseline/rejected attempt')
for parent,resultpin,prepin in (
    (PARENT,'0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a',
            'ad79d027343d5e1b5fda641b8c9aaaba288c63f49284b65b10a34e357ca17c9f'),
    (NATIVE,'3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0',
            'c64c712c72a3940b92797c8d62f972de48642b1a775c96507fd4ad5888d34cc8')):
    need(sha(parent/'RESULT.json')==resultpin and sha(parent/'preflight.json')==prepin,'parent receipt')
    result=json.loads((parent/'RESULT.json').read_text());pre=json.loads((parent/'preflight.json').read_text())
    check_records(result['guards'],'parent guards');check_records(pre['fixed'],'parent fixed')
    check_records(pre['sources'],'parent source')
for r in receipts:
    check_records(r['direct_guards'],'direct guards after audit')
    check_records(r['warning_policy_guards'],'warning guards after audit')
print(json.dumps({'status':'PASS_STAGES_3_5_AUTHOR_ARTIFACT_AUDIT','stages':3,
                  'direct_guards':[len(r['direct_guards']) for r in receipts],
                  'normalized_warning_counts':[1,3,0],
                  'scope':'point-in-time author artifacts; no Lean replay or closure audit'},sort_keys=True))
