#!/usr/bin/env python3
"""Audit two retained author stages and their warning baseline, without Lean."""
from hashlib import sha256
from pathlib import Path
import json
import os
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
HERE=Path(__file__).resolve().parent
DC=HERE.parents[1]
COPY=HERE/'author'
LIVE=Path('/tmp/nine-ipra-guarded-author-20261102-h')
OLD=Path('/tmp/nine-ipra-guarded-author-20261102-e')
BASE=DC/'research/nine-variable-ipra/bounded-build-preflight'
PARENT=Path('/tmp/ipra-standard-qm40-author-run-02')
NATIVE=Path('/tmp/ipra-qm40-incremental-author-20261102-d')
PINS={
 'manifest.json':'38e40bfb891c8c6a22d772552b4f4fa2a8ce844d99db5505bb84b01bcc478ec5',
 'receipts/001.json':'906f599ff609c08d25c121b0af388888324c0b6253338c0aa43401efd779e8d4',
 'receipts/002.json':'da2ce1ab889c752aefdc2be5c082e035f0e0b70a44f14a37f21639a7a3651675',
 'warning-policies/002.json':'b45cbebc3f41ae10a0592d20f308faef5321411452fc170040266f398b1cba0a',
 'warning-policies/002.log':'943044219534a63996be8e5b15b13b4ae334913c9bf5f40248c2e68d073f0f77',
 'attempts/001-001/deps.stdout':'25d71da947ad9e1778e42d80737130dcba02da31b2490f41b59a5d6a3efa4dfa',
 'attempts/002-001/deps.stdout':'276240047e4f4e0953819f9b968f640669f87e2e538bacca48e81f5896ded34d',
 'attempts/001-001/compile.log':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 'attempts/002-001/compile.log':'3ca55e13780ebdd3633bd9c63e738a34dc1858288e985375208972521c32a5d8',
}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p)
    if not os.path.lexists(p): return None
    need(p.is_file(),'nonfile guard: '+str(p))
    return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def check_records(items,label):
    bad=[p for p,v in items.items() if record(p)!=v]
    need(not bad,label+' drift: '+str(bad[:3]))
def check_copies():
    for p,h in PINS.items(): need(sha(COPY/p)==h==sha(LIVE/p),'retained/live mismatch: '+p)
    for n in ('001','002'):
        need((COPY/'attempts'/f'{n}-001/deps.stderr').read_bytes()==b'' and
             (LIVE/'attempts'/f'{n}-001/deps.stderr').read_bytes()==b'','dependency stderr')

check_copies();manifest=json.loads((COPY/'manifest.json').read_text())
need(manifest['runner_sha256']==sha(BASE/'replay.py')==
     '870ea642c6d494574998d00070c2cc13d10f6432b9775978a45c4d9a783875cf',
     'runner/source manifest')
names=('DiophantineConsistency.WeightedExpressionDegree','DiophantineConsistency.ModelDifferenceRing')
hashes=('452b70df66fa2ff40ae21f99ade7fcd195893363db90b8da9b17fe4028d4e162',
        '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
objects=('948b4e01db000ecf59395fc5555f51bf4b249f8922c40f40bbd6585b190b5772',
         '59ca56d54f6cdca4a25395e3a2bb0657055174bd0f87783e2ad94538208d81e1')
receipts=[]
roots=(LIVE/'lib',PARENT/'lib',Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),
       Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
for i,(name,sourcehash,objhash) in enumerate(zip(names,hashes,objects),1):
    stage=f'{i:03d}';r=json.loads((COPY/'receipts'/(stage+'.json')).read_text());receipts.append(r)
    need(r['status']=='PASS' and r['module']==name and r['source_sha256']==sourcehash,'stage receipt')
    source=LIVE/'src'/Path(*name.split('.')).with_suffix('.lean')
    target=LIVE/'lib'/Path(*name.split('.')).with_suffix('.olean')
    attempt=LIVE/'attempts'/f'{stage}-001'
    spec=manifest['modules'][i-1]
    need(spec['module']==name and spec['source_sha256']==sourcehash and
         sha(DC.parents[1]/spec['source'])==sourcehash and sha(source)==sourcehash and
         record(target)==r['output'] and sha(target)==objhash and
         sha(attempt/'object.olean')==objhash,'source/object')
    need(os.stat(target).st_ino==os.stat(attempt/'object.olean').st_ino and
         os.stat(target).st_dev==os.stat(attempt/'object.olean').st_dev,'atomic hard link')
    log=COPY/'attempts'/f'{stage}-001/compile.log'
    need(sha(log)==r['log_sha256'] and r['log']==str(attempt/'compile.log'),'log receipt')
    check_records(r['direct_guards'],'stage direct guards')
    check_records(r['warning_policy_guards'],'stage warning guards')
    dep=(COPY/'attempts'/f'{stage}-001/deps.stdout').read_text().splitlines()
    need(set(dep)=={d['path'] for d in r['direct'].values()},'direct dependency listing')
    need(all(record(d['path'])==d['record'] and r['direct_guards'].get(d['path'])==d['record']
             for d in r['direct'].values()),'direct input records')
    for item in r['direct'].values():
        path=Path(item['path']);owner=next((root for root in roots if path.is_relative_to(root)),None)
        need(owner is not None,'direct root')
        relative=path.relative_to(owner);stem=str(relative)[:-len('.olean')];candidates=[]
        for root in roots:
            for suffix in suffixes:
                need(str(root/(stem+suffix)) in r['direct_guards'],'missing direct companion guard')
            candidate=str(root/(stem+'.olean'))
            if r['direct_guards'][candidate] is not None: candidates.append((candidate,r['direct_guards'][candidate]))
        need(candidates and candidates[0][0]==str(path) and
             all(v['sha256']==item['record']['sha256'] for _,v in candidates),'direct precedence/conflict')

need(receipts[0]['warning_policy'] is None and (COPY/'attempts/001-001/compile.log').read_bytes()==b'',
     'first stage warnings')
policy=json.loads((COPY/'warning-policies/002.json').read_text())
need(receipts[1]['warning_policy']==policy and policy['source_sha256']==hashes[1] and
     policy['warning_count']==11 and policy['evidence_log_sha256']==
     '89dcf2e1d86d9704398e46710470354e3e45da2dd430e9fae369b3fe00f8f4f1','warning policy')
baseline=(COPY/'warning-policies/002.log').read_text()
newlog=(COPY/'attempts/002-001/compile.log').read_text()
oldlog=(OLD/'attempts/002-001/compile.log').read_text()
newsource=LIVE/'src/DiophantineConsistency/ModelDifferenceRing.lean'
oldsource=OLD/'src/DiophantineConsistency/ModelDifferenceRing.lean'
need(newlog.replace(str(newsource),'<SOURCE>')==baseline==
     oldlog.replace(str(oldsource),'<SOURCE>') and baseline.count('warning:')==11 and
     not any(s in baseline for s in ('error:','sorryAx')),'complete normalized warning output')
need(not (OLD/'lib/DiophantineConsistency/ModelDifferenceRing.olean').exists(),
     'rejected old stage was published')

for parent,resultpin,prepin in (
        (PARENT,'0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a',
                'ad79d027343d5e1b5fda641b8c9aaaba288c63f49284b65b10a34e357ca17c9f'),
        (NATIVE,'3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0',
                'c64c712c72a3940b92797c8d62f972de48642b1a775c96507fd4ad5888d34cc8')):
    need(sha(parent/'RESULT.json')==resultpin and sha(parent/'preflight.json')==prepin,'parent receipt pin')
    result=json.loads((parent/'RESULT.json').read_text());pre=json.loads((parent/'preflight.json').read_text())
    check_records(result['guards'],'parent guards');check_records(pre['fixed'],'parent fixed')
    check_records(pre['sources'],'parent frozen sources')
for r in receipts:
    check_records(r['direct_guards'],'direct guards after check')
    check_records(r['warning_policy_guards'],'warning guards after check')
check_copies()
print(json.dumps({'status':'PASS_FIRST_TWO_AUTHOR_STAGE_ARTIFACT_AUDIT','stages':2,
                  'direct_guards':[len(r['direct_guards']) for r in receipts],
                  'normalized_warnings':11,'scope':'point-in-time author artifact audit; no Lean replay or closure audit'},sort_keys=True))
