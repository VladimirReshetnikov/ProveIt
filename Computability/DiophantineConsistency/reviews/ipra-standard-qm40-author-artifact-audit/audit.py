#!/usr/bin/env python3
"""Check the recorded standard-QM40 author artifacts, without invoking Lean."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')

DC = Path(__file__).resolve().parents[2]
COPY = DC/'research/ipra-standard-qm40/author-rebuild/observations/attempt02'
LIVE = Path('/tmp/ipra-standard-qm40-author-run-02')
NATIVE = Path('/tmp/ipra-qm40-incremental-author-20261102-d')
BASE = DC/'research/ipra-standard-qm40/author-rebuild/historical-IPRAStandardTheory.log'
HIST = DC/'reviews/ipra-standard-current14-author-trial/state.json'
MODULES = ('IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse',
           'IPRAStandardTheory','IPRAStandardQM40')
PINS = {
    'RESULT.json':'0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a',
    'preflight.json':'ad79d027343d5e1b5fda641b8c9aaaba288c63f49284b65b10a34e357ca17c9f',
    'IPRASuccessorInduction.json':'32cf500b53cc1f10390096eebfd0f7afbc47cfb5620951e47ce09df3e100e08a',
    'IPRAAddOneGeneral.json':'e88f19ac4c8ecf4e94809f363d516ce147566ad64507c0af548eb7ae238686ac',
    'IPRASuccessorInductionConverse.json':'09f7307e36e754667ec1eeaeef26db8f9c3c8f2d88f602494cb7e76c338ca0ad',
    'IPRAStandardTheory.json':'9a83f63dee4cf683641eec16fa6059b7d5aed8e5fc9fe18e63ae96254278e9bf',
    'IPRAStandardQM40.json':'c2562a1dc45d7788118119b66caad53d079fe60cb4f33dfe4dcadb2a7cd31330',
}

def need(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def record(p):
    p=Path(p)
    if not os.path.lexists(p):
        return None
    need(p.is_file(), 'nonfile or dangling guard: '+str(p))
    return {'sha256':digest(p), 'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}

def check_records(items, label):
    bad=[path for path,expected in items.items() if record(path) != expected]
    need(not bad, label+' changed: '+str(bad[:3]))

def check_copies():
    for path,pin in PINS.items():
        need(digest(COPY/path) == pin and digest(LIVE/path) == pin, 'receipt drift: '+path)
    for name in MODULES:
        for path in ('logs/'+name+'.log', 'src/DiophantineConsistency/'+name+'.lean'):
            need(digest(COPY/path) == digest(LIVE/path), 'snapshot/log copy drift: '+path)

check_copies()
pre=json.loads((COPY/'preflight.json').read_text())
result=json.loads((COPY/'RESULT.json').read_text())
need(pre['status'] == 'READY_AUTHOR_STANDARD_QM40_NO_LEAN' and
     result['status'] == 'PASS_AUTHOR_STANDARD_QM40' and result['scope'] == pre['scope'], 'status')
need(digest(pre['parent']) == '3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0',
     'native parent')
prior=json.loads(Path(pre['parent']).read_text())
need(prior['status'] == 'PASS_AUTHOR_INCREMENTAL_QM40_NATIVE', 'native parent status')
need(len(pre['fixed']) == 10 and len(pre['sources']) == 5 and len(pre['guards']) == 200 and
     len(result['guards']) == 440 and len(prior['guards']) == 240, 'guard counts')
for label,items in (('fixed',pre['fixed']),('frozen sources',pre['sources']),
                    ('final guards',result['guards']),('native parent guards',prior['guards'])):
    check_records(items,label)

steps=result['steps']
need([s['module'] for s in steps] == list(MODULES), 'module inventory')
need(set(pre['guards']).issubset(result['guards']), 'initial guards omitted')
lib=LIVE/'lib/DiophantineConsistency'
changed={path for path,value in pre['guards'].items() if result['guards'][path] != value}
need(changed == {str(lib/(name+'.olean')) for name in MODULES}, 'unexpected initial guard change')
roots=(LIVE/'lib', NATIVE/'lib', Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),
       Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
for step in steps:
    name=step['module']
    need(step == json.loads((COPY/(name+'.json')).read_text()) and step['exit'] == 0,
         'individual step: '+name)
    src=LIVE/'src/DiophantineConsistency'/(name+'.lean')
    imports=set(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)) | {'Init'}
    need(set(step['direct']) == imports, 'declared/direct imports: '+name)
    for module,item in step['direct'].items():
        path=Path(item['path'])
        need(record(path) == item['record'] and result['guards'].get(str(path)) == item['record'],
             'selected direct input: '+module)
        owner=next((root for root in roots if path.is_relative_to(root)),None)
        need(owner is not None, 'direct input outside roots')
        relative=path.relative_to(owner)
        need('.'.join(relative.with_suffix('').parts) == module, 'direct module name')
        stem=str(relative)[:-len('.olean')]
        candidates=[]
        for root in roots:
            for suffix in suffixes:
                candidate=str(root/(stem+suffix))
                need(candidate in result['guards'], 'missing direct candidate: '+candidate)
            candidate=str(root/(stem+'.olean'))
            if result['guards'][candidate] is not None:
                candidates.append((candidate,result['guards'][candidate]))
        need(candidates and candidates[0][0] == str(path) and
             all(v['sha256'] == item['record']['sha256'] for _,v in candidates),
             'conflicting direct candidates: '+module)
    output=str(lib/(name+'.olean'))
    need(step['output'][output] == record(output) and step['output'][output] is not None and
         all(value is None for path,value in step['output'].items() if path != output),
         'output/companions: '+name)
    log=(COPY/'logs'/(name+'.log')).read_text()
    need(digest(COPY/'logs'/(name+'.log')) == step['log_sha256'] and
         not any(x in log for x in ('error:','sorryAx')), 'compiler log: '+name)
    if name not in ('IPRAStandardTheory','IPRAStandardQM40'):
        need(log == '', 'unexpected earlier compiler output: '+name)

# Whole-source-pinned warning policy: compare the complete logs after exactly
# the source-path normalization used by the reviewed runner.
need(digest(HIST) == 'bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61',
     'historical state pin')
need(digest(BASE) == '5d4f5799782ce2ffadea3175f6903008a8b03b5d389bbb91a6e9347573b68730',
     'warning baseline pin')
history=json.loads(HIST.read_text())
need(history['status'] == 'AUTHOR_ONLY_PASS', 'historical status')
rows={x['module'].split('.')[-1]:x for x in history['rows']}
for name in MODULES[:-1]:
    need(digest(LIVE/'src/DiophantineConsistency'/(name+'.lean')) == rows[name]['source_sha256'],
         'historical standard source: '+name)
need(rows['IPRAStandardTheory']['log_sha256'] == digest(BASE), 'historical warning log')
baseline=BASE.read_text().replace('/tmp/ipra-standard-current14-author-trial/src/DiophantineConsistency/IPRAStandardTheory.lean','<SOURCE>')
current=(COPY/'logs/IPRAStandardTheory.log').read_text().replace(str(LIVE/'src/DiophantineConsistency/IPRAStandardTheory.lean'),'<SOURCE>')
need(current == baseline and current.count('warning:') == 3, 'complete normalized warning output')
client=(COPY/'logs/IPRAStandardQM40.log').read_text()
need('warning:' not in client, 'client warning')
reports=re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]",client,re.M|re.S)
expected={'DiophantineConsistency.IPRAStandardQM40.'+x for x in
          ('literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency')}
need(len(reports) == 3 and {name for name,_ in reports} == expected and
     all({x.strip() for x in axioms.split(',')} == {'propext','Classical.choice','Quot.sound'}
         for _,axioms in reports), 'client axiom reports')
for label,items in (('fixed',pre['fixed']),('frozen sources',pre['sources']),
                    ('final guards',result['guards']),('native parent guards',prior['guards'])):
    check_records(items,label+' after audit')
check_copies()
print(json.dumps({'status':'PASS_STANDARD_QM40_AUTHOR_ARTIFACT_AUDIT',
                  'steps':len(steps),'fixed':len(pre['fixed']),'sources':len(pre['sources']),
                  'guards':len(result['guards']),'native_parent_guards':len(prior['guards']),
                  'matched_baseline_warnings':3,'axiom_reports':len(reports),
                  'scope':'point-in-time author artifacts; no Lean replay or full closure audit'},sort_keys=True))
