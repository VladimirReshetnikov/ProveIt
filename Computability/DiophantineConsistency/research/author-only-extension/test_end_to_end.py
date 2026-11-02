#!/usr/bin/env python3
"""Exercise the production orchestration on a synthetic one-module author parent.

The copied runner differs only in test paths, pinned receipt hashes, parent row
count, and hash-rate limit. Mutation cases add an explicit fault at final guard.
This does not validate the real parent or establish a matched replay.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

D=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
def write(p,v):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def call(args,**kw):
    p=subprocess.run(args,text=True,capture_output=True,**kw)
    if p.returncode: raise AssertionError((args,p.returncode,p.stdout,p.stderr))
    return p
def scan(stem):
    out={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        out[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)} if p.is_file() else None
    return out

with tempfile.TemporaryDirectory(prefix='author-ext-e2e-') as td:
    t=Path(td);repo=t/'repo';repo.mkdir();call(['git','init','-q',str(repo)])
    source=repo/'Use.lean';source.write_text('import Demo.Base\ntheorem toy : answer = 42 := rfl\n#print axioms toy\n')
    call(['git','-C',str(repo),'add','Use.lean'])
    call(['git','-C',str(repo),'-c','user.name=Toy','-c','user.email=toy@example.invalid',
          'commit','-qm','toy extension'])
    commit=call(['git','-C',str(repo),'rev-parse','HEAD']).stdout.strip()
    manifest={'status':'FROZEN_ADDITIONS','source_commit':commit,'order':['Demo.Use'],
              'sources':{'Demo.Use':{'workspace_path':'Use.lean','sha256':H(source),'imports':['Demo.Base']}},
              'axiom_reports':{'Demo.Use':['toy']}}
    spec=t/'additions.json';write(spec,manifest)
    snap=t/'parent-snapshot'; parent=t/'parent-pair/author'; plib=parent/'lib'; pkg=t/'package'
    (snap/'src/Demo').mkdir(parents=True);(plib/'Demo').mkdir(parents=True);pkg.mkdir()
    base=snap/'src/Demo/Base.lean';base.write_text('def answer : Nat := 42\n')
    env=dict(os.environ,LEAN_PATH=str(plib),LEAN_NUM_THREADS='1')
    for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
    lean_result=call([str(LEAN),'--root='+str(snap/'src'),str(base),'-o',str(plib/'Demo/Base.olean')],env=env)
    log=parent/'base.log';log.write_text(lean_result.stdout+lean_result.stderr)
    pm={'order':['Demo.Base'],'sources':{'Demo.Base':{'snapshot_path':'src/Demo/Base.lean','sha256':H(base)}}}
    write(snap/'manifest.json',pm)
    provider_root=t/'foundation-provider';(provider_root/'.lake/build/lib/lean/Foundation').mkdir(parents=True)
    foundation_input=t/'foundation-input.json';write(foundation_input,{'toy':True})
    provider=t/'provider.json';write(provider,{'root':str(provider_root),'declared_external_guard':{},'foundation_artifacts':{}})
    init=LEAN.parent.parent/'lib/lean/Init'
    state={'status':'PASS','records':[{'module':'Demo.Base','source_sha256':H(base),'exit':0,
              'log':str(log),'log_sha256':H(log),'direct_inputs':{}}],
           'manifest_sha256':H(snap/'manifest.json'),'provider_receipt_sha256':H(provider),
           'foundation_input_path':str(foundation_input),'foundation_input_sha256':H(foundation_input),
           'snapshot':str(snap),'provider':str(provider),'package_overlay':str(pkg),
           'lean_path':str(LEAN),'lean_sha256':H(LEAN),'outputs':{'Demo.Base':scan(plib/'Demo/Base')},
           'guarded_companions':scan(init)}
    write(parent/'state.json',state)
    audit=t/'audit.json';write(audit,{'status':'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT',
        'author_state_sha256':H(parent/'state.json'),'manifest_sha256':H(snap/'manifest.json'),
        'foundation_provider_receipt_sha256':H(provider)})
    original=(D/'run.py').read_text()
    changes={
      "ROOT = Path(__file__).resolve().parents[4]":f'ROOT = Path({str(repo)!r})',
      "PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')":f'PARENT = Path({str(parent)!r})',
      "PARENT_STATE_SHA = 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'":f"PARENT_STATE_SHA = '{H(parent/'state.json')}'",
      "AUDIT = ROOT / 'Computability/DiophantineConsistency/reviews/fresh-project-author-independent-audit/receipt.json'":f'AUDIT = Path({str(audit)!r})',
      "AUDIT_SHA = 'd21db65b29de29614976a3f32e42a1f44d8ddad60b30e5894abb473cfb5e9bcf'":f"AUDIT_SHA = '{H(audit)}'",
      "len(state['records']) == 1210":"len(state['records']) == 1",
      'LIMIT = 8 * 1024 * 1024':'LIMIT = 1024**4',
    }
    for old,new in changes.items():
        assert original.count(old)==1,old
        original=original.replace(old,new)
    def run_case(label,code,expect_success,reason=None):
        runner=t/(label+'.py');runner.write_text(code);out=t/(label+'-output')
        p=subprocess.run([sys.executable,str(runner),'--manifest',str(spec),'--manifest-sha256',H(spec),
                          '--output',str(out)],capture_output=True,text=True)
        result=json.loads((out/'state.json').read_text())
        if expect_success:
            assert p.returncode==0 and result['status']=='AUTHOR_ONLY_PASS' and len(result['rows'])==1,(p.stdout,p.stderr,result)
        else:
            assert p.returncode!=0 and result['status']=='FAILED' and reason in result['failure'],(p.stdout,p.stderr,result)
    run_case('good',original,True)
    marker='        verify_additions(spec,ROOT);verify_parent(state,audit)'
    assert original.count(marker)==1
    run_case('overlay-mutation',original.replace(marker,
        "        (lib/'Demo/Base.olean').unlink()\n        (lib/'Demo/Base.olean').write_bytes(b'bad')\n"+marker),False,'changed companion')
    run_case('new-companion',original.replace(marker,
        "        (lib/'Demo/Use.olean.private').write_bytes(b'bad')\n"+marker),False,'unexpected companion')
print('PASS_AUTHOR_EXTENSION_END_TO_END_TOY_AND_MUTATIONS')
