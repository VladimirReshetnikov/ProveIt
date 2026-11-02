#!/usr/bin/env python3
"""Bounded guard mutations and a real Lean symlink-overlay toy; no real replay."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('author_extension',D/'run.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.LIMIT=1024**4

def bad(label, action):
    try: action()
    except (ValueError, subprocess.CalledProcessError, FileNotFoundError): return
    raise AssertionError(('mutation accepted',label))

with tempfile.TemporaryDirectory(prefix='author-ext-toy-') as tmp:
    root=Path(tmp); repo=root/'repo';repo.mkdir()
    def call(args, **kw):
        return subprocess.run(args,check=True,text=True,capture_output=True,**kw)
    call(['git','init','-q',str(repo)])
    src=repo/'source.lean';src.write_text('import Demo.Base\ntheorem toy : answer = 42 := rfl\n#print axioms toy\n')
    call(['git','-C',str(repo),'add','source.lean'])
    call(['git','-C',str(repo),'-c','user.name=Toy','-c','user.email=toy@example.invalid',
          'commit','-qm','toy source'])
    commit=call(['git','-C',str(repo),'rev-parse','HEAD']).stdout.strip()
    row={'workspace_path':'source.lean','sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'imports':['Demo.Base']}
    manifest={'status':'FROZEN_ADDITIONS','source_commit':commit,'order':['Demo.Use'],
              'sources':{'Demo.Use':row},'axiom_reports':{'Demo.Use':['toy']}}
    assert m.verify_additions(manifest,repo)[0]==['Demo.Use']
    src.write_text(src.read_text()+'-- drift\n')
    bad('source drift',lambda:m.verify_additions(manifest,repo))
    src.write_bytes(call(['git','-C',str(repo),'show',commit+':source.lean']).stdout.encode())
    outside=root/'outside';outside.mkdir();(outside/'source.lean').write_bytes(src.read_bytes())
    (repo/'link').symlink_to(outside,target_is_directory=True)
    bad('source symlink',lambda:m.safe_source(repo,'link/source.lean'))
    bad('output under protected',lambda:m.protected_output(repo/'new',[repo]))
    bad('output ancestor of protected',lambda:m.protected_output(root,[repo]))
    (root/'redirect').symlink_to(repo,target_is_directory=True)
    bad('output symlink escape',lambda:m.protected_output(root/'redirect'/'new',[repo]))
    original=root/'object';original.write_bytes(b'correct')
    digest=hashlib.sha256(b'correct').hexdigest();alias=root/'alias';alias.symlink_to(original)
    guard={str(alias):{'realpath':str(original),'sha256':digest},str(root/'absent'):None}
    m.check_guard(guard)
    (root/'absent').write_text('unexpected');bad('new companion',lambda:m.check_guard(guard));(root/'absent').unlink()
    original.write_bytes(b'changed');bad('object drift',lambda:m.check_guard(guard));original.write_bytes(b'correct')
    (root/'other').write_bytes(b'correct');alias.unlink();alias.symlink_to(root/'other')
    bad('retargeted symlink',lambda:m.check_guard(guard))
    external=root/'external';external.mkdir();ext=external/'P.olean';ext.write_bytes(b'parent')
    parent_guard={str(external/('P'+s)):None for s in m.SUFFIXES}
    parent_guard[str(ext)]={'realpath':str(ext.resolve()),'sha256':hashlib.sha256(b'parent').hexdigest()}
    m.guard_external(ext,parent_guard)
    bad('unrecorded external',lambda:m.guard_external(external/'Other.olean',parent_guard))
    ext.write_bytes(b'substituted');bad('substituted external',lambda:m.guard_external(ext,parent_guard));ext.write_bytes(b'parent')
    (external/'P.olean.private').write_bytes(b'new')
    bad('new external companion',lambda:m.guard_external(ext,parent_guard));(external/'P.olean.private').unlink()
    m.reject_fallbacks((external,),{'Demo'})
    (external/'Demo.olean').write_bytes(b'foreign')
    bad('project fallback injection',lambda:m.reject_fallbacks((external,),{'Demo'}))
    m.reject_parent_shadow([{'direct_inputs':{'Demo.Base':{}}}],{'Demo.Use'})
    bad('parent dependency shadow',lambda:m.reject_parent_shadow([{'direct_inputs':{'Demo.Use':{}}}],{'Demo.Use'}))

    source=root/'lean-src/Demo'; parent=root/'parent/Demo'; overlay=root/'overlay/Demo'
    for p in (source,parent,overlay):p.mkdir(parents=True)
    (source/'Base.lean').write_text('def answer : Nat := 42\n')
    (source/'Use.lean').write_bytes(src.read_bytes())
    lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
    env=dict(os.environ,LEAN_PATH=str(parent.parent),LEAN_NUM_THREADS='1')
    for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
    call([lean,'--root='+str(source.parent),str(source/'Base.lean'),'-o',str(parent/'Base.olean')],env=env)
    (overlay/'Base.olean').symlink_to(parent/'Base.olean')
    env['LEAN_PATH']=str(overlay.parent)
    deps=call([lean,'--deps',str(source/'Use.lean')],env=env).stdout.splitlines()
    assert str(overlay/'Base.olean') in deps
    call([lean,'--root='+str(source.parent),str(source/'Use.lean'),'-o',str(overlay/'Use.olean')],env=env)
    assert (overlay/'Use.olean').is_file() and not (overlay/'Use.olean').is_symlink()
print('PASS_AUTHOR_EXTENSION_GUARDS_AND_LEAN_OVERLAY_TOY')
