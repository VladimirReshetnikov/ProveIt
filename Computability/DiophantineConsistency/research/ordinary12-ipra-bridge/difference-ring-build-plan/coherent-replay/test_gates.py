#!/usr/bin/env python3
"""Isolated fake-source/provider negative controls; no real project build."""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
import gates
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bad(fn):
 try:fn()
 except (ValueError,FileNotFoundError,KeyError):return
 raise AssertionError('invalid input accepted')
with tempfile.TemporaryDirectory(prefix='ipra-coexist-gates-') as temp:
 r=Path(temp);w=r/'w';w.mkdir();subprocess.run(['git','init','-q',str(w)],check=True)
 review=r/'review.json';review.write_text(json.dumps({'status':'PASS_TOY'}));terminal=r/'terminal.json';terminal.write_text(json.dumps({'observed_exit_code':0,'receipt_sha256':H(review)}))
 assert gates.check_review(review,H(review),terminal,H(terminal),'PASS_TOY','observed_exit_code')['observed_exit_code']==0
 bad(lambda:gates.check_review(review,H(review),terminal,H(terminal),'WRONG','observed_exit_code'))
 bad(lambda:gates.check_review(review,H(review),terminal,H(terminal),'PASS_TOY','wrong_exit'))
 (w/'lakefile.toml').write_text('x=1\n');(w/'lean-toolchain').write_text('toy\n');(w/'S.lean').write_text('def x := 1\n')
 subprocess.run(['git','-C',str(w),'add','.'],check=True);subprocess.run(['git','-C',str(w),'-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm','toy'],check=True)
 snap=r/'snap';src=snap/'src/P';src.mkdir(parents=True);f=src/'End.lean';f.write_bytes((w/'S.lean').read_bytes())
 m={'status':'FROZEN_NOT_COMPILED','target':'P.End','root':str(w),'project_modules':1,'order':['P.End'],'sources':{'P.End':{'snapshot_path':'src/P/End.lean','workspace_path':'S.lean','sha256':H(f),'imports':[]}},'external_modules':[],'lakefile_sha256':H(w/'lakefile.toml'),'lean_toolchain_sha256':H(w/'lean-toolchain')}
 mf=snap/'manifest.json';mf.write_text(json.dumps(m));mh=H(mf)
 assert gates.check_sources(snap,mh,w,'P.End',1)['project_modules']==1
 bad(lambda:gates.check_sources(snap,'0'*64,w,'P.End',1));bad(lambda:gates.check_sources(snap,mh,w,'P.End',2))
 (w/'S.lean').write_text('changed\n');bad(lambda:gates.check_sources(snap,mh,w,'P.End',1));(w/'S.lean').write_bytes(f.read_bytes())
 f.unlink();f.symlink_to(w/'S.lean');bad(lambda:gates.check_sources(snap,mh,w,'P.End',1));f.unlink();f.write_bytes((w/'S.lean').read_bytes())
 root=r/'provider';foundation=root/'.lake/build/lib/lean/Foundation';foundation.mkdir(parents=True);obj=foundation/'A.olean';obj.write_bytes(b'fresh')
 pkg=r/'pkg';pkg.mkdir();(pkg/'Foundation').symlink_to(foundation,target_is_directory=True);lean=r/'lean';lean.write_bytes(b'compiler');inputs=r/'inputs.json';inputs.write_text(json.dumps({'lean_sha256':H(lean)}))
 ext=r/'external';ext.write_bytes(b'external');guard={str(ext):{'realpath':str(ext.resolve()),'sha256':H(ext)},str(r/'absent'):None}
 receipt=r/'provider.json';receipt.write_text(json.dumps({'status':'BUILT','exit_code':0,'manifest_sha256':H(inputs),'space_stop':False,'root':str(root),'overlay':str(pkg),'declared_external_guard':guard,'foundation_artifacts':{'A.olean':H(obj)}}));rh=H(receipt)
 assert gates.check_provider(receipt,rh,inputs,H(inputs),lean,H(lean),['Foundation.A'])['foundation_artifacts']==1
 bad(lambda:gates.check_provider(receipt,rh,inputs,H(inputs),lean,H(lean),['Foundation.Missing']))
 bad(lambda:gates.check_provider(receipt,'0'*64,inputs,H(inputs),lean,H(lean)))
 ext.write_bytes(b'changed');bad(lambda:gates.check_provider(receipt,rh,inputs,H(inputs),lean,H(lean)));ext.write_bytes(b'external')
 (foundation/'extra').write_bytes(b'x');bad(lambda:gates.check_provider(receipt,rh,inputs,H(inputs),lean,H(lean)));(foundation/'extra').unlink()
 obj.write_bytes(b'drift');bad(lambda:gates.check_provider(receipt,rh,inputs,H(inputs),lean,H(lean)))
 print('PASS_COHERENT_PREFLIGHT_TOY tracked-source pins drift symlink provider guards inventory')
