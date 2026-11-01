#!/usr/bin/env python3
"""Run a tiny real-Lean rebuild plus stale-fallback and snapshot-drift controls."""
import hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D));from compare import compare
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');tool=lean.parent.parent/'lib/lean'
with tempfile.TemporaryDirectory(prefix='fresh-project-closure-control-') as td:
 root=Path(td);snap=root/'snapshot';src=snap/'src/FreshToy';src.mkdir(parents=True)
 texts={'FreshToy.Base':'def number : Nat := 1\n','FreshToy.Check':'import FreshToy.Base\ntheorem check : number = 1 := rfl\n#print axioms check\n'};rows={}
 for name,text in texts.items():
  p=snap/'src'/(name.replace('.','/')+'.lean');p.write_text(text);rows[name]={'workspace_path':str(p.relative_to(root)),'snapshot_path':str(p.relative_to(snap)),'sha256':H(p),'imports':['FreshToy.Base'] if name.endswith('Check') else []}
 m={'status':'FROZEN_NOT_COMPILED','target':'FreshToy.Check','root':str(root),'project_modules':2,'order':list(texts),'sources':rows};(snap/'manifest.json').write_text(json.dumps(m))
 provider=root/'provider';foundation=provider/'.lake/build/lib/lean/Foundation';foundation.mkdir(parents=True);pkg=provider/'package-lib';pkg.mkdir();(pkg/'Foundation').symlink_to(foundation);(pkg/'Init.olean').symlink_to(tool/'Init.olean');(pkg/'Init').symlink_to(tool/'Init',target_is_directory=True)
 (pkg/'Init.ir').symlink_to(tool/'Init.ir')
 for suffix in ('.private','.server'):
  x=tool/('Init.olean'+suffix)
  if x.exists():(pkg/('Init.olean'+suffix)).symlink_to(x)
 foundation_input=provider/'input.json';foundation_input.write_text(json.dumps({'lean_sha256':H(lean)}));receipt=provider/'build-all-receipt.json';receipt.write_text(json.dumps({'manifest_sha256':H(foundation_input),'status':'BUILT','exit_code':0,'declared_external_guard':{},'overlay':str(pkg),'root':str(provider),'foundation_artifacts':{}}))
 def run(name,extra=()):
  q=subprocess.run(['python3',str(D/'rebuild.py'),'--snapshot',str(snap),'--output',str(root/name),'--provider-receipt',str(receipt),'--snapshot-sha256',H(snap/'manifest.json'),'--provider-sha256',H(receipt),'--foundation-input',str(foundation_input),'--expected-axiom-reports','1',*extra],capture_output=True,text=True)
  f=root/name/'state.json';state=json.loads(f.read_text()) if f.exists() else None;return q,state
 q,s=run('valid');
 if q.returncode: print('LEAN LOG:',Path(s['records'][-1]['log']).read_text())
 assert q.returncode==0 and s['status']=='PASS' and len(s['records'])==2,(q.stdout,q.stderr,s)
 q,peer=run('valid_peer');assert q.returncode==0 and peer['status']=='PASS'
 result=compare(root/'valid/state.json',root/'valid_peer/state.json');assert result['status']=='MATCHED_PASS' and result['rows']==2
 peerstate=root/'valid_peer/state.json';saved=peerstate.read_bytes();bad=json.loads(saved);bad['records'][0]['object_sha256']='0'*64;peerstate.write_text(json.dumps(bad))
 try:compare(root/'valid/state.json',peerstate)
 except ValueError:pass
 else:raise AssertionError('comparator accepted altered object hash')
 peerstate.write_bytes(saved)
 authorstate=root/'valid/state.json';author_saved=authorstate.read_bytes()
 for mode in ('both_missing_row','both_altered_hash','both_missing_dependency','both_altered_axioms'):
  ax=json.loads(author_saved);bx=json.loads(saved)
  for z in (ax,bx):
   if mode=='both_missing_row':z['records'].pop()
   elif mode=='both_altered_hash':z['records'][0]['object_sha256']='0'*64
   elif mode=='both_missing_dependency':z['records'][1]['direct_inputs'].pop('FreshToy.Base')
   else:z['records'][-1]['axiom_reports']=['propext']
  authorstate.write_text(json.dumps(ax));peerstate.write_text(json.dumps(bx))
  try:compare(authorstate,peerstate)
  except ValueError:pass
  else:raise AssertionError('comparator accepted '+mode)
  authorstate.write_bytes(author_saved);peerstate.write_bytes(saved)
 pair=subprocess.run(['python3',str(D/'run_pair.py'),'--snapshot',str(snap),'--output',str(root/'paired'),'--provider-receipt',str(receipt),'--snapshot-sha256',H(snap/'manifest.json'),'--provider-sha256',H(receipt),'--foundation-input',str(foundation_input),'--expected-axiom-reports','1'],capture_output=True,text=True)
 assert pair.returncode==0 and json.loads((root/'paired/pair-state.json').read_text())['status']=='MATCHED_PASS',(pair.stdout,pair.stderr)
 (pkg/'FreshToy').mkdir();q,s=run('fallback');assert q.returncode!=0 and s['status']=='FAILED' and 'project fallback artifact' in s['failure'],(q.stdout,q.stderr,s);(pkg/'FreshToy').rmdir()
 (pkg/'FreshToy.so').write_bytes(b'stale');q,s=run('plugin');assert q.returncode!=0 and s['status']=='FAILED' and 'project fallback artifact' in s['failure'];(pkg/'FreshToy.so').unlink()
 m['sources']['FreshToy.Check']['imports']=[];(snap/'manifest.json').write_text(json.dumps(m));q,s=run('import_mismatch');assert q.returncode!=0 and s['status']=='FAILED' and 'declared and compiler deps disagree' in s['failure'];m['sources']['FreshToy.Check']['imports']=['FreshToy.Base'];(snap/'manifest.json').write_text(json.dumps(m))
 for name,extra in [('bad_manifest',['--snapshot-sha256','0'*64]),('bad_receipt',['--provider-sha256','0'*64]),('bad_report_count',['--expected-axiom-reports','2'])]:
  q,s=run(name,extra);assert q.returncode!=0,(name,q.stdout,q.stderr)
 (foundation/'unexpected.ir').write_text('extra');q,s=run('unexpected_foundation');assert q.returncode!=0 and 'Foundation inventory changed' in s['failure'];(foundation/'unexpected.ir').unlink()
 m['sources']['FreshToy.Base']['snapshot_path']='src/FreshToy/../../outside.lean';(snap/'manifest.json').write_text(json.dumps(m));q,s=run('escape');assert q.returncode!=0 and 'snapshot path' in s['failure'];m['sources']['FreshToy.Base']['snapshot_path']='src/FreshToy/Base.lean';(snap/'manifest.json').write_text(json.dumps(m))
 src.rename(src.parent/'FreshToyActual');src.symlink_to(src.parent/'FreshToyActual',target_is_directory=True);q,s=run('symlink_parent');assert q.returncode!=0 and 'snapshot symlinked parent' in s['failure'];src.unlink();(src.parent/'FreshToyActual').rename(src)
 bad_input=provider/'bad-input.json';bad_input.write_text(json.dumps({'lean_sha256':'0'*64}));bad_receipt=provider/'bad-receipt.json';bad_pr=json.loads(receipt.read_text());bad_pr['manifest_sha256']=H(bad_input);bad_receipt.write_text(json.dumps(bad_pr));q,s=run('compiler_mismatch',['--foundation-input',str(bad_input),'--provider-receipt',str(bad_receipt),'--provider-sha256',H(bad_receipt)]);assert q.returncode!=0
 fake=root/'fake/bin/lean';fake.parent.mkdir(parents=True);fakefoundation=root/'fake/lib/lean/Foundation';fakefoundation.mkdir(parents=True);marker=fakefoundation/'Marker.olean';marker.write_text('synthetic')
 fake.write_text('#!/usr/bin/python3\nimport sys\nprint('+repr(str(marker))+')\n');fake.chmod(0o755)
 fake_input=provider/'fake-input.json';fake_input.write_text(json.dumps({'lean_sha256':H(fake)}));fake_receipt=provider/'fake-receipt.json';fake_pr=json.loads(receipt.read_text());fake_pr['manifest_sha256']=H(fake_input);fake_receipt.write_text(json.dumps(fake_pr))
 q,s=run('foundation_tool_fallback',['--lean',str(fake),'--foundation-input',str(fake_input),'--provider-receipt',str(fake_receipt),'--provider-sha256',H(fake_receipt)]);assert q.returncode!=0 and 'Foundation outside fresh provider' in s['failure'],(q.stdout,q.stderr,s)
 (src/'Base.lean').write_text('def number : Nat := 2\n');q,s=run('drift');assert q.returncode!=0 and s['status']=='FAILED' and 'snapshot drift' in s['failure'],(q.stdout,q.stderr,s)
 print('PASS: paired real-Lean two-module fresh builds and comparator same-state mutations; fallback/plugin, omitted import, hash pins, path escape, symlink parent, Foundation inventory/tool fallback, report count, compiler and source drift controls rejected')
