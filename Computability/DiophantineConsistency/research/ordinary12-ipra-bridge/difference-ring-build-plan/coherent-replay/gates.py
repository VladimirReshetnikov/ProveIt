#!/usr/bin/env python3
"""Fail-closed source and provider preflight primitives for a proposed replay."""
import hashlib,json,os,subprocess
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('preflight rejects optimized Python and PYTHONOPTIMIZE')
def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def pin(path,expected):
 p=Path(path)
 if not p.is_file() or digest(p)!=expected:raise ValueError(('pin mismatch',str(p)))
def check_review(receipt,receipt_sha,terminal,terminal_sha,status,exit_key,sha_key='receipt_sha256'):
 pin(receipt,receipt_sha);pin(terminal,terminal_sha)
 r=json.loads(Path(receipt).read_text());t=json.loads(Path(terminal).read_text())
 if r.get('status')!=status or t.get(exit_key)!=0 or t.get(sha_key)!=receipt_sha:
  raise ValueError(('invalid review observation',status))
 return {'status':status,'receipt_sha256':receipt_sha,'terminal_sha256':terminal_sha,'observed_exit_code':0}
def no_symlink_components(path,root):
 path=Path(path);root=Path(root)
 if not path.is_relative_to(root) or root.is_symlink() or not root.is_dir():raise ValueError(('source root',str(root),str(path)))
 for p in (path,*path.relative_to(root).parents):
  q=p if isinstance(p,Path) and p.is_absolute() else root/p
  if q.is_symlink():raise ValueError(('source symlink',str(q)))
 if path.resolve(strict=True)!=path:raise ValueError(('source noncanonical',str(path)))
def check_sources(snapshot,expected_manifest,workspace,target,expected_count):
 snapshot=Path(snapshot).resolve(strict=True);workspace=Path(workspace).resolve(strict=True);mf=snapshot/'manifest.json';pin(mf,expected_manifest);m=json.loads(mf.read_text())
 names=m['order'];sources=m['sources']
 if m['status']!='FROZEN_NOT_COMPILED' or m['target']!=target or m['root']!=str(workspace) or len(names)!=expected_count or len(set(names))!=len(names) or len(sources)!=len(names) or set(sources)!=set(names) or names[-1]!=target:raise ValueError('source manifest coverage')
 if digest(workspace/'lakefile.toml')!=m['lakefile_sha256'] or digest(workspace/'lean-toolchain')!=m['lean_toolchain_sha256']:raise ValueError('project config drift')
 seen=set();paths=[]
 for name in names:
  row=sources[name];expected=snapshot/'src'/(name.replace('.','/')+'.lean');actual=snapshot/row['snapshot_path']
  if actual!=expected:raise ValueError(('snapshot source path',name))
  no_symlink_components(actual,snapshot/'src')
  wp=workspace/row['workspace_path']
  if not wp.is_relative_to(workspace) or wp.resolve(strict=True)!=wp:raise ValueError(('workspace path',name))
  if digest(actual)!=row['sha256'] or digest(wp)!=row['sha256']:raise ValueError(('source drift',name))
  if any(dep in sources and dep not in seen for dep in row['imports']):raise ValueError(('source order',name))
  seen.add(name);paths.append(row['workspace_path'])
 tracked=set(subprocess.check_output(['git','ls-files','-z','--',*paths],cwd=workspace).decode().split('\0'))-{''}
 changed=set(subprocess.check_output(['git','diff','--name-only','-z','HEAD','--',*paths],cwd=workspace).decode().split('\0'))-{''}
 if tracked!=set(paths) or changed:raise ValueError(('untracked or changed sources',sorted(set(paths)-tracked),sorted(changed)))
 pin(mf,expected_manifest)
 return {'project_modules':len(names),'target':target,'manifest_sha256':expected_manifest,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=workspace,text=True).strip(),'direct_foundation_imports':sorted(n for n in m['external_modules'] if n.startswith('Foundation.'))}
def check_guard(g):
 for path,expected in g.items():
  p=Path(path)
  if expected is None:
   if os.path.lexists(p):raise ValueError(('unexpected guard',path))
  elif not p.is_file() or str(p.resolve())!=expected['realpath'] or digest(p)!=expected['sha256']:raise ValueError(('guard mismatch',path))
def check_provider(receipt,expected_receipt,foundation_input,expected_input,lean,expected_lean,foundation_imports=()):
 receipt=Path(receipt);foundation_input=Path(foundation_input);lean=Path(lean);pin(receipt,expected_receipt);pin(foundation_input,expected_input);pin(lean,expected_lean);r=json.loads(receipt.read_text());fi=json.loads(foundation_input.read_text())
 if r['status']!='BUILT' or r['exit_code']!=0 or r['manifest_sha256']!=expected_input or fi['lean_sha256']!=expected_lean or r.get('space_stop') or 'declared_external_guard' not in r:raise ValueError('invalid provider status or pins')
 root=Path(r['root']).resolve(strict=True);foundation=root/'.lake/build/lib/lean/Foundation';pkg=Path(r['overlay'])
 if (pkg/'Foundation').resolve(strict=True)!=foundation:raise ValueError('Foundation overlay mismatch')
 check_guard(r['declared_external_guard']);expected=r['foundation_artifacts']
 for rel,h in expected.items():
  q=foundation/rel
  if Path(rel).is_absolute() or '..' in Path(rel).parts or q.is_symlink() or not q.is_file() or digest(q)!=h:raise ValueError(('Foundation artifact drift',rel))
 actual={str(q.relative_to(foundation)) for q in foundation.rglob('*') if q.is_file() or q.is_symlink()}
 if actual!=set(expected):raise ValueError('Foundation artifact coverage')
 for name in foundation_imports:
  if not name.startswith('Foundation.'):raise ValueError(('invalid Foundation module',name))
  rel=Path(*name.split('.')[1:]).with_suffix('.olean')
  if str(rel) not in expected or (pkg/'Foundation'/rel).resolve(strict=True)!=foundation/rel:raise ValueError(('Foundation direct input',name))
 pin(receipt,expected_receipt);pin(foundation_input,expected_input);pin(lean,expected_lean)
 return {'receipt_sha256':expected_receipt,'foundation_artifacts':len(expected),'guard_paths':len(r['declared_external_guard']),'outer_wrapper_exit_observed':False}
