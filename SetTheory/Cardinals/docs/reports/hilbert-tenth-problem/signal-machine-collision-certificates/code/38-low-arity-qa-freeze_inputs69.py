"""Authoring-only metadata freeze. Copies were made inertly with cp -a.
No input is changed, and no scientific program is imported or executed.
"""
from pathlib import Path
import hashlib,json,stat
R=Path('/workspace/shared/report69-low-arity-compilers-release-20261004')
origins={'science/low-arity':'/workspace/shared/two-witness-tensor-compiler-20261004',
'audits/low-arity-independent':'/workspace/shared/independent-low-arity-audit-20261004',
'science/exact-degree-comparison':'/workspace/shared/interpolation-exact-degree-20261004',
'audits/exact-degree-comparison':'/workspace/shared/interpolation-exact-degree-independent-audit-20261004'}
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def inv(root):
 out={}
 for p in [root,*sorted(root.rglob('*'))]:
  s=p.lstat();assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)
  row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':'directory' if p.is_dir() else 'file'}
  if p.is_file():
   assert s.st_nlink==1;b=p.read_bytes();row.update(bytes=len(b),sha256=sha(b))
  out[p.relative_to(root).as_posix()]=row
 return out
original=json.loads((R/'qa/ORIGINAL_INPUT_METADATA.json').read_bytes()); additions=[]
for copied,source in origins.items():
 src=Path(source); a=inv(src); b=inv(R/copied); assert a==b,(copied,'copy mismatch')
 for rel,row in a.items():
  key=str(src if rel=='.' else src/rel)
  if key in original: assert original[key]==row,key
  else: original[key]=row;additions.append(key)
(R/'qa/ORIGINAL_INPUT_METADATA.json').write_bytes(enc(original))
(R/'qa/INPUT_FREEZE_RECEIPT.json').write_bytes(enc({'status':'PASS','copied_roots':origins,'copy_bytes_modes_mtimes_equal':True,'added_baseline_entries':len(additions),'note':'Newly accepted audit and comparison source baselines begin at this freeze; earlier baseline entries are checked and retained.'}))
files={};directories={};roots={}
for scope in ('science','audits'):
 for rel,row0 in inv(R/scope).items():
  row=dict(row0);kind=row.pop('kind')
  if rel=='.':roots[scope]=row
  elif kind=='file':files[scope+'/'+rel]=row
  else:directories[scope+'/'+rel]=row
pindata=enc({'format':'Report69 frozen input pins v1','roots':roots,'source_roots':origins,'files':files,'directories':directories})
(R/'INPUT_PINS.json').write_bytes(pindata)
p=R/'tools/release69.py'; lines=p.read_text().splitlines()
for i,line in enumerate(lines):
 if line.startswith('INPUT_PINS_SHA256 ='):lines[i]='INPUT_PINS_SHA256 = '+repr(sha(pindata))
 if line.startswith('PROTECTED ='):
  lines[i]=line[:-1]+", Path('/workspace/shared/independent-low-arity-audit-20261004'), Path('/workspace/shared/interpolation-exact-degree-20261004'), Path('/workspace/shared/interpolation-exact-degree-independent-audit-20261004'))"
p.write_text('\n'.join(lines)+'\n')
p=R/'tools/build_report69.py';lines=p.read_text().splitlines()
for i,line in enumerate(lines):
 if line.startswith('HELPER_SHA256 ='):lines[i]='HELPER_SHA256 = '+repr(sha((R/'tools/release69.py').read_bytes()))
p.write_text('\n'.join(lines)+'\n')
print('Frozen',len(files),'files and',len(directories),'directories; input map',sha(pindata))
