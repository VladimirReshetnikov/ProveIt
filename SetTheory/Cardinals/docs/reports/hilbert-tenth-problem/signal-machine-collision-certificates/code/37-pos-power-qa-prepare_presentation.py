#!/usr/bin/env python3
"""Owned one-time presentation preparation. No scientific code is imported or run."""
from pathlib import Path
import hashlib
import json
import stat
import shutil

ROOT=Path('/workspace/shared/report67-power-reductions-release-20261004')
OLD=Path('/workspace/shared/report66-bounded-certificates-counting-release-20261004')
SOURCES={
 'science/power-baseline':'/workspace/shared/positive-power22-reduction-20261004',
 'science/power-twelve':'/workspace/shared/positive-power12-continuation-20261004',
 'science/exact-degree':'/workspace/shared/interpolation-exact-degree-20261004',
 'science/bounded-certificates':str(OLD/'science/bounded-certificates'),
 'audits/power-baseline':'/workspace/shared/independent-power-module-audit-20261004',
 'audits/power-twelve':'/workspace/shared/independent-power12-audit-20261004',
 'audits/exact-degree':'/workspace/shared/interpolation-exact-degree-independent-audit-20261004',
}
def sha(data): return hashlib.sha256(data).hexdigest()
def encode(value): return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
def tree(root):
 files={}; dirs={}
 for p in sorted(root.rglob('*')):
  s=p.lstat(); rel=p.relative_to(root).as_posix()
  row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
  if stat.S_ISDIR(s.st_mode): dirs[rel]=row
  elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:
   raw=p.read_bytes(); row.update(bytes=len(raw),sha256=sha(raw)); files[rel]=row
  else: raise ValueError('Unsafe entry '+str(p))
 s=root.stat()
 return {'files':files,'directories':dirs,'root':{'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}}

checks={}
for dest,source in SOURCES.items():
 original=tree(Path(source)); copy=tree(ROOT/dest)
 if original!=copy: raise ValueError('Copy differs '+dest)
 checks[dest]={'origin':source,'inventory':original,'faithful_copy':True}
(ROOT/'qa/SOURCE_COPY_COMPARISON.json').write_bytes(encode(checks))
pins={'format':'Report67 frozen input pins v1','roots':{},'source_roots':SOURCES,'files':{},'directories':{}}
for name in ('science','audits'):
 inventory=tree(ROOT/name); pins['roots'][name]=inventory['root']
 pins['files'].update({name+'/'+p:row for p,row in inventory['files'].items()})
 pins['directories'].update({name+'/'+p:row for p,row in inventory['directories'].items()})
data=encode(pins); (ROOT/'INPUT_PINS.json').write_bytes(data)
inputpin=sha(data)
mods=('Report67.tex','power.tex','elimination.tex','twelve.tex','compiler.tex','degree.tex','composition.tex','scope.tex')
protected=tuple(sorted(set(SOURCES.values())|{str(OLD)}))
oldrelease=(OLD/'tools/release66.py').read_text()
release=oldrelease.replace('Report66','Report67').replace('report66','report67').replace('release66','release67')
release=release.replace("INPUT_PINS_SHA256 = '6ddfffa2d40fec72b14da420676a018ac05e5ab527c64feaf16fed13457fa4da'",f"INPUT_PINS_SHA256 = '{inputpin}'")
lines=release.splitlines()
lines=[('MODULES = '+repr(mods)) if line.startswith('MODULES = ') else ('PROTECTED = ('+', '.join('Path('+repr(p)+')' for p in protected)+',)') if line.startswith('PROTECTED = ') else line for line in lines]
release='\n'.join(lines)+'\n'
(ROOT/'tools/release67.py').write_text(release)
helperpin=sha(release.encode())
builder=(OLD/'tools/build_report66.py').read_text().replace('Report66','Report67').replace('report66','report67').replace('release66','release67')
builder=builder.replace("HELPER_SHA256 = '6a86de64d934a9bf13a3780edf7ef92942d72a860146b442ad89949606360344'",f"HELPER_SHA256 = '{helperpin}'")
(ROOT/'tools/build_report67.py').write_text(builder)
selftest=(OLD/'tools/selftest66.py').read_text().replace('Report66','Report67').replace('report66','report67').replace('release66','release67').replace('selftest66','selftest67')
(ROOT/'tools/selftest67.py').write_text(selftest)
provenance=ROOT/'qa/prior-release-tools'; provenance.mkdir()
for name in ('release66.py','build_report66.py','selftest66.py'):
 shutil.copy2(OLD/'tools'/name,provenance/name)
shutil.copy2(OLD/'README.md',provenance/'README.Report66.md')
(ROOT/'qa/TOOL_ADAPTATION.json').write_bytes(encode({'origin':str(OLD),'scope':'Presentation/release tools only; no scientific program execution','changes':['Report number and tool names','Eight manuscript modules','Frozen source-root list','Input pin and helper pin'],'old_hashes':{p.name:sha(p.read_bytes()) for p in provenance.iterdir()},'new_hashes':{p.name:sha(p.read_bytes()) for p in (ROOT/'tools').iterdir()},'input_pins_sha256':inputpin,'helper_sha256':helperpin}))
print(json.dumps({'input_pins':inputpin,'helper':helperpin,'frozen_files':len(pins['files'])}))
