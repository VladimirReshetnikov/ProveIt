#!/usr/bin/env python3
"""Publish frozen completed build records, never proof objects or new proof invocations."""
from pathlib import Path
import argparse, gzip, hashlib, io, json, shutil, tarfile

def sha(b): return hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--build',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();r=a.build.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);assert not any(out.iterdir()),'Use a fresh empty publication directory'
 review=json.loads((r/'actual-review.json').read_text());assert review['status']=='PASS_CLOSED_KERNEL'
 names=['plan.json','toolchain.json','actual-review.json','build_serial.py','review_actual.py','wait_build.py','wait_build_v2.py','build-run1.stdout','build-run2.stdout','build-run3.stdout','toolchain-switch.log','toolchain-install.log','toolchain-core-install.log','toolchain-stdlib-install.log','toolchain-stdlib-install-v2.log','setup-review.json','coqdep.txt','coqdep.stderr','coqdep-review.json','regeneration-first.log','regeneration-first-review.json','regeneration-opacity.log','regeneration-opacity-review.json','portable-plan-review.json','portable-driver.diff','portable-v3-from-v1.diff','check_portable_controls.py','portable-controls.json','portable-sigterm-control.log','legacy229-pin-observation.json','metadata-finalization.json','literal-check215.log','regenerated-opacity/regeneration215.json']
 paths=[r/n for n in names]
 for name in ['records','attempts','kernel','history']:
  paths.extend(p for p in (r/name).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
 # Full preserved notices accompany the recorded source snapshots.
 notices=[r/'k230-rocq/THIRD_PARTY.md',*(r/'k230-rocq/LICENSES').glob('*')]
 paths.extend(notices)
 assert len(paths)==len(set(paths)) and all(p.is_file() and not p.is_symlink() for p in paths)
 members={}
 archive=out/'evidence.tar.gz'
 with archive.open('wb') as raw, gzip.GzipFile(fileobj=raw,mode='wb',filename='',mtime=0) as gz, tarfile.open(fileobj=gz,mode='w|') as tar:
  for p in sorted(paths,key=lambda p:str(p.relative_to(r))):
   rel=p.relative_to(r).as_posix();b=p.read_bytes();info=tarfile.TarInfo(rel);info.size=len(b);info.mode=0o644;info.mtime=0
   tar.addfile(info,io.BytesIO(b));members[rel]={'bytes':len(b),'sha256':sha(b)}
 index={'status':'PUBLISHED_COMPLETED_BUILD_EVIDENCE','scope':'Exact raw records, logs, source snapshots and preserved history. Compiled objects and installed toolchain binaries are recorded by hash, not bundled.','historical_build_root':str(r),'archive_sha256':sha(archive.read_bytes()),'members':members}
 (out/'evidence-index.json').write_text(json.dumps(index,indent=2)+'\n')
 shutil.copyfile(r/'actual-review.json',out/'actual-review.json')
 for name in ['K215F.Correct215','K215F.CorrectDense215']:
  rec=json.loads((r/'records'/(name+'.json')).read_text());log=Path(rec['source_snapshot']).parent/'output.log'
  shutil.copyfile(log,out/(name+'.log'))
 kernel=Path(review['kernel_record']).parent/'output.log';shutil.copyfile(kernel,out/'coqchk.log')
 print(json.dumps({'files':len(members),'uncompressed_bytes':sum(x['bytes'] for x in members.values()),'archive_bytes':archive.stat().st_size,'archive_sha256':index['archive_sha256']},indent=2))
if __name__=='__main__':main()
