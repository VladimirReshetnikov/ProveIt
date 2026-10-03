"""Read-only provenance inventory of nine incoming substrate reports.

This is intake, not a mathematical review or an author-test replay. Archives
are read from the checkout or their original arrival commit after retirement.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import zipfile

ARRIVALS={
 '060e08a07d8e6a8ad5ab9ff6c1f7465e22e35630':{
  'Linear_Boundary_Transport_Research.zip':'7b2b3505fe36d9f01777bd198742cc1206f1232e0951964d1ee30681c6c5e096',
  'Positive_Spectrum_Diophantine.zip':'fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8',
  'Spectral_Guards_Without_Time_Expansion.zip':'0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53',
  'clock_spectra_research.zip':'dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22',
  'no_borrowed_firings.zip':'390c4c9a6dbe9a7701de8e0b6689a21d60b35c577aa11a9977989c088a8d0d45',
  'unique_polynomial_histories.zip':'0f0f52d5c6617a22cdd0820386eb378c700e5f5c36bfee810ae13818137465e4',
 },
 '2a8a3959980457aeb0fcf62e26860c809b5a2f42':{
  'Conservative_Signal_Diophantine_Frontend.zip':'43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73',
  'Membrane_Motif_Research_Package.zip':'47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99',
  'Universal_Membrane_Research_Package.zip':'dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5',
 },
}

def repository():
 for root in Path(__file__).resolve().parents:
  if (root/'.git').exists():return root
 raise ValueError('Supply --root for a repository checkout')

def read_archive(root,name,commit,expected,*,historical=False):
 rel='docs/incoming/'+name;path=root/rel
 data=path.read_bytes() if path.is_file() and not historical else subprocess.check_output(['git','show',commit+':'+rel],cwd=root)
 if hashlib.sha256(data).hexdigest()!=expected:raise ValueError('Archive bytes changed: '+name)
 return data

def verify(root=None,*,historical=False):
 if type(historical) is not bool:raise ValueError('historical must be Boolean')
 root=repository() if root is None else Path(root).resolve();archives=[]
 for commit,entries in ARRIVALS.items():
  for name,sha in entries.items():
   data=read_archive(root,name,commit,sha,historical=historical);members=[]
   with zipfile.ZipFile(io.BytesIO(data)) as z:
    names=z.namelist()
    if len(names)!=len(set(names)):raise ValueError('Duplicate member path')
    for info in z.infolist():
     p=PurePosixPath(info.filename)
     if p.is_absolute() or '..' in p.parts:raise ValueError('Unsafe archive path')
     if info.is_dir():continue
     body=z.read(info);members.append(dict(path=info.filename,bytes=len(body),sha256=hashlib.sha256(body).hexdigest()))
   archives.append(dict(archive=name,arrival_commit=commit,sha256=sha,archive_bytes=len(data),
    files=members,python_files=[m['path'] for m in members if m['path'].endswith('.py')],
    readmes=[m['path'] for m in members if PurePosixPath(m['path']).name.lower()=='readme.md'],
    article_sources=[m['path'] for m in members if m['path'].endswith('.tex')]))
 return dict(status='INTAKE_ONLY_NOT_FULLY_REVIEWED',archives=archives,
  total_archives=len(archives),total_files=sum(len(a['files']) for a in archives),
  total_python_files=sum(len(a['python_files']) for a in archives),
  scope='Archive/member authentication and README-level scope triage only. No author verifier run or full proof validation is asserted by this receipt.')

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path);p.add_argument('--historical',action='store_true');p.add_argument('--write',action='store_true');a=p.parse_args()
 result=verify(a.root,historical=a.historical);path=Path(__file__).with_suffix('.json')
 if a.write:path.write_text(json.dumps(result,indent=2)+'\n')
 elif json.loads(path.read_text())!=result:raise ValueError('Saved intake receipt differs')
 print(json.dumps({k:result[k] for k in ('status','total_archives','total_files','total_python_files')}))
