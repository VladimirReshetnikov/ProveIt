from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[1]
out=[]
for a in sorted((R/'sources').iterdir()):
 root=next(p for p in a.iterdir() if p.is_dir())
 if (root/'SHA256SUMS.json').exists():
  mf=root/'SHA256SUMS.json';entries={n:{'sha256':h} for n,h in json.loads(mf.read_text()).items()}
 elif (root/'MANIFEST.sha256').exists():
  mf=root/'MANIFEST.sha256';entries={}
  for line in mf.read_text().splitlines():
   h,n=line.split('  ',1)
   if n in entries:raise ValueError('duplicate manifest member')
   entries[n]={'sha256':h}
 elif (root/'FILE_MANIFEST.json').exists():
  mf=root/'FILE_MANIFEST.json';entries={e['path']:e for e in json.loads(mf.read_text())['files']}
 else:
  mf=root/'MANIFEST.json';entries=json.loads(mf.read_text())['files']
 for n,e in entries.items():
  p=root/n
  if not p.resolve().is_relative_to(root.resolve()):raise ValueError('unsafe path')
  b=p.read_bytes()
  if hashlib.sha256(b).hexdigest()!=e['sha256']:raise ValueError(n+' sha256')
  if 'bytes' in e and len(b)!=e['bytes']:raise ValueError(n+' bytes')
 out.append({'archive':a.name+'.zip','manifest':mf.name,'entries':len(entries),'status':'PASS','manifest_sha256':hashlib.sha256(mf.read_bytes()).hexdigest()})
print(json.dumps(out,indent=2))
(R/'baseline/MANIFEST_CHECKS.json').write_text(json.dumps({'status':'PASS','total_entries':sum(x['entries'] for x in out),'archives':out},indent=2)+'\n')
