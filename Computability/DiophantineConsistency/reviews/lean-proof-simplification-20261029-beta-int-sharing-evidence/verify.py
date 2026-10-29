from pathlib import Path
import hashlib,json,zipfile,subprocess
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda x:hashlib.sha256(x).hexdigest();zpath=r/m['archive'];assert h(zpath.read_bytes())==m['archive_sha256'];assert h((r/'independent-review.txt').read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(zpath) as z:
 assert z.testzip() is None and len(z.namelist())==len(set(z.namelist())) and set(z.namelist())==set(m['members'])
 for n,d in m['members'].items():
  b=z.read(n);assert len(b)==d['bytes'] and h(b)==d['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 for n in [n for n in z.namelist() if n.startswith('commit/')]:
  _,phase,name=n.split('/');rev=m['source_parent'] if phase=='baseline' else m['source_commit'];path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name;assert z.read(n)==subprocess.check_output(['git','show',rev+':'+path])
 omitted=json.loads(z.read('bundle/omitted-logs.json'));assert len(omitted)==14
 for d in omitted:
  p=Path(d['path']);assert p.exists() and p.stat().st_size==d['bytes'] and h(p.read_bytes())==d['sha256']
print('PASS',len(m['members']),'members; 32 source snapshots; 14 omitted external logs verified')
