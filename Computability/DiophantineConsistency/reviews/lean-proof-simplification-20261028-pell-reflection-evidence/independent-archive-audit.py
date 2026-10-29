from pathlib import Path
import json,zipfile,hashlib,subprocess
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-pell-reflection-evidence');j=json.loads((p/'BUNDLE.json').read_text());H=lambda b:hashlib.sha256(b).hexdigest();arc=p/j['archive'];assert H(arc.read_bytes())==j['archive_sha256'];review=(p/j['independent_review']['file']).read_bytes();assert H(review)==j['independent_review']['sha256']
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None and set(z.namelist())==set(j['members'])
 for name,x in j['members'].items():
  b=z.read(name);assert len(b)==x['bytes'] and H(b)==x['sha256']
 for name in z.namelist():
  if not name.startswith('source/') or not name.endswith('.lean'):continue
  _,phase,basename=name.split('/');ref=j['source_parent'] if phase=='baseline' else j['source_commit'];source=subprocess.check_output(['git','show',ref+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+basename]);assert z.read(name)==source
 matches=[n for n in z.namelist() if n.endswith('independent-review.txt')];assert matches and all(z.read(n)==review for n in matches)
 print('CRC,',len(j['members']),'manifest entries,',sum(n.startswith('source/') and n.endswith('.lean') for n in z.namelist()),'commit/parent source snapshots and independent review verified')
 print('archive SHA256',j['archive_sha256'],'review SHA256',j['independent_review']['sha256'])
