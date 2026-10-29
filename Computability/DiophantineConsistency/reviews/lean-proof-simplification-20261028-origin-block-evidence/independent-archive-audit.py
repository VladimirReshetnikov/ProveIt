from pathlib import Path
import json,zipfile,hashlib,subprocess
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-origin-block-evidence');j=json.loads((p/'BUNDLE.json').read_text());H=lambda b:hashlib.sha256(b).hexdigest();zpath=p/j['archive'];assert H(zpath.read_bytes())==j['archive_sha256'];review=(p/j['independent_review']['file']).read_bytes();assert H(review)==j['independent_review']['sha256']
with zipfile.ZipFile(zpath) as z:
 assert z.testzip() is None and set(z.namelist())==set(j['members'])
 for name,x in j['members'].items():
  b=z.read(name);assert len(b)==x['bytes'] and H(b)==x['sha256']
 assert z.read('prototype/independent-review.txt')==review
 for phase,ref in [('baseline',j['source_parent']),('final',j['source_commit'])]:
  s=subprocess.check_output(['git','show',ref+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticPackingBlocks.lean']);assert z.read('source/'+phase+'.lean')==s
 print('CRC,',len(j['members']),'manifest entries, both git source snapshots and independent review verified')
 print('archive SHA256',j['archive_sha256'],'review SHA256',j['independent_review']['sha256'])
