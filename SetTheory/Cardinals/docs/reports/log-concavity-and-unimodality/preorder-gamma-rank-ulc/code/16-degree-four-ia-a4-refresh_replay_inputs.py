"""Export only global certificates already present in successful immutable receipts."""
from pathlib import Path
import json,hashlib
A=Path(__file__).parent
records={}
for rp in sorted(A.glob('global_gap*_receipt.json')):
 r=json.loads(rp.read_text())
 assert r['verdict'].startswith('listed global integer-population gaps approved')
 for key,h in r['input_sha256'].items():
  p=Path(key)
  if p.suffix!='.json' or not p.name.startswith('global_integer'):continue
  data=json.loads(p.read_text())
  if not data.get('certificate'):continue
  kind=data.get('target','whole_gap');tid=data['template'];gap=data.get('gap',3)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  pair=next(x for x in r['identities'] if (x['template'],x['gap'])==(tid,gap))
  records[(tid,gap,kind)]={'template':tid,'gap':gap,'target':kind,'certificate':str(p),'sha256':h,'independent_receipt':str(rp),'square_orbits':pair['counts']['positive_square_orbits']}
prog=json.loads((A/'incremental_progress.json').read_text())
manifest={'scope':'approved exact global certificate inputs only; ordinary and face-batch approvals are separate','approved_global_certificates':[records[k] for k in sorted(records)],'complete_templates':prog['complete_templates'],'pending_templates':sorted(set(range(76))-set(prog['complete_templates'])),'ordinary_ledger':str(A/'ordinary_global_gap_approvals.json'),'face_batches':{'small':'small-faces/certificates.jsonl','medium':'medium-faces/certificates_checkpoint2.jsonl'}}
(A/'approved_replay_inputs.json').write_text(json.dumps(manifest,indent=2)+'\n');print('Selected',len(records),'exact global inputs')
