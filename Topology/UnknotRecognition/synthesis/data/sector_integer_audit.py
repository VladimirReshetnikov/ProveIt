"""Replay retained real-sector transcripts through literal and binary transport."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import types
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.integer_codec import json_safe

BASE='aa7a87aa42d0d546b1bfe017f0a0b5e0731fd449'
PATH='Topology/UnknotRecognition/fast/fastunknot/normal_sector_verify.py'
old=types.ModuleType('fastunknot._frozen_integer_sector_verify')
old.__package__='fastunknot'
exec(compile(subprocess.check_output(['git','show',f'{BASE}:{PATH}']),PATH,'exec'),old.__dict__)

def encoded(proof,zero='0x0'):
    result=deepcopy(proof)
    for entry in result['rays']:
        entry['quadrilaterals']=[hex(x)if x else zero for x in entry['quadrilaterals']]
        entry['euler_characteristic']=hex(entry['euler_characteristic'])
    if 'q_support_certificate'in result:result['q_support_certificate']=encoded(result['q_support_certificate'],zero)
    return json.loads(json.dumps(result))

records=[]
for file,key in [('generic-euler-sector-audit.json','negative_proofs'),
                 ('feasible-span-audit.json','reduced_proofs'),
                 ('matching-support-audit.json','reduced_proofs')]:
    ledger=json.loads((DATA/file).read_text())
    for i,case in enumerate(ledger[key]):
        records.append((file,i,case))
assert len(records)==134
result=[]
disabled=('fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_sector._discover_in_kernel','fastunknot.sector_planar.sector_planar_rays',
    'fastunknot.sector_euler.SourceEuler.__init__','fastunknot.normal_disk_kernel.normal_compressing_disk_count')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in independent replay')))
    for file,i,case in records:
        source,proof=case['triangulation'],case['certificate']
        assert old.verify_sector_exhaustion(source,proof)
        assert verify_sector_exhaustion(source,proof)
        assert proof['rays']
        binary=encoded(proof)
        assert not old.verify_sector_exhaustion(source,binary)
        assert verify_sector_exhaustion(source,binary)
        assert verify_sector_exhaustion(source,encoded(proof,'-0X00'))
        mutated=deepcopy(binary);mutated['rays'][0]['euler_characteristic']=hex((1<<8192)+1)
        assert not verify_sector_exhaustion(source,mutated)
        mutated=deepcopy(proof);mutated['rays'][0]['quadrilaterals'][0]=1<<16384
        assert not verify_sector_exhaustion(source,json.loads(json.dumps(json_safe(mutated))))
        t=len(source['tetrahedra'])
        assert all(all(value.bit_length()<=7*t for value in row['quadrilaterals'])for row in proof['rays'])
        result.append(dict(ledger=file,index=i,status=proof['status'],tetrahedra=t,rays=len(proof['rays']),
            nested_q_support='q_support_certificate'in proof,
            matching_support='matching_support_certificate'in proof,
            literal_accepted=True,frozen_hex_accepted=False,hex_accepted=True,signed_zero_accepted=True,
            large_changed_euler_rejected=True,large_changed_coordinate_rejected=True))
previous=json.loads((DATA/'transport-annulus-audit.json').read_text())['native_source_sha256']
changed=[]
for relative,digest in previous.items():
    if sha256((ROOT/relative).read_bytes()).hexdigest()!=digest:changed.append(relative)
assert changed==['fast/fastunknot/normal_sector_verify.py'],changed
paths=[str(p.relative_to(ROOT))for folder in [ROOT/'fast/fastunknot',ROOT/'fast/tests']for p in sorted(folder.rglob('*.py'))]
pins={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
report=dict(baseline=BASE,baseline_verifier_sha256=sha256(subprocess.check_output(['git','show',f'{BASE}:{PATH}'])).hexdigest(),
    changed_existing_sources=changed,retained_proofs=len(result),records=result,
    new_source_sha256=pins,driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    prior_source_pins=len(previous),producer_disabled=True)
(DATA/'sector-integer-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in ('records','new_source_sha256')}))
