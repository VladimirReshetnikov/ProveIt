from pathlib import Path
import json
from disc_basis import Candidate, reduce_family
from check_certificate import verify
from reference import partitions
root = Path(__file__).resolve().parents[1]
cs = [Candidate(f'partition-{i}', p, i) for i,p in enumerate(partitions(4))]
kept, out = reduce_family(cs, 4)
source = {'r': 4, 'candidates': [c.record() for c in cs]}
assert verify(source['candidates'], out['certificate'])
(root/'examples'/'input.json').write_text(json.dumps(source, indent=2)+'\n')
(root/'examples'/'certificate.json').write_text(json.dumps(out['certificate'], indent=2)+'\n')
print(f'{len(cs)} supplied candidates -> {len(kept)} representatives; independent check passed.')
