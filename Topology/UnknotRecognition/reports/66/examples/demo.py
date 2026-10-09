"""Create and independently replay a signed continuation certificate."""
import json
from pathlib import Path
from signed_continuations.core import *
from signed_continuations.codec import *
from signed_continuations.verify import verify_basis
from signed_continuations.surfaces import *

family=[Candidate(p,-p.blocks,f'fragment-{i}','example-interface') for i,p in enumerate(partitions(4))]
reduction=reduce_family(family)
record={'scope':'algebraic candidate family; not an ambient normal-surface certificate',
        'family':family_to_dict(family),'certificate':reduction.certificate.as_dict()}
assert verify_basis(family_from_dict(record['family']),certificate_from_dict(record['certificate']))
print(f'{len(family)} states -> {len(reduction.candidates)} original witnesses; replay passed.')
out=Path(__file__).with_name('certificate.json');out.write_text(json.dumps(record,indent=2)+'\n')
# Genuine triangulated examples, checked without the partition producer.
disk=fan_disk(3,seams=((0,1),));torus=punctured_torus();cap=fan_disk(3,seams=((0,1),))
for name,fragment in [('disk',disk),('punctured torus',torus)]:
 info=inspect(fragment);completed=inspect(glue(fragment,cap),require_live=False)
 print(f'{name}: prefix Euler {info.euler}, completed Euler {completed.euler}, disk={completed.is_disk}')
