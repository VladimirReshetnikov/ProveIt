#!/usr/bin/env python3
import sys,json,itertools
from pathlib import Path
HERE=Path(__file__).resolve().parent
REF=HERE/'reference/theory_encoding'
sys.path.insert(0,str(REF))
import check_dne_variants as v
import boolean_bundle_variants as b
_,_,rows,prefix,mapping=b.context()
source={x['mask']:x for x in json.loads((HERE/'bundle_variants.json').read_text())['variants']}[2002]
f=v.freeze(source['bundle']);redexes=v.redexes(f)
variants=[]
for mask in range(1<<len(redexes)):
 selected={p for i,p in enumerate(redexes) if mask&(1<<i)}
 g=v.normalize(f,selected)
 r=b.record('bundle2002_dne'+str(mask),g,[],rows,prefix,mapping)
 r.update(mask=3000+mask,proof={'conjunction_source':2002,'additional_DNE_original_addresses':sorted(selected)})
 variants.append(r)
(HERE/'bundle2002_dne_variants.json').write_text(json.dumps({'scope':'conjunction family2002 followed by contextual DNE','variants':variants},indent=2)+'\n')
print('Variants',len(variants),'additional redexes',len(redexes))
