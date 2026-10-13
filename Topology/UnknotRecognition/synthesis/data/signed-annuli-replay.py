"""Replay all five delivered signed-annulus packets with producers disabled."""
from contextlib import ExitStack
import hashlib,json
from pathlib import Path
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
cases=json.loads((ROOT/'fast/signed_annulus_research/corpus.json').read_text())['cases']
names=['signed_annulus_source.signed_annulus_source','signed_annulus_basis.signed_annulus_basis',
       'signed_annulus_basis.compile_signed_quotient','cyclic_basis.cyclic_basis_blocks',
       'cyclic_basis.compile_nielsen','cyclic_basis.rank_two_lift',
       'normal_cut_handlebodies._signed_cut','normal_cut_handlebodies.normal_cut_handlebodies']
records=[]
with ExitStack() as stack:
    for name in names:stack.enter_context(patch('fastunknot.'+name,side_effect=AssertionError(name)))
    for c in cases:
        p=ROOT/'reports/114/results/certificates'/(c['id'].replace('/','__')+'.json')
        raw=p.read_bytes();proof=json.loads(raw)
        assert verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],proof),c['id']
        records.append(dict(id=c['id'],verified=True,packet_sha256=hashlib.sha256(raw).hexdigest()))
report=dict(passed=True,packets=len(records),records=records,disabled_producers=names,
            source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').glob('*.py'))})
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(passed=True,packets=len(records))))
