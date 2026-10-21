#!/usr/bin/env python3
"""Independent read-only identity/row correspondence; never imports delivered code."""
from pathlib import Path
import hashlib, io, json, zipfile
P=Path('/tmp/zfc-intake195/extracted/K216_Partial_Selector_2026-10-20')
OUT=Path('/tmp/zfc-intake195/math-review')
sha=lambda b:hashlib.sha256(b).hexdigest()
read_files=['README.md','report.tex','sections/construction.tex','sections/theory.tex','sections/verification.tex','provenance/ATTRIBUTION.md','code/source_equivalence.py','code/reconstruct216.py','code/audit216.py','code/check_joint_fold.py','code/validate_native.py']
read_inventory=[{'path':str(P/f),'sha256':sha((P/f).read_bytes()),'lines':len((P/f).read_text().splitlines()),'scope':'full source/text read'} for f in read_files]
with zipfile.ZipFile(P/'parent/K217_Dominated_Continuation_2026-10-20.zip') as z:
    parent_bytes=(P/'parent/K217_Dominated_Continuation_2026-10-20.zip').read_bytes()
    assert sha(parent_bytes)=='4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809'
    root='K217_Dominated_Continuation_2026-10-20/'
    old_raw=z.read(root+'machine/sites217.json')
    old_table=z.read(root+'machine/k217.native.tm')
    nested=z.read(root+'parent/K218_Dominated_Rho8_2026-10-20.zip')
    assert sha(old_raw)=='9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
    assert sha(old_table)=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088'
    assert sha(nested)=='080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'
    inherited={'code/check_joint_fold.py':z.read(root+'code/check_joint_fold.py')==(P/'code/check_joint_fold.py').read_bytes()}
with zipfile.ZipFile(io.BytesIO(nested)) as z:
    for f in ['validate_native.py','runtime/symbolic_runtime.py','runtime/independent_runtime.py','inputs/legacy_mapping.json']:
        names=[n for n in z.namelist() if n.endswith('/code/'+f)]
        assert len(names)==1,(f,names)
        inherited['code/'+f]=z.read(names[0])==(P/'code'/f).read_bytes()
assert all(inherited.values())
old=json.loads(old_raw); new=json.loads((P/'source/sites216.json').read_bytes())
assert new==json.loads((P/'source/sites216.compact.json').read_bytes())
assert [r[1:] for r in old]==[r[1:] for r in new]
assert old[:37]==new[:37]
assert [r for r in old if not r[0].startswith('11101001001')]==[r for r in new if not r[0].startswith('11101001001')]
assert len(new)==4751 and sum(2 if r[1]=='CD' else 1 for r in new)==6176

def parse(raw):
    out={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=(int(q),int(b));assert key not in out
        assert b in ('0','1') and w in ('0','1') and d in ('L','R')
        out[key]=(int(w),d,int(z))
    states={q for q,b in out};assert set(out)=={(q,b)for q in states for b in(0,1)}
    assert {z for w,d,z in out.values()}-states=={254}
    return out,states
O,Q=parse((P/'machine/prefold217.native.tm').read_bytes());N,R=parse((P/'machine/k216.native.tm').read_bytes())
assert len(Q)==217 and len(R)==216 and R==Q-{183}
incoming={q:[(s,b,w,d)for(s,b),(w,d,z)in O.items()if z==q]for q in(164,183)}
assert incoming=={164:[(143,1,1,'R')],183:[(205,0,0,'R')]}
phi=lambda q:164 if q==183 else q
changed=[]
for (q,b),(w,d,z) in O.items():
    if N[phi(q),b]!=(w,d,phi(z)):changed.append([q,b])
assert changed==[[164,0],[183,0]]
assert O[164,0]==(0,'R',77) and O[183,0]==(0,'R',150)
assert N[164,0]==(0,'L',201) and O[164,1]==O[183,1]==N[164,1]==(1,'R',98)
assert [N[k]for k in[(201,0),(201,1),(195,0),(196,0)]]==[(0,'R',195),(1,'R',196),(0,'R',150),(0,'R',77)]
mp=json.loads((P/'machine/canonicalization.json').read_text());m={int(k):v for k,v in mp['native_to_canonical'].items()}
assert m[0]==0 and m[84]==84 and m[254]==216
record={'status':'SOURCE_AND_ORDINARY_PROOF_REVIEW_CLEAN','role':'Independent full manuscript and selected proof-checker source reader; earlier accepted Source149/152 ordinary-proof reviewer. Not packet author or fresh candidate executor.','scope':'No supplied script, compiler, Lean, Rocq, manifest suite, runtime or blank replay executed. This own script only reads selected bytes/JSON/ZIP members and checks literal source/transition identities.','findings':[], 'precision_notes':['Provider branches are unused by the new selector, not necessarily globally unused; all surviving live roles remain obligations.','The all-initial-tape fold theorem compares the new prefold217 and final216, not arbitrary-tape behavior of the accepted original217 across the source reallocation.','The runtime and startup counts below are delivered evidence, not independently replayed here.'], 'read_inventory':read_inventory,'inherited_byte_equal':inherited,'parent_archive_sha256':sha(parent_bytes),'nested_dominated_archive_sha256':sha(nested),'parent_source_sha256':sha(old_raw),'parent_native_sha256':sha(old_table),'candidate_native_sha256':sha((P/'machine/k216.native.tm').read_bytes()),'candidate_dense_sha256':sha((P/'machine/k216.tm').read_bytes()),'candidate_source_sha256':sha((P/'source/sites216.json').read_bytes()),'candidate_compact_source_sha256':sha((P/'source/sites216.compact.json').read_bytes()),'literal_word_occurrences':len(new),'source_guard_cases':6176,'first37_and_nonAX_unchanged':True,'prefold_states':217,'final_states':216,'unique_incoming':incoming,'changed_old_rows_under_phi':changed,'canonical_dispatch':m[84],'delivered_evidence':{'runtime_guard_cases':6176,'symbolic_rules':1709992,'direct_rows':432,'minimum_affine_duration':13,'startup_steps':313133,'startup_head':-5,'startup_gap':80,'logical_registers':[3,0,0,0,3,0,0,0,0],'spares':[1,130],'one_cells':277},'dossier_sha256':sha((OUT/'dossier.md').read_bytes()),'reviewer_script_sha256':sha(Path(__file__).read_bytes())}
(OUT/'review.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'review_sha256':sha((OUT/'review.json').read_bytes()),'inherited_byte_equal':inherited,'states':216,'source_occurrences':4751},indent=2))
