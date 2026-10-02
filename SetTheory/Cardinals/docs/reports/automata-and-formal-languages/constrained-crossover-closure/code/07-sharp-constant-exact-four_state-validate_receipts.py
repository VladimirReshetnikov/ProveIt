"""Validate compact receipts; also check regenerated candidates when present."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent
expected={-1:12407380,0:186704,1:14622000,2:15145667,3:3127160,4:202894,5:3837,6:80}
receipt=json.loads((ROOT/'audit_receipt.json').read_text())
for name in ['four-state-pruned-census.log','independent-pruned-census.log']:
    text=(ROOT/name).read_text()
    done=re.search(r'DONE graphs (\d+) tested (\d+) best (\d+)',text)
    assert done and tuple(map(int,done.groups()))==(411,45695722,6)
    counts={int(k):int(v) for k,v in re.findall(r'RANK (-?\d+) COUNT (\d+)',text)}
    assert counts==expected and sum(counts.values())==45695722
assert receipt['retained_scan']['tested']==45695722
for name in ['four-state-high-transient-pairs.txt','independent-high-transient-pairs.txt']:
    file=ROOT/name
    if file.exists():
        data=file.read_bytes()
        assert len(data.splitlines())==23228
        assert hashlib.sha256(data).hexdigest()==receipt['candidate_list_sha256']
family=json.loads((ROOT/'family_verification.json').read_text())
assert family['passed'] and family['number_of_automata']==95
literal=json.loads((ROOT/'literal_rank_seven.json').read_text())
assert literal['passed']
assert [r['maximum_rank'] for r in literal['slices']]==[1,2,3,4,5,6,7,7]
assert sum(r['hull_targets'] for r in literal['slices'])==509
print('Four-state compact receipts validated; regenerated candidates checked if present')
