"""Own scratch-only prose successor writer; no maintained edits or supplied execution."""
from pathlib import Path
import difflib, hashlib, json
W=Path(__file__).resolve().parent; D=W/'write-v3'; D.mkdir()
oldhash='66ea2f96202ced805752390b56cc8ce1e902529bad628058e0668bb43585dd92'
review=W.parent/'independent-math-review/review.json'; newhash=hashlib.sha256(review.read_bytes()).hexdigest()
assert newhash=='4c5450280a7f8ebeec2f30df967284ccd74f94d0e0bc4a690954ab25ad281ff5'
for p in sorted((W/'write-v2').glob('*.md')):
 s=p.read_text()
 s=s.replace(oldhash,newhash)
 s=s.replace('Eighteen other pending archives remain outside this batch.', 'At the placement checkpoint, eighteen other pending archives remained outside this batch. The later arrival `1590329560` added `zfc-raw-profile-routing-20261018.zip` to that queue, bringing it to nineteen; it is not included here.')
 s=s.replace('Only this ZIP was retired; 18 other pending archives were not included.', 'Only this ZIP was retired; 18 other pending archives were outside the placement checkpoint. Arrival `1590329560` subsequently added `zfc-raw-profile-routing-20261018.zip`, bringing the separate queue to 19 without changing this batch.')
 if p.name=='host-README.md':
  needle='base article remains unchanged; the collection still has 290 reports.\n'
  assert s.count(needle)==1
  s=s.replace(needle,needle+'The placement checkpoint left eighteen other archives queued; the later raw-profile\nrouting arrival `1590329560` brings that separate queue to nineteen.\n')
 (D/p.name).write_text(s)
 (D/(p.name+'.diff')).write_text(''.join(difflib.unified_diff(p.read_text().splitlines(True),s.splitlines(True),fromfile='preserved-write-v2/'+p.name,tofile='selected-write-v3/'+p.name)))
(W/'write-v3-freeze.json').write_text(json.dumps({'status':'FINAL_SOURCE_ONLY_PROSE_SUCCESSOR','scope':'Current ordinary review hash and separate queue-arrival chronology only; prior v1/v2 remain unchanged.','ordinary_review_sha256':newhash,'selected':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in D.glob('*.md')},'maintained_edits':False},indent=2)+'\n')
