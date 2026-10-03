"""Convert the producer JSONL to an integer stream for the independent C++ audit."""
from pathlib import Path
import json
base=Path('/workspace/shared/preorder-gamma-degree4/two-attachment')
out=Path(__file__).resolve().parent/'representatives.tsv'
with out.open('w') as f:
 for line in (base/'a2_polynomials.jsonl').open():
  d=json.loads(line)
  values=[d['id']]+d['core_rows']+d['attachments']+[d['orientation_mask'],d['legal_types']]+sum(d['gamma'],[])
  assert len(values)==63
  f.write(' '.join(map(str,values))+'\n')
