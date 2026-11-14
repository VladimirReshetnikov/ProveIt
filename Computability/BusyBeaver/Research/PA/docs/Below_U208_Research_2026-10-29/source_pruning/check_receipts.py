import json,re,hashlib
from pathlib import Path
B=Path(__file__).resolve().parent
def require(c,m):
 if not c:raise ValueError(m)
summary={}
for name,layers in [('class_a_guarded',12),('class_b_guarded',12),('class_a_wide',8)]:
 text=(B/'search'/f'{name}.log').read_text();lines=text.splitlines();require(len(lines)==layers,f'{name}: incomplete log');total=1
 for i,line in enumerate(lines):
  m=re.fullmatch(r'depth (\d+) new (\d+) total (\d+)',line);require(m is not None,f'{name}: unexpected line');d,n,t=map(int,m.groups());require(d==i and t==total+n,f'{name}: count mismatch');total=t
 summary[name]={'layers':layers,'additional_tables':total-1,'found_candidates':0}
require(summary==json.loads((B/'search_receipts.json').read_text()),'receipt summary differs')
print(json.dumps({'status':'SEARCH_LOG_RECEIPTS_CONSISTENT','scope':'Receipt parsing, not discovery replay or lower-bound proof','lanes':summary},indent=2))
