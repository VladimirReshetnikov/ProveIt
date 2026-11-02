#!/usr/bin/env python3
"""Check the draft inverse array against the audited row-index receipt."""
import hashlib,json,re,sys
from pathlib import Path
if not __debug__ or sys.flags.optimize:raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;SOURCE=HERE/'CompactRelabelInverseBase.lean';RECEIPT=HERE.parent/'receipt.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sha(SOURCE)!='ed1c50fa4dd5677c1f02c8c14fb1ee332ac1306b8d08d742afbabafb8d629011':raise ValueError('source drift')
if sha(RECEIPT)!='2600b91d7cdc5f51a06ef7788e57d4164170d264777d037933231671ca32ef54':raise ValueError('receipt drift')
r=json.loads(RECEIPT.read_bytes());forward=r['old_row_to_compact_index']
if len(forward)!=942 or sorted(forward)!=[0]+list(range(2,943)):raise ValueError('invalid forward mapping')
expected=[942]*943
for i,j in enumerate(forward):expected[j]=i
text=SOURCE.read_text();mark='def inverseRows : Array ℕ := #['
if text.count(mark)!=1:raise ValueError('array marker')
body=text.split(mark,1)[1].split(']',1)[0]
if re.sub(r'[\s,\d]','',body):raise ValueError('array syntax')
actual=list(map(int,re.findall(r'\d+',body)))
if actual!=expected or actual[1]!=942:raise ValueError('inverse array mismatch')
bad=actual.copy();bad[0],bad[2]=bad[2],bad[0]
if bad==expected:raise ValueError('mutation control failed')
print('PASS_EXPLICIT_INVERSE_MATCHES_RECEIPT',sha(SOURCE),sha(RECEIPT),'one mutation control')
