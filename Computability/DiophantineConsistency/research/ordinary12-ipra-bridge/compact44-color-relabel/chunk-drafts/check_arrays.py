#!/usr/bin/env python3
"""Compare the draft Lean array literals with the audited finite receipt."""
import hashlib,json,re,sys
from pathlib import Path
if not __debug__ or sys.flags.optimize:raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'CompactRelabelBase.lean';RECEIPT=HERE.parent/'receipt.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sha(SOURCE)!='9e5191f12bd4e8bae0fc8992da9779f61964ce9e67af7b69d191061c3cc1bd9f':raise ValueError('Lean source drift')
if sha(RECEIPT)!='2600b91d7cdc5f51a06ef7788e57d4164170d264777d037933231671ca32ef54':raise ValueError('finite receipt drift')
r=json.loads(RECEIPT.read_bytes());mapping={'horizontal':'horizontal_old_to_compact','vertical':'vertical_old_to_compact','rowIndices':'old_row_to_compact_index'}
def check(text):
 for name,key in mapping.items():
  opening='def '+name+' : Array ℕ := #['
  if text.count(opening)!=1:raise ValueError('array opening '+name)
  tail=text.split(opening,1)[1]
  if ']' not in tail:raise ValueError('array terminator '+name)
  chunk=tail.split(']',1)[0]
  if re.sub(r'[\s,\d]','',chunk):raise ValueError('non-literal array '+name)
  xs=list(map(int,re.findall(r'\d+',chunk)))
  if xs!=r[key]:raise ValueError('array mismatch '+name)
text=SOURCE.read_text();check(text)
for before,after in [('  0, 1, 2, 3, 4, 5, 6, 87,','  1, 0, 2, 3, 4, 5, 6, 87,'),('  0, 1, 2, 3, 188, 189,','  1, 0, 2, 3, 188, 189,')]:
 changed=text.replace(before,after,1)
 if changed==text:raise ValueError('mutation unavailable')
 try:check(changed)
 except ValueError:continue
 raise ValueError('mutation not detected')
print('PASS_DRAFT_ARRAYS_MATCH_FINITE_RECEIPT',sha(SOURCE),sha(RECEIPT),'two mutation controls')
