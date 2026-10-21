#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
from history_markers import read_table,histories
P=Path(__file__).resolve().parent
path=P/'q13_normal215.native.tm';T=read_table(path)
results=[]
for q in (13,123,91,73,82,161,61):
 for bit in (0,1):
  ans=histories(T,q,bit,8)
  results.append({k:v for k,v in ans.items()if k!='histories'})
receipt={'status':'EXACT_FINITE_BACKWARD_HISTORY_CENSUS','table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scope':'All executions with at least eight preceding transitions. Earlier initial prefixes require separate checking.','results':results}
(P/'marker_summary.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

