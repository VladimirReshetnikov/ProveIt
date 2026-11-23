#!/usr/bin/env python3
"""Create complete JSON proof/countermodel examples and replay their imports."""
import json
from pathlib import Path
from proplogic import *

p,q,r=Var(0),Var(1),Var(2)
examples=[
    ('IPC_identity',decide_ipc((),Imp(p,p)),check_ipc_result),
    ('IPC_excluded_middle_countermodel',decide_ipc((),Or(p,Not(p))),check_ipc_result),
    ('CPC_excluded_middle_proof',truth_table_prove((),Or(p,Not(p))),check_cpc_result),
    ('CPC_article_countervaluation',truth_table_prove((),Imp(p,Imp(Or(q,r),Imp(r,Not(p))))),check_cpc_result),
]
records=[]
for name,result,checker in examples:
    data=result_data(result)
    roundtrip=result_from_data(json.loads(json.dumps(data)))
    assert checker(roundtrip)
    records.append({'name':name,'replay_passed':True,'certificate':data})
path=Path(__file__).with_name('demo_certificates.json')
path.write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{'name':r['name'],'kind':r['certificate']['kind'],'replay_passed':r['replay_passed']}
                  for r in records],indent=2))
