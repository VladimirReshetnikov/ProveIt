#!/usr/bin/env python3
"""Summarize actual bounded-search logs; incomplete runs stay incomplete."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parent
RUNS=[
 ('occurrence194',134,'Per-occurrence and global DAG rotations',240,202611140815),
 ('global194',134,'Rotations with fixed/AX compatible folds',240,202611140921),
 ('reparse194',134,'Rotations and whole-word dictionary reparsing',240,202611141317),
 ('globalqns194',135,'QNS rotations with fixed/AX compatible folds',240,202611141901),
 ('globalqns6_3b3b',136,'QNS6 alternate increment-six tree',180,202611141944),
 ('equality_E3',134,'First congruence-head antecedent exchange',240,202611142100),
 ('equality_E4',134,'Second congruence-head antecedent exchange',240,202611142101),
 ('equality_E3Q',134,'First congruence exchange and Q exchange',240,202611142102),
 ('gammaH',134,'Diagonal head Gamma(H)',240,202611142245),
 ('qn6_fixedreuse',135,'QN6 exact reuse of fixed decoder pairs, including increment-three',300,202611142356),
 ('qn6_forced_inc3',135,'QN6 fixed-pair reuse constrained to use increment-three',240,202611150004),
 ('orientation_QN5_3a2',135,'Coefficient-five 3+2 with fixed-pair reuse',150,202611150100),
 ('orientation_QN6_3b3b',135,'Coefficient-six reverse 3+3 with fixed-pair reuse',150,202611150101),
 ('orientation_QN6_2plus4',135,'Coefficient-six 2+4 with fixed-pair reuse',150,202611150102),
]
rows=[]
for name,fixed,description,budget,seed in RUNS:
 path=ROOT/(name+'.log');txt=path.read_text()if path.exists()else''
 match=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',txt)
 row=dict(name=name,description=description,fixed_states=fixed,requested_seconds=budget,seed=seed,status='complete'if match else'incomplete')
 if match:
  it,ac,hits,best,seconds=match.groups();row.update(proposals=int(it),accepted_moves=int(ac),qualifying_hits=int(hits),best_score=int(best),best_score_plus_fixed=fixed+int(best),seconds=float(seconds))
 rows.append(row)
receipt={'repository':'https://github.com/VladimirReshetnikov/ProveIt','commit':'2337ce611a26e308697ccbddb2a1636f989f01c3','runs':rows,'scope':'Bounded stochastic grammar searches. Scores are not machine correctness certificates or lower bounds. No new machine is claimed by these search logs. A hit would still require exact word and source binding, scanner validation, all physical contracts, blank startup, and PA calibration.','action_screens':{}}
for name in ['qns6_action_summary','qns6_action17_summary','qns6_initial','equality_initial','gamma_initial','radix_orientations_initial']:
 p=ROOT/(name+'.json')
 if p.exists():receipt['action_screens'][name]=json.loads(p.read_text())
p=ROOT/'qn6_triple_contracts.json'
if p.exists():
 rs=json.loads(p.read_text());receipt['inc3_direct_contractions']={'cases':len(rs),'minimum_scored_count':min(r['total']for r in rs),'minimum_with_a_forced_contraction':min(r['total']for r in rs if any(r['anchors'])),'three_run_positions':[61,73,89]}
receipt['total_proposal_attempts']=sum(x.get('proposals',0)for x in rows)
receipt['iteration_count_convention']='The proposals fields count attempted iteration slots, including inapplicable rotations; they are not counts of distinct grammars or certified candidates.'
(ROOT/'SUMMARY.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
