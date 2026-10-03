#!/usr/bin/env python3
"""Literal two-resettable-place variant. No huge microtrace is enumerated."""
from pathlib import Path
import json,sys
from collections import Counter
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R.parent))
from build_net import compile_net,ledger
from source_quadratic import semantic_table
from peak_quadratic import compile_peak
from reset_quadratic import compile_schema
p=json.loads((R/'source/literal2.json').read_text());n=compile_net(p,initial_affine={'A':{'raw_A':1},'budget':{'raw_A':1},'q:START':{'constant':1}},parameters=['raw_A'])
n['theorem_input_domain']='Positive raw_A; the actual zero-input source is a nonhalting two-instruction loop.'
counts=ledger(n);assert (counts['places'],counts['transitions'],counts['ordinary_arcs'],counts['reset_arcs'],counts['distinct_reset_places'])==(8417,10756,38336,2340,2)
assert Counter(r[0] for r in p['rows'].values())=={'ADD':6068,'SUB':2340}
table=semantic_table(p);peak=compile_peak(table,1,initial=['raw_A',0]);trace=compile_schema(n,1,project_controls=True)
assert peak['ledger']=={'natural_witnesses':29906,'affine_squares':7,'quadratic_products':10749,'degree_at_most':2}
assert trace['ledger']=={'natural_witnesses':53780,'affine_squares':11,'quadratic_products':10756,'degree_at_most':2}
for name,obj in [('reset_net.json',n),('net_ledger.json',counts),('canonical_peak_schema_h1.json',peak),('projected_trace_schema_T1.json',trace)]:
 (R/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'net':counts,'canonical_peak_h1':peak['ledger'],'projected_trace_T1':trace['ledger']},indent=2))
