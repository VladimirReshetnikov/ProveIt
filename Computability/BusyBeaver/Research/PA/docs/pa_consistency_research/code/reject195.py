#!/usr/bin/env python3
"""Reproduce one complete-tape counterexample to the rejected 195-state layout."""
import json,sys
from pathlib import Path
from verify import ROOT,require
from check_concrete import frame,expectation,run
sys.path.insert(0,str(Path(__file__).resolve().parent/'runtime'))
import independent_runtime as r,source_language as s
sites=json.loads((ROOT/'data/rejected195_source.json').read_text());site=sites[1003]
expected=expectation(site,[0]*9,[0],48)
result=run(r.table(ROOT/'data/rejected195.native.tm'),frame(site[0],[0]*9,[0],48),expected,s.tree(sites),48,10000)
require(result['status']=='OTHER_CLEAN_ROOT'and result['steps']==276,'Expected counterexample did not reproduce')
require(result['actual']['gap']==49 and result['actual']['spares']==[0,1],'Wrong counterexample tape')
require(result['actual']!=expected,'No mismatch')
values=[0]*9;values[1]=1
expected_positive=expectation(site,values,[0],48)
positive=run(r.table(ROOT/'data/rejected195.native.tm'),frame(site[0],values,[0],48),expected_positive,s.tree(sites),48,10000)
require(positive['status']=='OTHER_CLEAN_ROOT'and positive['steps']==278,'Positive counterexample did not reproduce')
require(positive['actual']['registers'][1]==1 and expected_positive['registers'][1]==0,'Positive logical effect mismatch')
print(json.dumps(dict(status='REJECTED195_COUNTEREXAMPLE_PASS',source_site=1003,source_instruction=site,expected=expected,actual=result['actual'],steps=result['steps'],root_visits=result['root_visits'],positive_case=dict(initial_registers=values,expected=expected_positive,actual=positive['actual'],steps=positive['steps']),scope='Refutes the intended first-return source-frame contract; does not decide the candidate blank-tape halting sentence.'),indent=2))
