#!/usr/bin/env python3
"""Verify exact source certificates; standard library, no search required."""
from pathlib import Path
import hashlib,json,sys
import source_language as s
HERE=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise ValueError(message)
def digest(raw):return hashlib.sha256(raw).hexdigest()

def main():
    need(__debug__ and not sys.flags.optimize,'Run with Python assertions enabled')
    # Delivery-manifest replay omitted by intake policy; selected inputs are pinned in the replay plan.
    baseline=json.loads((HERE/'data/dominated203.json').read_text())
    old=s.tree(baseline);oldgraph,oldchecks=s.graph_arithmetic(baseline)
    need(oldgraph==s.graph_intervals(baseline),'Baseline CFG resolvers disagree')
    need(s.metrics(old)==dict(dag_nodes=203,leaf_occurrences=4751,maximum_depth=45,maximum_zero_run=6),'Baseline metrics')
    word=[row[1:]for row in baseline];records=[]
    for name in ['seed205.json','zero5_walk206.json']+[f'zero5_dp{i}.json'for i in range(4)]:
        raw=(HERE/'data'/name).read_bytes();rows=json.loads(raw);tree=s.tree(rows);met=s.metrics(tree)
        graph,checks=s.graph_arithmetic(rows)
        need(graph==s.graph_intervals(rows)==oldgraph,('Exact guarded CFG differs',name))
        need([row[1:]for row in rows]==word,('Primitive word differs',name))
        need(rows[:37]==baseline[:37],('Initializer addresses differ',name))
        if name=='seed205.json':need(met['dag_nodes']==205 and met['maximum_zero_run']==6,('Seed metrics',met))
        else:need(met['dag_nodes']==206 and met['maximum_zero_run']==5,('Five-zero metrics',met))
        need(met['leaf_occurrences']==4751,('Leaf count',name))
        records.append(dict(file='data/'+name,sha256=digest(raw),metrics=met,primitive_word_equal=True,guarded_CFG_equal=True,two_CFG_resolvers_agree=True,initializer37_equal=True,no_stray_suffix_checks=checks))
    result=dict(status='EXACT_SOURCE_RECODING_CERTIFICATES_PASS',baseline_sha256=digest((HERE/'data/dominated203.json').read_bytes()),baseline_metrics=s.metrics(old),graph_sha256=digest(s.compact(oldgraph)),primitive_word_sha256=digest(s.compact(word)),records=records,scope='Exact source semantics for all natural register vectors. No physical allocation, quantified binary runtime, or blank-start proof is claimed by this checker.')
    (HERE/'receipts/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
