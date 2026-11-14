#!/usr/bin/env python3
"""Classify label-independent transition graphs, intentionally ignoring starts.

For a finite deterministic edge-labelled graph with a root reaching every
vertex, canonical breadth-first traversal from that root is complete. Taking
the least such traversal over all roots gives a root-free canonical form.
This does NOT assert equality of blank-start behavior.
"""
from pathlib import Path
import collections,json,sys
from census import parse_table,digest

def canonical(rows):
    states={q for q,b in rows};best=None;best_root=None
    for root in states:
        order=[root];ix={root:0};seq=[]
        for q in order:
            for b in (0,1):
                w,d,n=rows[q,b]
                if n in states and n not in ix:ix[n]=len(ix);order.append(n)
                seq.append((w,d,ix[n] if n in states else -1))
        if len(order)==len(states):
            enc=tuple(seq)
            if best is None or enc<best:best,best_root=enc,root
    if best is None:raise ValueError('no vertex reaches whole graph')
    return digest(json.dumps(best,separators=(',',':')).encode()),best_root

def main():
    d=Path(sys.argv[1]); tables=json.loads((d/'tables.json').read_text())
    groups=collections.defaultdict(list)
    for x in tables:groups[x['transition_sha256']].append(x)
    result=[];unclassified=[]
    for k,v in groups.items():
        data=(d/'tables_by_raw_hash'/(v[0]['raw_sha256']+'.tm')).read_bytes();meta,rows=parse_table(data)
        try:h,r=canonical(rows)
        except ValueError as e:
            unclassified.append({'transition_sha256':k,'working_states':meta['working_states'],'representative_raw_sha256':v[0]['raw_sha256'],'occurrences':len(v),'first_source':v[0]['source'],'first_member':v[0]['member'],'reason':str(e)})
            continue
        result.append({'transition_sha256':k,'root_free_graph_sha256':h,'canonicalizing_root_label':r,'working_states':meta['working_states'],'representative_raw_sha256':v[0]['raw_sha256'],'occurrences':len(v),'first_source':v[0]['source'],'first_member':v[0]['member']})
    (d/'root_free_graphs.json').write_text(json.dumps(result,indent=2)+'\n')
    (d/'root_free_unclassified.json').write_text(json.dumps(unclassified,indent=2)+'\n')
    unique={x['root_free_graph_sha256']:x for x in result}
    summary={'root_free_graph_classes_classified':len(unique),'classified_transition_tables':len(result),'unclassified_transition_tables':len(unclassified),'state_count_graph_histogram':dict(sorted(collections.Counter(x['working_states'] for x in unique.values()).items())),'scope':'Root-free action graphs for tables with a vertex reaching all controls, intentionally ignoring each designated initial state. Includes experiments and rejected tables. Graphs lacking such a vertex are listed separately, not incorrectly counted as independent graphs.'}
    (d/'root_free_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
