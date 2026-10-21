#!/usr/bin/env python3
"""Count soundly separable tree-walk subquery keys; no proof/compiler claim."""
import collections, contextlib, io, json, runpy, sys
from pathlib import Path
if not __debug__: raise SystemExit('Do not run with -O/-OO: assertions are required.')
ROOT=Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()): p=runpy.run_path(str(ROOT/'profile_forward_checks.py'))
nodes=p['nodes'];queries=p['site_queries']
raw=set();relative=set();relative_zero_trim=set();weighted=0
for (root,path),multiplicity in queries.items():
    t=root;d=0
    while True:
        suffix=path[d:]
        raw.add((t,suffix,d));relative.add((t,suffix))
        k=len(suffix)
        while k and suffix[k-1]==0:k-=1
        relative_zero_trim.add((t,suffix[:k]))
        weighted+=multiplicity
        if nodes[t][0]=='leaf':break
        t=nodes[t][1+(path[d] if d<len(path) else 0)];d+=1
out={'status':'STATIC_SUBQUERY_COUNT_NOT_LEAN_PROOF',
 'commit':p['out']['commit'],'source_sha256':p['out']['source_sha256'],
 'twalk_recursive_calls_including_leaves':weighted,
 'unique_exact_subtree_remaining_path_depth_keys':len(raw),
 'unique_subtree_remaining_path_keys_relative_depth':len(relative),
 'unique_subtree_remaining_path_trailing_zeros_removed':len(relative_zero_trim),
 'unique_syntax_nodes_across_both_trees':len(nodes),
 'requirements':[
   'Relative-depth walk needs a generic accumulator-shift lemma before reuse.',
   'Trailing-zero canonicalization additionally needs equal implicit-bitstream/tsite-consumption lemmas.',
   'Exact endpoint paths remain distinct in the current certificate relation.',
   'A materialized shared DAG plus checked memo dependencies is needed to realize counts; Lean will not automatically memoize these reductions.'
 ]}
(ROOT/'walker_sharing_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
