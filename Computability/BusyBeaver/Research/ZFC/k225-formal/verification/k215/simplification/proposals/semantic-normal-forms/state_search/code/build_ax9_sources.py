#!/usr/bin/env python3
"""Exact closed source surgery and independent full-control comparisons.

AX9clear: clear incoming top instead of pushing it.
AX9additive: omit that push; generalization binder gains incoming top.
AX9topbinder: also omit the D copy; completeness requires an extra bridge.
No binary-runtime or ZFC-calibration claim is made by this finite source tool.
"""
from pathlib import Path
import argparse,json,hashlib
import source_language as s
import source_splice as sp


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 raw=a.source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 a.output.mkdir(parents=True,exist_ok=True)
 oldrows=json.loads(raw);old=s.tree(oldrows);oldg=s.graph_intervals(oldrows)
 assert oldg==s.graph_arithmetic(oldrows)[0]
 variants=[('ax9clear',26,45,(('CD',1),('CC',1))),('ax9additive',26,45,None),('ax9topbinder',26,52,None)]
 report={'source_sha256':hashlib.sha256(raw).hexdigest(),'baseline':s.metrics(old),'variants':[]}
 for name,lo,hi,replace in variants:
  new=sp.apply_closed_splices(old,{(lo,hi):replace});rows=s.sites(new)
  graph=s.graph_intervals(rows);assert graph==s.graph_arithmetic(rows)[0]
  size=0 if replace is None else sp.size(replace)
  delta=hi-lo-size
  def image(i):
   if i<lo:return i
   if i>=hi:return i-delta
   assert i==lo, ('Outside edge enters deleted block interior',i)
   return lo
  checked=0
  for i,r in enumerate(oldrows):
   if lo<=i<hi:continue
   j=image(i)
   assert rows[j][1:]==r[1:]
   effect,targets=oldg[i]
   assert graph[j]==[effect,[image(x) for x in targets]]
   checked+=len(targets)
  # A removed or inserted closed block has no external control escapes.
  assert all(s.boundary(x)==(0,0,False) for x in sp.closed_forest(old,lo,hi))
  if replace is not None:assert s.boundary(replace)==(0,0,False)
  data=s.compact(rows);(a.output/(name+'.json')).write_bytes(data)
  report['variants'].append({'name':name,'removed_ordinal_interval':[lo,hi],
   'replacement_leaves':size,'source_sha256':hashlib.sha256(data).hexdigest(),
   'metrics':s.metrics(new),'retained_guarded_edges_checked':checked,
   'independent_new_cfg_resolvers_agree':True,
   'scope':'Exact source surgery and external-control binding, not semantic calibration or binary verification.'})
 (a.output/'source-construction.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
