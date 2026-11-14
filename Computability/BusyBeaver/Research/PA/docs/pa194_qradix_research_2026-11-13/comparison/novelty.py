#!/usr/bin/env python3
"""Exact graph comparison against every current explicitly encoded 194-state class.

This rejects cosmetic rediscoveries under any spanning start, arbitrary state
renaming, reflection, global bit complementation, or both. It does not claim
semantic inequivalence or prove a consistency calibration.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('literal',HERE/'literal_inventory.py')
lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)

def canon(data):
 forms=[c for flip in (False,True) for comp in (False,True) for q in sorted(data[1])
         if (c:=lib.canonical(data,q,flip,comp)) is not None]
 if not forms:raise ValueError('No spanning root: this comparator needs whole spanning action graphs')
 # A final write and move have no effect on whether the machine halts.
 forms=[tuple(tuple((0,'H',-1) if a[2]==-1 else a for a in row) for row in form) for form in forms]
 return min(forms)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidate',type=Path)
 ap.add_argument('--output',type=Path);args=ap.parse_args()
 b=args.candidate.read_bytes();data=lib.parse_table(b)
 if data is None:raise ValueError('Not a complete one-halt binary L/R numeric table')
 target=canon(data);frontier=json.loads((HERE/'frontier194.json').read_text())
 matches=[];controls=[]
 for i,x in enumerate(frontier['classes']):
  p=HERE/x['representative_file'];bb=p.read_bytes()
  assert hashlib.sha256(bb).hexdigest()==x['representative_sha256'],p
  dd=lib.parse_table(bb);assert dd is not None and len(dd[1])==194
  form=canon(dd)
  if form==target:matches.append({'name':x['name'],'source':x['source'],'status':x['status']})
  if i==0:
   # A root-preserving relabeling, reflection and bit swap must compare equal.
   rows,states,halt=dd;mapping={s:10000+7*j for j,s in enumerate(sorted(states))};hh=20000
   transformed={(mapping[q],bit^1):(w^1,'R' if d=='L' else 'L',mapping[t] if t in states else hh)
                for (q,bit),(w,d,t) in rows.items()}
   assert canon((transformed,set(mapping.values()),hh))==form
   controls.append('Exact recovery of a relabeled, reflected and bit-complemented prior table')
 result={'snapshot':frontier['snapshot'],'candidate':args.candidate.name,'candidate_sha256':hashlib.sha256(b).hexdigest(),
  'states':len(data[1]),'prior_194_classes_checked':len(frontier['classes']),'matches':matches,'novel_under_stated_graph_equivalences':not matches,
  'equivalences_allowed':['arbitrary state renaming','any spanning root','global tape reflection','global bit complementation','ignoring the final write and move on halting transitions'],
  'comparison':'Full canonical tuples compared exactly; hashes are identifiers only.','canonical_tuple_sha256':hashlib.sha256(repr(target).encode()).hexdigest(),
  'positive_control':controls,'limitations':'Graph novelty only. Includes all 39 text-table frontier classes and the JSON-only PA194N_AD. Does not enumerate unmaterialized source generators.'}
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
