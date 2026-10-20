#!/usr/bin/env python3
"""Replay G's closed interderivations and the exact seed-bundle projections.

The G derivations are inherited unchanged. In addition to numerical cases,
this replay checks one schematic derivation using a,b,c and the syntactic
label builder ('kappa',a,b). Evaluation of that label builder at natural
values commutes with every formula/proof constructor, so this is a uniform
proof template, not an appeal to the numerical examples.

TAUT leaves abbreviate the retained rho8/rho6 classical bridge. This is an
ordinary syntactic certificate, not a Rocq or Lean kernel endpoint.
"""
from pathlib import Path
import argparse,hashlib,json
import merged_euclidean_helper_certificate as g
from combined_helper_certificate import I,N,taut,assumptions,export,read_export
NUMERIC_KAPPA=g.kappa

def schematic_kappa(a,b):
 if type(a) is int and type(b) is int:return NUMERIC_KAPPA(a,b)
 return 'kappa',a,b

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path,default=Path(__file__).with_name('seed_g_logic_receipt.json'))
 ap.add_argument('--proofs',type=Path,default=Path(__file__).with_name('seed_g_logic_proofs.json'))
 args=ap.parse_args()
 assert __debug__
 g.kappa=schematic_kappa
 roots={};summaries={}
 cases=[('a','b','c'),(0,0,0),(0,1,2),(1,0,0),(1,1,0),(3,999,1001)]
 for a,b,c in cases:
  for name,t in [('reflexivity',g.reflexivity(a)),('helper',g.ordinary_helper(a,b)),
       ('box_elimination',g.equality_box_elim(a,b)),('old_euclidean',g.euclidean(a,b,c)),
       ('reverse_G',g.merged_from_old(a,b,c))]:
   roots[f'{name}_{a}_{b}_{c}']=t
 # Exact abstract structure of the emitted seed bundles. C stands for the
 # complete quantified negated-core formula Q_c(H -> not W).
 RV=('opaque','RV');H=('opaque','H_eq');C=('opaque','negated_seed_core')
 old=N(I(RV,I(H,C)))
 new=N(I(RV,C))
 roots['seed_old_to_new']=taut(I(old,new))
 roots['seed_old_projects_helper']=taut(I(old,H))
 roots['seed_new_and_helper_to_old']=taut(I(new,I(H,old)))
 for name,t in roots.items():
  assert not assumptions(t)
  seen=set();counts={};g.check(t,seen,counts)
  if name.startswith(('reflexivity','helper','box_elimination','old_euclidean')):
   assert 'OLD_H' not in counts and 'OLD_RHO7' not in counts
  if name.startswith('reverse_G'):assert 'G' not in counts
  summaries[name]={'nodes':len(seen),'rules':counts}
 data=export(roots)
 data['scope']='Uniform closed G proof template plus numeric regressions and exact seed-bundle transformations. Symbolic kappa evaluates to4*P(a,b)+1; no freshness premise is used in these syntactic interderivations. TAUT abbreviates inherited rho8/rho6 proof bridge.'
 raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
 reloaded=read_export(json.loads(raw));seen=set();counts={}
 for name,t in reloaded.items():
  assert t.form==roots[name].form
  g.check(t,seen,counts)
 args.proofs.write_bytes(raw)
 result={'status':'SEED_G_UNIFORM_CLOSED_LOGIC_CERTIFICATE_PASS','proof_sha256':hashlib.sha256(raw).hexdigest(),
  'proof_nodes':len(data['proof_nodes']),'formula_count':len(data['formulas']),
  'schematic_label_assignments':1,'numerical_regression_assignments':5,'root_count':len(roots),
  'seed_bundle_old':old,'seed_bundle_new':new,'roots':summaries,'rules':counts,'scope':data['scope']}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('roots','seed_bundle_old','seed_bundle_new')},indent=2))
if __name__=='__main__':main()
