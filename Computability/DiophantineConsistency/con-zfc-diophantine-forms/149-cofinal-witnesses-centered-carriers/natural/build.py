#!/usr/bin/env python3
"""Compose shift-free descending factorials, positive Pell centers, pooled digits."""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, importlib.util, json, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'inherited/descending18'

def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
pc=module('natural_contractor',next((BASE/'portable').rglob('psd_contract/contract.py')))
checker=module('independent_checker',BASE/'check_natural.py')
def write(path,value):
 path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')

def transform(positive_center=True):
 parent=BASE/'source/equation.json';original=json.loads(parent.read_text());e=deepcopy(original)
 names={v['name']:i for i,v in enumerate(e['variables'])};v=names.__getitem__
 newrow=lambda label,terms:{'label':label,'terms':pc.dump(pc.loadpoly(terms))}
 replacement={};deleted=set()
 if positive_center:
  square=len(e['variables']);e['variables'].append({'name':'index_cap.auxiliary_trace_square','kind':'gate'})
  replacement[154]=[newrow('index_cap.auxiliary_trace_square',[[1,[square]],[-1,[v('index_cap.U'),v('index_cap.U')]]]),
   newrow('index_cap.positive_comparison_center',[[1,[v('mul.433')]],[-1,[v('shared.lower_A')]],[-1,[v('shared.A_slack')]],[1,[]],[-4,[v('index_cap.Y'),square]],[-1,[square]],[1,[v('shared.lower_A'),square]],[1,[v('shared.A_slack'),square]]])]
  replacement[163]=[newrow('index_cap.V_even_positive_multiple',[[1,[v('index_cap.V')]],[-2,[v('mul.440')]]])]
  deleted|={164,165}
 e['residuals']=[s for i,r in enumerate(e['residuals']) if i not in deleted for s in replacement.get(i,[r])]
 groups=[('t0',['choose0','crt.range.index'],'pow3.output'),('t',['crt.range.'+n for n in ('a','b','c','d','derived_label_sum')],'mul.418'),('y',['crt.range.S','crt.range.Sp'],'pow4.output'),('x',['crt.range.u','crt.range.vq'],'pow5.output')]
 replacement={};deleted={'choose0.digit_bound'}
 for label,requests,den in groups:
  slack=v(requests[0]+'.modular_rslack')
  replacement[requests[0]+'.remainder_bound']=newrow('pooled_digits.'+label,[[1,[v(den)]],[-1,[slack]],[-1,[]]]+[[-1,[v(req+'.modular_remainder')]] for req in requests])
  e['variables'][slack]['name']='pooled_digits.'+label+'.slack'
  deleted|={req+'.remainder_bound' for req in requests}
 e['residuals']=[replacement.get(r['label'],r) for r in e['residuals'] if r['label'] in replacement or r['label'] not in deleted]
 used=sorted({i for r in e['residuals'] for c,m in r['terms'] for i in m});rename={i:j for j,i in enumerate(used)}
 e['variables']=[e['variables'][i] for i in used]
 for r in e['residuals']:r['terms']=pc.dump(pc.loadpoly([[c,[rename[i] for i in m]] for c,m in r['terms']]))
 e['variant']='round19_descending_pooled'+('_positive_center' if positive_center else '')
 e['metrics'],expanded=pc.metrics_and_polynomial(e)
 cert={'schema':'round19_natural_composition_v1','parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),'positive_center':positive_center,'groups':groups,'retained_extended_parent_indices':used,'proof':'PROOF.md'}
 return e,expanded,cert

def build(output,positive_center=True):
 output=Path(output)
 if output.exists() and any(output.iterdir()):raise ValueError('output must be empty')
 e,exp,cert=transform(positive_center)
 for n,o in [('raw/equation.json',e),('raw/expanded_polynomial.json',exp),('raw/transformation.json',cert)]:write(output/n,o)
 import cofinal
 ce,cexp,ccert=cofinal.transform(e,pc)
 for n,o in [('equation.json',ce),('expanded_polynomial.json',cexp),('transformation.json',ccert)]:write(output/'cofinal_raw'/n,o)
 result={}
 fixed=module('fixed_natural_contractor',ROOT/'contract_fixed.py')
 for name,cap,source in [('projected221',32,e),('dimension219',24,ce),('cofinal221',32,ce)]:
  if name!='dimension219':engine=pc
  else:
   fixed.ROW_PRIORITY=tuple(json.loads((ROOT/name/'priority.json').read_text()))
   fixed.SOURCE_SHA256=hashlib.sha256(fixed.canonical(source)).hexdigest();engine=fixed
  target,certificate,polynomial=engine.contract(source,support_cap=cap)
  receipt,independent=checker.verify(source,target,certificate)
  if polynomial['terms']!=independent:raise ValueError('coefficient disagreement')
  for n,o in [('equation.json',target),('elimination_certificate.json',certificate),('expanded_polynomial.json',polynomial),('VERIFICATION.json',receipt)]:write(output/name/n,o)
  result[name]=receipt
 import apply_row_basis
 for name,origin in [('natural219','dimension219'),('sparse221','cofinal221'),('balanced221','projected221')]:
  original=json.loads((output/origin/'equation.json').read_text())
  operations=json.loads((ROOT/name/'operations.json').read_text())
  eq,poly=apply_row_basis.emit(original,operations)
  rc=json.loads((ROOT/name/'row_basis_certificate.json').read_text())
  rc['equation']=eq
  rc['source_sha256']=hashlib.sha256((output/origin/'equation.json').read_bytes()).hexdigest()
  rc['source_equation_sha256']=hashlib.sha256(fixed.canonical(original)).hexdigest()
  for file,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('row_basis_certificate.json',rc)]:write(output/name/file,obj)
 write(output/'SUMMARY.json',result);return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);p.add_argument('--no-positive-center',action='store_true');a=p.parse_args();print(json.dumps(build(a.output,not a.no_positive_center),indent=2))
