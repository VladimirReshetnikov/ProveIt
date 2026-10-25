#!/usr/bin/env python3
"""Independent name-level audit of the complete raw semantic composition.

No constructor or contractor imports. This checks finite source edits, not the
unbounded center/factorial/CRT theorem supplied in PROOF.md.
"""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
import json
ROOT=Path(__file__).resolve().parent
PARENT_SHA='2b4b3088a6e4433dad4742ba53fe233f48e3bf83026b940ebc7ab820b338d7c6'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def named(record,variables):
 total={}
 for c,m in record['terms']:
  require(type(c)is int,'nonintegral coefficient')
  mon=tuple(sorted(variables[i]['name'] for i in m));total[mon]=total.get(mon,0)+c
 return {m:c for m,c in total.items() if c}
def poly(terms):
 out={}
 for c,m in terms:
  k=tuple(sorted(m));out[k]=out.get(k,0)+c
 return {m:c for m,c in out.items() if c}
def expected_rows(parent):
 vs=parent['variables'];rows=[]
 for i,r in enumerate(parent['residuals']):
  lab=r['label'];p=named(r,vs)
  if i in (164,165) or lab=='choose0.digit_bound' or lab.endswith('.remainder_bound') and lab!='fact0.remainder_bound':continue
  if i==154:
   rows.append(('index_cap.auxiliary_trace_square',poly([(1,['index_cap.auxiliary_trace_square']),(-1,['index_cap.U','index_cap.U'])])))
   rows.append(('index_cap.positive_comparison_center',poly([(1,['mul.433']),(-1,['shared.lower_A']),(-1,['shared.A_slack']),(1,[]),(-4,['index_cap.Y','index_cap.auxiliary_trace_square']),(-1,['index_cap.auxiliary_trace_square']),(1,['shared.lower_A','index_cap.auxiliary_trace_square']),(1,['shared.A_slack','index_cap.auxiliary_trace_square'])])))
  elif i==163:
   rows.append(('index_cap.V_even_positive_multiple',poly([(1,['index_cap.V']),(-2,['mul.440'])])))
  else:rows.append((lab,p))
 # Independent expected insertion at the first old bound in each group.
 groups=[('t0',['choose0','crt.range.index'],'pow3.output'),('t',['crt.range.'+n for n in ('a','b','c','d','derived_label_sum')],'mul.418'),('y',['crt.range.S','crt.range.Sp'],'pow4.output'),('x',['crt.range.u','crt.range.vq'],'pow5.output')]
 for g,requests,den in groups:
  label=requests[0]+'.modular_digit'
  index=next(i for i,(lab,p) in enumerate(rows) if lab==label)+1
  rows.insert(index,('pooled_digits.'+g,poly([(1,[den]),(-1,[]),(-1,['pooled_digits.'+g+'.slack'])]+[(-1,[r+'.modular_remainder']) for r in requests])))
 return rows,groups

def verify(parent,source,certificate):
 require(source['domain']==parent['domain']=='nonnegative integers','domain widened')
 require(sha256((ROOT/'inherited/descending18/source/equation.json').read_bytes()).hexdigest()==PARENT_SHA,'parent bytes')
 require(parent==json.loads((ROOT/'inherited/descending18/source/equation.json').read_text()),'parent object binding')
 require(certificate['parent_sha256']==PARENT_SHA,'parent binding')
 require(certificate['schema']=='round19_natural_composition_v1' and certificate['positive_center'] is True,'delta mode')
 expected,groups=expected_rows(parent)
 require(certificate['groups']==[[a,b,c] for a,b,c in groups],'denominator groups')
 actual=[(r['label'],named(r,source['variables'])) for r in source['residuals']]
 require(actual==expected,'literal semantic rows differ')
 ext=deepcopy(parent['variables'])+[{'name':'index_cap.auxiliary_trace_square','kind':'gate'}]
 for g,requests,den in groups:
  i=next(i for i,v in enumerate(ext) if v['name']==requests[0]+'.modular_rslack');ext[i]['name']='pooled_digits.'+g+'.slack'
 used={n for lab,p in expected for m in p for n in m}
 indices=[i for i,v in enumerate(ext) if v['name'] in used]
 require(source['variables']==[ext[i] for i in indices],'coordinate map')
 require(certificate['retained_extended_parent_indices']==indices,'coordinate index certificate')
 require(all(len(m)<=2 for lab,p in expected for m in p),'lost quadratic degree')
 terms={}
 for lab,p in expected:
  for m,c in p.items():
   for n,d in p.items():
    k=tuple(sorted(m+n));terms[k]=terms.get(k,0)+c*d
 terms={m:c for m,c in terms.items() if c}
 met={'variables':len(indices),'quadratic_rows':len(expected),'exact_degree':max(map(len,terms)),'expanded_monomials':len(terms),'max_abs_expanded_coefficient':max(map(abs,terms.values())),'max_abs_row_coefficient':max(abs(c) for lab,p in expected for c in p.values())}
 require(source['metrics']==met,'raw metrics')
 names={v['name']:i for i,v in enumerate(source['variables'])}
 expanded=sorted([[c,sorted(names[n] for n in m)] for m,c in terms.items()],key=lambda cm:tuple(cm[1]))
 return {'verified':True,**met,'new_raw_variables':1,'removed_raw_variables':11,'removed_private_low_slacks':7,'removed_output_slacks':1,'center_parent_witnesses_removed':3},expanded

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def verify_cofinal(source,target,certificate):
 require(source['domain']==target['domain']=='nonnegative integers','cofinal domain')
 require(certificate['schema']=='even_descending_cofinal_beta_v1','cofinal schema')
 require(certificate['source_sha256']==sha256(canonical(source)).hexdigest(),'cofinal source hash')
 require(certificate['target_sha256']==sha256(canonical(target)).hexdigest(),'cofinal target hash')
 require(certificate['old_t0_equals']==[2,-8] and certificate['new_horizon']=='t=2*t0+4','cofinal horizon')
 expected=[]
 for r in source['residuals']:
  p=named(r,source['variables']);out={}
  for mon,c in p.items():
   products=[(c,())]
   for n in mon:
    factor=[(2,('t0',)),(-8,())] if n=='t0' else [(1,(n,))]
    products=[(a*b,tuple(sorted(m+k))) for a,m in products for b,k in factor]
   for a,m in products:out[m]=out.get(m,0)+a
  out={m:c for m,c in out.items() if c}
  if r['label']=='endpoint.first_remainder':expected.append(('endpoint.cofinal_beta_bound',{('y',):1,():1,('pow0.output',):-1}))
  else:expected.append((r['label'],out))
 actual=[(r['label'],named(r,target['variables'])) for r in target['residuals']]
 require(actual==expected,'cofinal translated rows')
 oldnames=[v['name'] for v in source['variables']];deleted=oldnames.index('endpoint.r0');retained=[i for i in range(len(oldnames)) if i!=deleted]
 require(target['variables']==[source['variables'][i] for i in retained],'cofinal variables')
 require(certificate['deleted_original_variable_index']==deleted and certificate['retained_original_indices']==retained,'cofinal restoration map')
 require(certificate['replaced_row']=='endpoint.first_remainder' and certificate['new_row']=='y+1=V','cofinal endpoint binding')
 result={}
 for lab,p in expected:
  for m,c in p.items():
   for n,d in p.items():
    key=tuple(sorted(m+n));result[key]=result.get(key,0)+c*d
 result={m:c for m,c in result.items() if c}
 met={'variables':len(retained),'quadratic_rows':len(expected),'exact_degree':max(map(len,result)),'expanded_monomials':len(result),'max_abs_expanded_coefficient':max(map(abs,result.values())),'max_abs_row_coefficient':max(abs(c) for lab,p in expected for c in p.values())}
 require(target['metrics']==met,'cofinal metrics')
 names={v['name']:i for i,v in enumerate(target['variables'])}
 expanded=sorted([[c,sorted(names[n] for n in m)] for m,c in result.items()],key=lambda cm:tuple(cm[1]))
 return {'verified':True,**met,'domain_theorem':'ordinary, in COFINAL_PROOF.md; not an unrestricted translation bijection'},expanded
