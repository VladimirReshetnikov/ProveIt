#!/usr/bin/env python3
"""Exact shared-square recircuiting and natural pooled q-power construction."""
from copy import deepcopy
from pathlib import Path
import argparse, json, hashlib
ROOT=Path(__file__).resolve().parent

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):return json.loads(p.read_text())
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def poly(ts):return {tuple(m):c for c,m in ts}
def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
 o={}
 for p in ps:
  for m,c in p.items():o[m]=o.get(m,0)+c
 return {m:c for m,c in o.items() if c}
def scale(c,p):return {m:c*a for m,a in p.items() if c*a}
def mul(p,q):
 o={}
 for m,c in p.items():
  for n,d in q.items():
   k=tuple(sorted(m+n));o[k]=o.get(k,0)+c*d
 return {m:c for m,c in o.items() if c}
def subst(p,mapping):
 out={}
 for mon,c in p.items():
  term={():c}
  for v in mon:term=mul(term,mapping.get(v,{(v,):1}))
  out=add(out,term)
 return out

def pack(e):
 used=sorted({v for r in e['residuals'] for c,m in r['terms'] for v in m}); ren={v:i for i,v in enumerate(used)}
 e['variables']=[e['variables'][i] for i in used]
 for r in e['residuals']:r['terms']=dump({tuple(ren[v] for v in m):c for c,m in r['terms']})
 return e,used

def finish(e):
 total={}
 for r in e['residuals']:total=add(total,mul(poly(r['terms']),poly(r['terms'])))
 e['metrics']={'variables':len(e['variables']),'quadratic_rows':len(e['residuals']),'exact_degree':max(map(len,total)),'expanded_monomials':len(total),'max_abs_expanded_coefficient':max(map(abs,total.values())),'max_abs_row_coefficient':max(abs(c) for r in e['residuals'] for c,m in r['terms'])}
 return {'schema':'sparse_integer_polynomial_v1','domain':e['domain'],'variables':len(e['variables']),'terms':dump(total)}

def sharing(source,alpha=26,beta=42):
 e=deepcopy(source); ns={x['name']:i for i,x in enumerate(e['variables'])}
 def a(n):return {(ns[n],):1}
 L=add(scale(2,a('crt.encoded.b')),a('mul.36'))
 h=a('mul.143'); mapping={
 ns['mul.43']:add(h,scale(34-alpha,L),{():72-beta}),
 ns['mul.143']:add(h,scale(30-alpha,L),{():56-beta}),
 ns['mul.370']:add(a('mul.366'),scale(2,a('fact0.output')))}
 third='mul.166' if 'mul.166' in ns else 'add.171'
 mapping[ns[third]]=add(scale(4,h),scale(100-4*alpha,L),{():156-4*beta}) if third=='mul.166' else add(scale(8,h),scale(208-8*alpha,L),scale(4,a('crt.encoded.b')),scale(2,a('mul.60')),{():349-8*beta})
 e['variables'][ns['mul.143']]={'name':'syntax.shared_shifted_square','kind':'shared nonnegative shifted square'}
 # Locate defining rows by the parent original coordinates and exact monic pivot.
 def defining(n):
  j=ns[n]
  rows=[i for i,r in enumerate(source['residuals']) if poly(r['terms']).get((j,))==1 and r['label'] in ('multiplication','addition')]
  if len(rows)!=1:raise ValueError((n,rows))
  return rows[0]
 r43,r143,r166,r370,r366=[defining(n) for n in ('mul.43','mul.143',third,'mul.370','mul.366')]
 images=[subst(poly(r['terms']),mapping) for r in source['residuals']]
 core=add(h,scale(-4,mul(L,L)),scale(-alpha,L),{():-beta})
 for i,c in ((r43,1),(r143,1),(r166,4 if third=='mul.166' else 8)):
  if images[i]!=scale(c,core):raise ValueError('shared square identity')
 if images[r370]!=images[r366]:raise ValueError('shared factorial multiple identity')
 deleted={r143,r166,r370}; records=[]; forward=[]
 for i,r in enumerate(source['residuals']):
  if i in deleted:continue
  p=core if i==r43 else images[i]
  records.append({'label':'syntax.shared_square_definition' if i==r43 else r['label'],'terms':dump(p)})
  forward.append(i)
 e['residuals']=records;e['variant']='round21_shared_syntax_square'; e,used=pack(e); expanded=finish(e)
 cert={'schema':'shared_nonnegative_square_recircuited_v1','parent_sha256':hashlib.sha256(canonical(source)).hexdigest(),'affine_parent_restorations':{str(v):dump(p) for v,p in mapping.items()},'shared_square_original_index':ns['mul.143'],'shared_square_form':dump(L),'alpha':alpha,'beta':beta,'deleted_parent_rows':sorted(deleted),'target_parent_row_ids':forward,'parent_square_rows':[[r43,1],[r143,1],[r166,4 if third=='mul.166' else 8]],'duplicate_parent_rows':[r366,r370],'retained_extended_indices':used,'target_sha256':hashlib.sha256(canonical(e)).hexdigest()}
 return e,expanded,cert

def pooling(source):
 e=deepcopy(source); ns={x['name']:i for i,x in enumerate(e['variables'])}
 def a(n):return {(ns[n],):1}
 A=add(a('shared.lower_A'),a('shared.A_slack')); n=a('pow2.output')
 z=ns['shared.Zminus1']; mapping={z:add(scale(2,{(z,):1}),{():1})}
 # The contracted denominator outputs are the exact pooled-remainder sums.
 blocks=[('index0.Y','index0.previous_Y',['choose0.modular_remainder','pooled_digits.t0.slack','crt.range.index.modular_remainder']),('index2.Y','index2.previous_Y',['crt.range.S.modular_remainder','pooled_digits.y.slack','crt.range.Sp.modular_remainder']),('index1.Y','index1.previous_Y',['crt.range.u.modular_remainder','pooled_digits.x.slack','crt.range.vq.modular_remainder'])]
 request=[]
 for yn,zn,mn in blocks:
  request.append((a(yn),a(zn),add({():1},*[a(s) for s in mn])))
 gone={'base3.T','pow3.quotient','pow4.quotient','pow5.quotient'}; goneids={ns[s] for s in gone}
 deleted=[i for i,r in enumerate(source['residuals']) if any(v in goneids for c,m in r['terms'] for v in m)]
 if len(deleted)!=4:raise ValueError(('pooled removed rows',deleted))
 rows=[{'label':r['label'],'terms':dump(subst(poly(r['terms']),mapping))} for i,r in enumerate(source['residuals']) if i not in deleted]
 fresh=[]
 for name in ('U','M','K'):
  idx=len(e['variables']);e['variables'].append({'name':'pooled_power.'+name,'kind':'natural pooled power witness'});fresh.append({(idx,):1})
 U,M,K=fresh
 Y2=add(*[mul(Y,Y) for Y,Z,m in request]); D2=add(*[mul(add(m,Z),add(m,Z)) for Y,Z,m in request]); H=add(*[mul(Y,add(m,Z)) for Y,Z,m in request])
 ps=[add(U,scale(-1,Y2)),add(K,scale(-2,H),scale(-1,mul(add(scale(2,A),scale(-1,n)),M)),mul(n,U)),add(D2,M,scale(-1,mul(n,K)))]
 for label,p in zip(('sum_Y_squares','pooled_quotient_linearization','sum_power_errors'),ps):rows.append({'label':'pooled_power.'+label,'terms':dump(p)})
 e['residuals']=rows;e['variant']='round21_natural_three_coordinate_pooled_q_powers';e,used=pack(e);expanded=finish(e)
 cert={'schema':'natural_pooled_q_powers_v1','parent_sha256':hashlib.sha256(canonical(source)).hexdigest(),'deleted_parent_rows':deleted,'deleted_parent_variables':sorted(gone),'frame_substitution':{'variable_original_index':z,'old_value':'2*new_value+1'},'block_names':blocks,'retained_extended_indices':used,'target_sha256':hashlib.sha256(canonical(e)).hexdigest()}
 return e,expanded,cert

def main(output):
 summary={}
 for origin,label in [('dimension206','dimension203'),('projected207','projected204'),('projected208','projected205')]:
  source=read(ROOT/'inherited'/origin/'equation.json');e,p,c=sharing(source)
  for name,obj in [('equation.json',e),('expanded_polynomial.json',p),('sharing_certificate.json',c)]:write(output/label/name,obj)
  summary[label]=e['metrics']
  newlabel={'dimension203':'pooled202','projected204':'pooled203','projected205':'pooled204'}[label]
  e,p,c=pooling(e)
  for name,obj in [('equation.json',e),('expanded_polynomial.json',p),('pooling_certificate.json',c)]:write(output/newlabel/name,obj)
  summary[newlabel]=e['metrics']
 import importlib.util
 spec=importlib.util.spec_from_file_location('row_emitter',ROOT/'apply_row_basis.py');emitter=importlib.util.module_from_spec(spec);spec.loader.exec_module(emitter)
 for name,origin in [('natural202','pooled202'),('natural202_lowheight','pooled202'),('natural203','pooled203'),('natural204','pooled204')]:
  operations=read(ROOT/name/'operations.json');source=read(output/origin/'equation.json');e,p=emitter.emit(source,operations);mm=e['metrics']
  met=dict(variables=mm['variables'],rows=mm['quadratic_rows'],terms=mm['expanded_monomials'],height=mm['max_abs_expanded_coefficient'],row_height=mm['max_abs_row_coefficient'],row_support=sum(len(r['terms'])for r in e['residuals']))
  cert=dict(equation=e,metrics=met,operations=operations,source='../'+origin+'/equation.json')
  for file,obj in [('equation.json',e),('expanded_polynomial.json',p),('operations.json',operations),('row_basis_certificate.json',cert)]:write(output/name/file,obj)
  summary[name]=mm
 write(output/'SUMMARY.json',summary)
 print(json.dumps(summary,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);main(ap.parse_args().output)
