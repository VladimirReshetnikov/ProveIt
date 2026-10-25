#!/usr/bin/env python3
"""Independent source-to-horizon-equation replay; no producer imports.

Uses only this contribution's independently written sparse ring routines.
The inherited Horn factorization's ordinary correctness proof is retained;
its exact certified local rewrite is checked and applied to the new source.
"""
import argparse,copy,hashlib,json,zipfile
from pathlib import Path
from verify_projection import read_terms,plus,times,substitute

PREFIX='ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/'
def must(c,msg):
 if not c:raise ValueError(msg)
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def polynomials(d):return [read_terms(r['terms']) for r in d['residuals']]
def replace(rows,i,value,n):
 images=[value if k==i else {(k,):1} for k in range(n)]
 return [substitute(p,images) for p in rows]
def solve(p,i):
 c=p.get((i,));must(c in (-1,1),'nonunit monic coefficient')
 must(not any(i in m for m in p if m!=(i,)),'nonlinear monic coordinate')
 return {m:-c*v for m,v in p.items() if m!=(i,)}
def equal(a,b,msg):
 must(a['domain']==b['domain']=='unrestricted integers',msg+': integer domain')
 must(a['variables']==b['variables'],msg+': coordinates')
 must([r['label'] for r in a['residuals']]==[r['label'] for r in b['residuals']],msg+': labels')
 must(polynomials(a)==polynomials(b),msg+': polynomials')
def with_rows(d,p):
 out=copy.deepcopy(d)
 must(len(p)==len(out['residuals']),'row census')
 for r,s in zip(out['residuals'],p):r['terms']=terms(s)
 return out
def shrink(d,rows,keepv,keepr):
 must(keepv==sorted(set(keepv)) and keepr==sorted(set(keepr)),'noncanonical retention')
 ren={i:j for j,i in enumerate(keepv)}
 must(all(i in ren for k in keepr for m in rows[k] for i in m),'deleted live coordinate')
 out=copy.deepcopy(d);out['variables']=[copy.deepcopy(d['variables'][i]) for i in keepv]
 out['residuals']=[dict(d['residuals'][j],terms=terms({tuple(ren[i] for i in m):c for m,c in rows[j].items()})) for j in keepr]
 return out
def quadratic(rows):must(all(len(m)<=2 for p in rows for m in p),'nonquadratic intermediate')

def raw_mutation(original,recorded):
 out=copy.deepcopy(original);n={v['name']:i for i,v in enumerate(out['variables'])}
 q,z,s,v,t,d,h=[n[k] for k in ['pow2.output','radix.odd_square_root_half','beta.odd_square_multiplier','beta.odd_square_root_half','t0','growth.power_base','cofinal.horizon_root']]
 rules={
 'radix.odd_square':({():-1,(q,):1,(z,):-4,(z,z):-4},{():-1,(q,):1,(z,):-4}),
 'beta.odd_square_multiplier':({():-1,(s,):1,(v,):-4,(v,v):-4},{():-1,(s,):1,(v,):-2}),
 'growth.base_definition':({(d,):1,(t,):-2,():-34},{(d,):1,(t,):-(1<<27),():-33*(1<<26)}),
 'cofinal.horizon':({(t,):1,(h,h):-1},{})}
 seen=set()
 for r in out['residuals']:
  if r['label'] in rules:
   label=r['label'];must(label not in seen,'duplicate semantic row');seen.add(label)
   before,after=rules[label];must(read_terms(r['terms'])==before,'original semantic pattern')
   r['terms']=terms(after)
 must(seen==set(rules),'missing semantic row')
 equal(out,recorded,'four exact raw mutations')
 return out

def horn_rewrite(raw,template,certificate):
 rows=polynomials(raw)
 changed=set()
 for step in certificate['changes']:
  i=step['row'];must(i not in changed,'repeated Horn mutation');changed.add(i)
  must(rows[i]==read_terms(step['old']),'Horn inherited source pattern')
  rows[i]=read_terms(step['new'])
 removed=certificate['deleted_rows'];must(len(set(removed))==len(removed),'duplicate deleted Horn row')
 result=[p for i,p in enumerate(rows) if i not in set(removed)]+[read_terms(certificate['new_row'])]
 must(len(template['variables'])==len(raw['variables'])+1,'Horn new gate census')
 for i,(before,after) in enumerate(zip(raw['variables'],template['variables'])):
  must(before['name']==after['name'],'Horn source coordinate name')
  if before!=after:
   must(i in certificate['square_variables'] and before['kind']=='square_difference' and after['kind']=='gate','Horn source coordinate kind')
 return with_rows(template,result)

def monic_projection(source,cert):
 rows=polynomials(source);n=len(source['variables']);deleted=set();eliminated=set()
 for step in cert['steps']:
  r,i=step['row_id'],step['variable'];must(r not in deleted and i not in eliminated,'reused projection pivot')
  value=solve(rows[r],i);must(value==read_terms(step['restoration']),'monic restoration')
  must(max(map(len,value),default=0)==step['restoration_degree'],'restoration degree')
  rows=replace(rows,i,value,n);must(not rows[r],'nonzero eliminated row');quadratic(rows)
  deleted.add(r);eliminated.add(i)
 keepv=cert['retained_original_variables'];keepr=cert['retained_original_rows'];unused=set(cert['unconstrained_removed'])
 must(keepr==[i for i in range(len(rows)) if i not in deleted],'retained monic rows')
 must(not (set(keepv)&eliminated or set(keepv)&unused or eliminated&unused),'variable partition overlap')
 must(set(keepv)|eliminated|unused==set(range(n)),'variable partition missing')
 must(not any(i in unused for j in keepr for m in rows[j] for i in m),'unconstrained deletion not free')
 return shrink(source,rows,keepv,keepr)

def translate(source,cert):
 must(cert['convention']=='old=new+shift','translation convention')
 rows=polynomials(source);n=len(source['variables']);seen=set()
 for i,c in cert['shifts']:
  must(type(c) is int and i not in seen,'translation data');seen.add(i)
  rows=replace(rows,i,{(i,):1,():c},n)
 return with_rows(source,rows)

def affine(source,cert):
 rows=polynomials(source);n=len(source['variables']);names={v['name']:i for i,v in enumerate(source['variables'])}
 for name,inputs in cert['coordinate_shears']:
  i=names[name];must(name not in inputs,'nonunimodular shear')
  value={(i,):1}
  for other,c in inputs.items():must(type(c) is int,'nonintegral shear');value[(names[other],)]=c
  rows=replace(rows,i,value,n)
 for i,j,c in cert['row_operations']:
  must(i!=j and type(c) is int,'noninvertible residual operation');rows[i]=plus(rows[i],rows[j],c)
 deleted=set();eliminated=set()
 for step in cert['projections']:
  i,j=step['variable'],step['row'];must(i not in eliminated and j not in deleted,'repeated affine projection')
  value=solve(rows[j],i);must(value==read_terms(step['replacement']),'affine restoration')
  must(max(map(len,value),default=0)<=1,'not affine')
  rows=replace(rows,i,value,n);must(not rows[j],'affine pivot not zero');deleted.add(j);eliminated.add(i)
 out=shrink(source,rows,[i for i in range(n) if i not in eliminated],[j for j in range(len(rows)) if j not in deleted]);rows=polynomials(out)
 for i,j,c in cert['final_row_operations']:
  must(i!=j and type(c) is int,'noninvertible final operation');rows[i]=plus(rows[i],rows[j],c)
 quadratic(rows)
 return with_rows(out,rows)

def final_projection(source,cert):
 rows=polynomials(source);n=len(source['variables']);deleted=set();eliminated=set()
 for step in cert['pivots']:
  i,j=step['variable'],step['row'];value=solve(rows[j],i)
  must(value==read_terms(step['replacement']),'final affine restoration')
  rows=replace(rows,i,value,n);must(not rows[j],'final pivot not zero');deleted.add(j);eliminated.add(i)
 j,h=cert['deleted_zero_row'],cert['unconstrained_removed']
 must(j not in deleted and h not in eliminated,'repeated final deletion')
 must(not rows[j] and not any(h in m for p in rows for m in p),'horizon gate not free')
 deleted.add(j);eliminated.add(h)
 kv=[i for i in range(n) if i not in eliminated];kr=[i for i in range(len(rows)) if i not in deleted]
 must(kv==cert['retained_original_variables'] and kr==cert['retained_original_rows'],'final retention lists')
 return shrink(source,rows,kv,kr)

def expanded_check(equation,expanded,metrics):
 r=polynomials(equation);quadratic(r);p={}
 for row in r:p=plus(p,times(row,row))
 must(p==read_terms(expanded['terms']),'all expanded coefficients')
 n=len(equation['variables']);must({i for m in p for i in m}==set(range(n)),'live coordinates')
 actual={'domain':'unrestricted integers','variables':n,'quadratic_residuals':len(r),'degree':max(map(len,p)),'collected_monomials':len(p),'coefficient_height':max(map(abs,p.values())),'residual_height':max(abs(c) for row in r for c in row.values())}
 must(actual==metrics,'all finite metrics');return actual

def main():
 ap=argparse.ArgumentParser();ap.add_argument('archive',type=Path);ap.add_argument('horizon_directory',type=Path);a=ap.parse_args();root=a.horizon_directory
 def local(name):return json.loads((root/name).read_bytes())
 digest=hashlib.sha256(a.archive.read_bytes()).hexdigest();changes=local('source_changes.json')
 must(digest==changes['source_archive_sha256'],'source archive pin');must(changes['growth_multiplier']==1<<26,'growth constant')
 with zipfile.ZipFile(a.archive) as z:
  def get(name):return json.loads(z.read(PREFIX+name))
  original=get('factorial_free_affine/raw_source.json')
  raw=raw_mutation(original,local('raw_source.json'))
  expected_changes=[{'row':i,'before':r['terms'],'after':raw['residuals'][i]['terms']} for i,r in enumerate(original['residuals']) if r['label'] in ('growth.base_definition','cofinal.horizon')]
  claimed_changes=[{k:c[k] for k in ('row','before','after')} for c in changes['changes']]
  must(expected_changes==claimed_changes,'raw source-change ledger')
  horn=horn_rewrite(raw,get('factorial_free_affine/factored_source.json'),get('factorial_free_affine/factorization_certificate.json'))
  pc=local('projection_certificate.json');projected=monic_projection(horn,pc)
  tr=translate(projected,get('factorial_free_affine/translation_certificate.json'))
  report={}
  for profile in ['principal','companion']:
   ac=local(profile+'/affine_certificate.json');changed=affine(tr,ac)
   equal(changed,local(profile+'/mutated_source.json'),'full lineage '+profile)
   target=final_projection(changed,local(profile+'/final_certificate.json'))
   equal(target,local(profile+'/equation.json'),'final horizon coefficients '+profile)
   report[profile]=expanded_check(target,local(profile+'/expanded_polynomial.json'),local(profile+'/metrics.json'))
 # Semantic changed coefficients remain structurally valid in these controls.
 bad=copy.deepcopy(local('raw_source.json'))
 i=next(i for i,r in enumerate(bad['residuals']) if r['label']=='growth.base_definition')
 bad['residuals'][i]['terms'][0][0]-=1
 try:raw_mutation(get_original_raw(a.archive),bad)
 except ValueError:control=True
 else:raise ValueError('changed growth coefficient accepted')
 report.update(status='PASS',source_archive_sha256=digest,raw_semantic_changes=4,monic_restorations=len(pc['steps']),independent_of_producer=True,mutation_control_rejected=control,scope='Complete exact new raw-to-final lineage; inherited Horn factorization proof and unbounded arithmetic calibration remain mathematical dependencies.')
 print(json.dumps(report,sort_keys=True,indent=2))
def get_original_raw(archive):
 with zipfile.ZipFile(archive) as z:return json.loads(z.read(PREFIX+'factorial_free_affine/raw_source.json'))
if __name__=='__main__':main()
