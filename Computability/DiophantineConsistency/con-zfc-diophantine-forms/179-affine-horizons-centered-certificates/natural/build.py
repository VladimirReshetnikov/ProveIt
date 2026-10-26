#!/usr/bin/env python3
"""Rebuild round22 natural charts using only the Python standard library."""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text())
def canon(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def sha(x):return hashlib.sha256(canon(x)).hexdigest()
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def p(ts):return {tuple(m):c for c,m in ts}
def dump(x):return [[c,list(m)] for m,c in sorted(x.items()) if c]
def add(*ps):
 q={}
 for x in ps:
  for m,c in x.items():q[m]=q.get(m,0)+c
 return {m:c for m,c in q.items() if c}
def scale(c,x):return {m:c*v for m,v in x.items() if c*v}
def mul(x,y):
 q={}
 for m,c in x.items():
  for n,d in y.items():
   k=tuple(sorted(m+n));q[k]=q.get(k,0)+c*d
 return {m:c for m,c in q.items() if c}
def sub(x,mp):
 q={}
 for mon,c in x.items():
  term={():c}
  for v in mon:term=mul(term,mp.get(v,{(v,):1}))
  q=add(q,term)
 return q

def finish(e):
 rows=[p(r['terms']) for r in e['residuals']];total=add(*[mul(r,r) for r in rows])
 e['metrics']={'variables':len(e['variables']),'quadratic_rows':len(rows),'exact_degree':max(map(len,total)),'expanded_monomials':len(total),'max_abs_expanded_coefficient':max(map(abs,total.values())),'max_abs_row_coefficient':max(abs(c) for r in rows for c in r.values())}
 if e['metrics']['exact_degree']>4:
  e['metrics']['residual_rows']=e['metrics'].pop('quadratic_rows')
 return {'schema':'sparse_integer_polynomial_v1','domain':e['domain'],'variables':len(e['variables']),'terms':dump(total)}

def chart(source,named):
 e=deepcopy(source);ns={v['name']:i for i,v in enumerate(e['variables'])};rows=[p(r['terms']) for r in e['residuals']];n=len(ns)
 forward=[{(v,):1} for v in range(n)];inverse=deepcopy(forward);ops=[];targets=set();definitions={}
 for entry in named:
  if entry['target'] not in ns:continue
  v=ns[entry['target']];lin={tuple(ns[name] for name in mon):c for c,mon in entry['addition']}
  if any(c<0 or len(m)>1 or v in m for m,c in lin.items()):raise ValueError('non-positive elementary addition')
  mapping={v:add({(v,):1},scale(-1,lin))}
  rows=[sub(r,mapping) for r in rows]
  forward[v]=add(forward[v],sub(lin,dict(enumerate(forward))))
  inverse=[sub(g,mapping) for g in inverse]
  ops.append({'variable':v,'addition':dump(lin)});targets.add(v)
 for v in targets:
  matches=[]
  for j,r in enumerate(source['residuals']):
   q=p(r['terms'])
   if q.get((v,))==1 and all(v not in m for m in q if m!=(v,)) and all(c<0 for m,c in q.items() if m!=(v,)):
    matches.append(j)
  if len(matches)!=1:raise ValueError(('defining gate',v,matches))
  definitions[v]=matches[0]
 order=sorted(targets,key=lambda v:definitions[v]);seen=set()
 for v in order:
  dependencies={w for c,m in source['residuals'][definitions[v]]['terms'] for w in m if w!=v and w in targets}
  if not dependencies<=seen:raise ValueError('not triangular source dependency')
  seen.add(v)
 for r,q in zip(e['residuals'],rows):r['terms']=dump(q)
 ex=finish(e)
 cert={'schema':'natural_triangular_gate_chart_v1','source_sha256':sha(source),'target_sha256':sha(e),'operations':ops,'original_defining_rows':[[v,definitions[v]] for v in order],'forward_map':{str(v):dump(forward[v]) for v in order},'inverse_map':{str(v):dump(inverse[v]) for v in order},'unchanged_variables':[v for v in range(n) if v not in targets]}
 return e,ex,cert

def octic(source):
 e=deepcopy(source);ns={v['name']:i for i,v in enumerate(e['variables'])}
 atom=lambda name:{(ns[name],):1}
 U=ns['pooled_power.U'];K=ns['pooled_power.K'];M=atom('pooled_power.M');n=atom('pow2.output');A=add(atom('shared.lower_A'),atom('shared.A_slack'))
 rows=[p(r['terms']) for r in e['residuals']];removed=[j for j,r in enumerate(rows) if any(U in m or K in m for m in r)]
 if len(removed)!=3:raise ValueError('octic incidence')
 names=[('index0.Y','index0.previous_Y',['choose0.modular_remainder','pooled_digits.t0.slack','crt.range.index.modular_remainder']),('index2.Y','index2.previous_Y',['crt.range.S.modular_remainder','pooled_digits.y.slack','crt.range.Sp.modular_remainder']),('index1.Y','index1.previous_Y',['crt.range.u.modular_remainder','pooled_digits.x.slack','crt.range.vq.modular_remainder'])]
 errors=[]
 for yn,zn,mns in names:
  errors.append(add({():1},atom(zn),*[atom(x) for x in mns],scale(-1,mul(n,atom(yn)))))
 T=add(scale(2,mul(A,n)),scale(-1,mul(n,n)),{():-1});q=add(*[mul(x,x) for x in errors],scale(-1,mul(T,M)))
 if q!=add(rows[removed[2]],mul(n,rows[removed[1]]),scale(-1,mul(mul(n,n),rows[removed[0]]))):raise ValueError('elimination identity')
 e['residuals']=[r for j,r in enumerate(e['residuals']) if j not in removed]+[{'label':'pooled_power.direct_error_quartic','terms':dump(q)}]
 kept=[v for v in range(len(ns)) if v not in (U,K)];ren={v:i for i,v in enumerate(kept)};e['variables']=[e['variables'][v] for v in kept]
 for r in e['residuals']:r['terms']=dump({tuple(ren[v] for v in m):c for c,m in r['terms']})
 e['variant']='round22_natural200_degree8';ex=finish(e)
 return e,ex,{'schema':'natural_pool_linearization_elimination_v1','source_sha256':sha(source),'target_sha256':sha(e),'deleted_rows':removed,'deleted_variables':[U,K],'retained_indices':kept,'unpacked_direct_residual':dump(q),'identity':'R2+n*R1-n^2*R0','n_positive_justification':'inherited retained unpooled pow2 authentication'}

def main(out):
 summary={};named=read(ROOT/'shears.json')
 for n in (202,203,204):
  source=read(ROOT/'inherited'/('pooled'+str(n))/'equation.json');e,x,c=chart(source,named)
  target=out/('chart'+str(n))
  for file,obj in [('equation.json',e),('expanded_polynomial.json',x),('chart_certificate.json',c)]:write(target/file,obj)
  summary[target.name]=e['metrics']
  if n==202:
   ee,xx,cc=octic(e)
   for file,obj in [('equation.json',ee),('expanded_polynomial.json',xx),('elimination_certificate.json',cc)]:write(out/'natural200_degree8'/file,obj)
   summary['natural200_degree8']=ee['metrics']
 import apply_row_basis
 for name,origin in [('natural202','chart202'),('natural202_lowheight','chart202'),('natural203','chart203'),('natural204','chart204')]:
  operations=read(ROOT/name/'operations.json');source=read(out/origin/'equation.json');e,x=apply_row_basis.emit(source,operations);m=e['metrics']
  met={'variables':m['variables'],'rows':m['quadratic_rows'],'terms':m['expanded_monomials'],'height':m['max_abs_expanded_coefficient'],'row_height':m['max_abs_row_coefficient'],'row_support':sum(len(r['terms']) for r in e['residuals'])}
  c={'equation':e,'metrics':met,'operations':operations,'source':'../'+origin+'/equation.json'}
  for file,obj in [('equation.json',e),('expanded_polynomial.json',x),('operations.json',operations),('row_basis_certificate.json',c)]:write(out/name/file,obj)
  summary[name]=m
 write(out/'SUMMARY.json',summary);print(json.dumps(summary,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);main(ap.parse_args().output)
