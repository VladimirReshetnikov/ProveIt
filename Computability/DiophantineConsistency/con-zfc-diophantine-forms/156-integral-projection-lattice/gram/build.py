#!/usr/bin/env python3
import json,pathlib,sys,hashlib,collections,math
from fractions import Fraction
def prod(a,b):
 d=collections.defaultdict(int)
 for am,ac in a.items():
  for bm,bc in b.items(): d[tuple(sorted(am+bm))]+=ac*bc
 return {m:c for m,c in d.items() if c}
def addto(a,b,sign=1):
 for m,c in b.items():
  a[m]=a.get(m,0)+sign*c
  if not a[m]:del a[m]
def metrics(p):return len(p),max(map(abs,p.values())),sum(map(abs,p.values()))

def components(n,edges):
 adj={i:[] for i in range(n)}
 for i,j,s in edges:adj[i].append(j);adj[j].append(i)
 seen=set();out=[]
 for i in range(n):
  if i in seen or not adj[i]:continue
  vs=[i];seen.add(i)
  for k in vs:
   for j in adj[k]:
    if j not in seen:seen.add(j);vs.append(j)
  out.append(sorted(vs))
 return out

def ldl(mat):
 n=len(mat);A=[[Fraction(x) for x in row] for row in mat];L=[[Fraction(int(i==j)) for j in range(n)] for i in range(n)];D=[]
 for k in range(n):
  pivot=A[k][k];D.append(pivot)
  if pivot<=0:raise ValueError('Gram matrix is not positive definite')
  for i in range(k+1,n):L[i][k]=A[i][k]/pivot
  for i in range(k+1,n):
   for j in range(k+1,n):A[i][j]-=A[i][k]*A[k][j]/pivot
 return L,D

def encode(z):return [z.numerator,z.denominator]
def emit(source_path,edge_list,outpath):
 out=pathlib.Path(outpath);out.mkdir(parents=True,exist_ok=True)
 source=pathlib.Path(source_path);s=json.loads(source.read_text());edges=[tuple(e) for e in edge_list]
 rows=[{tuple(m):int(c) for c,m in row['terms']} for row in s['residuals']];n=len(rows);p={}
 for r in rows:addto(p,prod(r,r))
 source_metrics=metrics(p)
 for i,j,sgn in edges:addto(p,prod(rows[i],rows[j]),sgn)
 blocks=[]
 for vs in components(n,edges):
  idx={v:i for i,v in enumerate(vs)};d=len(vs);H=[[2*int(i==j) for j in range(d)] for i in range(d)]
  for i,j,sgn in edges:
   if i in idx:H[idx[i]][idx[j]]=H[idx[j]][idx[i]]=sgn
  L,D=ldl(H);det=math.prod(D)
  blocks.append({'residual_indices':vs,'gram_matrix_H':H,'unit_lower_L':[[encode(x) for x in rr] for rr in L],'positive_diagonal_D':[encode(x) for x in D],'determinant':encode(det)})
 srcsha=hashlib.sha256(source.read_bytes()).hexdigest()
 equation={'schema':'proveit.diophantine.gram.v1','domain':'unrestricted integers','definition':'sum(r_i^2) + sum(sign*r_i*r_j for [i,j,sign] in gram_cross_terms)','source_sha256':srcsha,'variables':s['variables'],'residuals':s['residuals'],'gram_cross_terms':[list(e) for e in edges]}
 polynomial={'schema':'proveit.diophantine.sparse.v1','domain':'unrestricted integers','variables':s['variables'],'terms':[[c,list(m)] for m,c in sorted(p.items())]}
 stat={'variable_count':len(s['variables']),'used_variables':len(set(v for m in p for v in m)),'residual_count':n,'degree':max(map(len,p)),'monomial_count':len(p),'coefficient_height':max(map(abs,p.values())),'coefficient_l1':sum(map(abs,p.values())),'content':math.gcd(*p.values()),'cross_term_count':len(edges),'source_monomials':source_metrics[0],'source_height':source_metrics[1],'source_l1':source_metrics[2]}
 cert={'source_sha256':srcsha,'H_convention':'diagonal 2, symmetric edge signs off diagonal, zeros otherwise; Q = r^T H r / 2','blocks':blocks,'isolated_count':n-sum(len(b['residual_indices']) for b in blocks),'identity':'Each block H = L D L^T. All D entries are positive. Therefore Q vanishes exactly when every residual vanishes.'}
 for name,obj in [('equation.json',equation),('expanded_polynomial.json',polynomial),('GRAM_CERTIFICATE.json',cert),('METRICS.json',stat)]:
  (out/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
 (out/'source_equation.json').write_bytes(source.read_bytes())
 print(json.dumps({'directory':str(out),'metrics':stat,'blocks':[{'dimension':len(b['residual_indices']),'determinant':b['determinant'],'pivots':b['positive_diagonal_D']} for b in blocks]},indent=2))

if __name__=='__main__':
 import argparse,tempfile
 parser=argparse.ArgumentParser(description="Rebuild the frozen integer Gram equations with exact arithmetic.")
 parser.add_argument('--check',action='store_true',help='Compare regenerated artifacts byte for byte (default).')
 parser.add_argument('--output',type=pathlib.Path,help='Write reconstructed components to this directory.')
 args=parser.parse_args();root=pathlib.Path(__file__).resolve().parent
 configurations=json.loads((root/'EDGES.json').read_text())
 def run(destination,check):
  for name,edges in configurations.items():
   emit(root/name/'source_equation.json',edges,destination/name)
   if check:
    for filename in ('source_equation.json','equation.json','expanded_polynomial.json','GRAM_CERTIFICATE.json','METRICS.json'):
     if (destination/name/filename).read_bytes()!=(root/name/filename).read_bytes():
      raise ValueError('Reconstruction mismatch: '+name+'/'+filename)
  print('All exact Gram reconstructions passed.')
 if args.output is not None:
  run(args.output.resolve(),False)
 else:
  with tempfile.TemporaryDirectory(prefix='proveit-gram-rebuild-') as tmp:
   run(pathlib.Path(tmp),True)
