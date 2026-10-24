import json, pathlib, hashlib, gzip, sympy as s
p=pathlib.Path(__file__).resolve().parent
d=json.loads((p/'signed34_sextic.json').read_text()); vs=s.symbols(' '.join(d['variables'])); ports=s.symbols(' '.join(d['fixed_numerals'])); names={str(x):x for x in vs+ports}; rows=[s.sympify(x,locals=names) for x in d['residuals']]
def need(ok,msg):
 if not ok: raise RuntimeError(msg)
r,c=names['r'],names['c']; involving=[x for x in rows if x.has(r)]
need(len(involving)==1,'r uniqueness')
need(s.expand(involving[0]-(names['I']-(2*r+1)*c*c))==0,'r defining row')
need(all(s.Poly(x,*vs).total_degree()<=3 for x in rows),'degree upper bound')
need(set.union(*(x.free_symbols for x in rows))==set(vs+ports),'all unknowns and all coefficient ports live')
checks=0
for x in range(64,129):
 for z in range(5,65):
  gap=(2*(x-1)*z-5)**2-(x-3)*(4*x*z*z-2)
  need(gap==4*(x+1)*z*z-20*(x-1)*z+25+2*(x-3)>0,'base growth gap')
  checks+=1
for x in range(64,129):
 for n in range(1,20):
  need((x-3)**n>2**(2*n+2)+2,'final growth comparison');checks+=1
for exponent in range(3,33):
 beta=2**exponent-1
 for t in range(4*exponent):
  need((-pow(2,t,beta))%beta!=1,'Mersenne sign');checks+=1
source=p/'upstream/q41'
receipt=json.loads((p/'UPSTREAM_COPY_RECEIPT.json').read_text())
for name,expected in receipt['files'].items():
 need(hashlib.sha256((source/name).read_bytes()).hexdigest()==expected,'copied source '+name)
binding=d['coefficient_binding']; manifest=json.loads((p/binding['inherited_manifest']).read_text())
for port,rel in binding['ports'].items():
 path=p/rel; raw=gzip.decompress(path.read_bytes()); key={'K0':'K','MF':'MF_source'}.get(port,port)
 need(hashlib.sha256(raw).hexdigest()==manifest['payloads'][key]['sha256'],'actual raw coefficient '+port)
 need(len(raw)==manifest['payloads'][key]['bytes'],'actual coefficient length '+port)
source_hash={n:hashlib.sha256((source/n).read_bytes()).hexdigest() for n in ['quartic41.json','PROOF41.md','PROOF44.md']}
result={'status':'PASS finite algebra, authenticated source closure, actual coefficient payloads and elementary diagnostic checks; unbounded proof independently reviewed, not kernel checked','variable_count':34,'residual_count':19,'exact_degree':6,'degree_witness':{'monomial':'r^2*c^4','coefficient':4},'finite_diagnostic_cases':checks,'source_sha256':source_hash,'source_package':'con-zfc-structural-reductions-2026-10-23','arrival_commit':'0c6be9a074d8905b22015e93c5c9d28eda36e95e','placement_commit':'a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49'}
(p/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
