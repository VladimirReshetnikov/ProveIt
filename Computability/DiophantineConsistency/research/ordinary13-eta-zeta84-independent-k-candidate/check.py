from pathlib import Path
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-independent-k-candidate');p=Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json');raw=p.read_bytes()
assert sha256(raw).hexdigest()=='ce50ab07246ad3fb77ad787fa5703fd64a8dfd94a346308b73f891225cb36f03'
g=json.loads(raw);assert len(g['source'])==85 and g['witnesses'][9:11]==['n_eta','n_zeta']
uses=[row for row in g['source'] if 'n_zeta' in row];assert uses==[['kbase','+','n_eta','n_zeta']]
rows=[];deleted=0
for row in g['source']:
 if row==['kbase','+','n_eta','n_zeta']:deleted+=1;continue
 rows.append(['n_k' if x=='kbase' else x for x in row])
assert deleted==1 and len(rows)==84
w=g['witnesses'].copy();w[10]='n_k'
child={'name':'independent k coordinate: conditional zero-map candidate, no unrestricted equivalence', 'domain':g['domain'],'witnesses':w,'fixed_numerals':g['fixed_numerals'],'source':rows,'output':g['output'],'parent_sha256':sha256(raw).hexdigest(),'proof_status':'pointwise parent-to-child identity and conditional reverse if k>=eta; compact graph forcing open'}
encoded=(json.dumps(child,indent=2,ensure_ascii=False)+'\n').encode()
if '--write' in sys.argv:(D/'candidate.json').write_bytes(encoded)
else:assert (D/'candidate.json').read_bytes()==encoded
# Structural induction certificate: after changing slot 10 to eta+zeta,
# every row after the deleted kbase is exactly the old operation on matching
# wires. This works over any commutative ring and integer ports.
assert all('kbase' not in row for row in rows)
def ev(graph,ws,ps,mod=None):
 d=dict(zip(graph['witnesses'],ws));d.update(zip(graph['fixed_numerals'],ps))
 for name,op,a,b in graph['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  z={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  d[name]=z if mod is None else z%mod
 return d
rng=random.Random(481605);m=1000000007
for _ in range(300):
 parent=[rng.randrange(0,25) for _ in range(13)];ports=[rng.randrange(-4,7) for _ in range(4)]
 c=parent.copy();c[10]=parent[9]+parent[10]
 a=ev(g,parent,ports,m);b=ev(child,c,ports,m)
 for name in ['A0','A1','Fa','g72','out']:assert a[name]==b[name],name
 assert c[10]>=c[9] and c[10]-c[9]==parent[10]
# Syntactic total-degree bounds; port coefficients are degree 0. They are
# upper bounds, not a proof that the expanded polynomial reaches that degree.
def bound(graph):
 d={name:1 for name in graph['witnesses']};d.update({name:0 for name in graph['fixed_numerals']})
 for name,op,a,b in graph['source']:
  x=d[a] if isinstance(a,str) else 0;y=d[b] if isinstance(b,str) else 0
  d[name]=x+y if op=='*' else max(x,y)
 return d[graph['output']]
print(json.dumps({'parent_sha256':sha256(raw).hexdigest(),'candidate_sha256':sha256(encoded).hexdigest(),'parent_rows':85,'candidate_rows':84,'natural_inputs':13,'parent_degree_upper_bound':bound(g),'candidate_degree_upper_bound':bound(child),'exact_forward_coordinate_map':'child[10]=parent[9]+parent[10]','conditional_inverse':'parent[10]=child[10]-child[9] when child[10]>=child[9]','structural_row_identity_checked':True,'modular_controls':300,'unrestricted_compact_zero_map_proved':False,'lean_executed':False},sort_keys=True,indent=2))
