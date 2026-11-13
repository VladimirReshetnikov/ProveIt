from pathlib import Path
from hashlib import sha256
import json,re,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-zero-graph-fact-binding-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'IndependentKZeroGraphFacts.lean.src').read_text()
for n in ('first_fields','first_norm','main_field','main_norm','zero_k_impossible_of_rank_representation'):
 assert len(re.findall(r'^theorem '+n+r'\b',s,re.M))==1
 assert '#print axioms DiophantineConsistency.IndependentKZeroGraphFactsDraft.'+n in s
for x in ('(hR : rankRing v=ι R)','(hk : v 10=0)','IndependentKUnitBridgeDraft.signed_norms intPorts v hz',
 'have hJ := child_J_positive v hz','apply zero_k_fact_cut','(natPorts 3:V)'):
 assert x in s,x
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={row[0]:row[1:] for row in g['source']}
for n,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],
 'Y':['*','q3','s'],'U':['*','Y','q2'],'kY':['*','Y','n_k'],
 'c':['+','n_eta','kY'],'ell':['*','E','kY'],'g26':['+','X','K0'],
 'Bt':['-','g27','F'],'Z':['-','g32','Bt'],'G':['+','alpha','g44'],
 'R':['+','g47','g50'],'r0base':['-','n_k','R'],'shift':['-','g54','r0'],
 'Dstar':['+','g58','g59'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[n]==row,(n,r[n])
assert g['witnesses'][10]=='n_k' and g['fixed_numerals']==['beta','K0','MC','MF']
rng=random.Random(6012)
for _ in range(1000):
 v=[rng.randrange(5) for i in range(13)];v[10]=0;p=[rng.randrange(7) for i in range(4)]
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],p))
 for n,op,x,y in g['source']:
  x=e[x] if isinstance(x,str) else x;y=e[y] if isinstance(y,str) else y
  e[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 b=p[0]*v[0];q=b+1;X=q*v[6];Y=q**3*(v[7]+1);U=Y*q*q
 C=q-(v[1]+1)-(v[2]+1);B=C*(X+p[1])-(v[1]+1)
 R=(v[2]+1+(q-(v[1]+1))*b)*(q*q-1)+v[0]*(p[2]+q*p[3]);a=X*Y+Y;H=3+4*a
 z=U*(X+a*v[9])+H*(U*v[12]+R+1)
 assert e['Z']==b*v[8]-B and e['ell']==0 and e['R']==R and e['Dstar']==z
 assert e['A0']==e['Z']**2-b*b and e['A1']==z*z-U*U*(1+(H+a*a)*v[9]**2)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'graph_zero_k_field_wiring_checked':True,'bounded_exact_graph_controls':1000,
 'rank_representation_explicit':True,'lexical_interface_checks':True,
 'lean_executed':False,'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
