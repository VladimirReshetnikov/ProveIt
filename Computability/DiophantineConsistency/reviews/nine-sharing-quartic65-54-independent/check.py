#!/usr/bin/env python3
"""Independent exact free-ring reconstruction of the affine-inlined seed."""
import pathlib,json,hashlib,gzip,subprocess,sys,collections
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-quartic65-54-candidate';G=D/'candidates/one-page-padding-staircase-carrier65-2011'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
for name,h in [('seed.json','d3bc360e995a3cd617e43b905875de9db2d4b1a1e4257b4bbc6460e95330fcbc'),('build.py','787469fb24abf36657b0ae8fd708830a2a8edbf67b9d2e202bb5bb4434072c06'),('check.py','41c6e21944b95804ee05f78766b2d2f262e6ed60bc1f06f7182bb8c73cd8c50b'),('result.json','042207ccb78899f362c6d1b24f37fa90b0978090ccf93758b5cc60d0d388a116'),('source_binding.py','01aea8fccceab83c9b94f0d0a9611ce2713f4e1a188b2cd9ab0b13e3491b444e')]:assert sha(P/name)==h
assert sha(G/'polynomial.json')=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads((G/'polynomial.json').read_text());s=json.loads((P/'seed.json').read_text());assert s['source_graph_sha256']==sha(G/'polynomial.json') and s['coefficient_binding']==g['coefficient_binding'] and s['fixed_ports']==g['fixed_numerals']
for name,m in g['coefficient_binding']['ports'].items():
 p=(G/g['coefficient_binding']['path']/m['file']).resolve();z=p.read_bytes();raw=gzip.decompress(z);assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==m['bits'] and int.from_bytes(raw,'big')>0
# Exponent monomials are sorted tuples of free atoms; signed coefficients are integers.
def plus(a,b,scale=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+scale*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   k=tuple(sorted(x+y));c[k]=c.get(k,0)+i*j
 return {k:v for k,v in c.items() if v}
def num(n):return {():n} if n else {}
def variable(n):return {(n,):1}
def evalexpr(e):
 op=e[0]
 if op=='num':return num(e[1])
 if op=='port':return variable('port:'+e[1])
 if op=='var':return variable('var:'+str(e[1]))
 x,y=evalexpr(e[1]),evalexpr(e[2]);return mul(x,y) if op=='mul' else plus(x,y,1 if op=='add' else -1)
def degree(e):
 if e[0] in ('num','port'):return 0
 if e[0]=='var':return 1
 a,b=degree(e[1]),degree(e[2]);return a+b if e[0]=='mul' else max(a,b)
def coords(e):
 if e[0]=='var':return {e[1]}
 if e[0] in ('num','port'):return set()
 return coords(e[1])|coords(e[2])
# Pair components are exact polynomials over input and previously materialized variables.
zero=num(0);pairs={n:(plus(variable('var:'+str(i+1)),num(1)),zero) for i,n in enumerate(g['witnesses'])};pairs.update({n:(variable('port:'+n),zero) for n in g['fixed_numerals']})
def lookup(x):
 if type(x)==int:assert x>=0;return num(x),zero
 return pairs[x]
def residual(rr,kind,name,expected):assert rr['kind']==kind and rr.get('gate')==name and evalexpr(rr['expr'])==expected
assert len(g['source'])==len(s['gate_records'])==65 and len(s['residuals'])==41 and s['jones_witness_count']==54 and s['coordinate_count']==55 and s['input_coordinate']==0
nextres=0;occupied=set(range(1,15));counts=collections.Counter();inline_quadratic=[];cuts=set();constructed=0
for index,(row,rec) in enumerate(zip(g['source'],s['gate_records'])):
 n,op,a,b=row;assert (rec['name'],rec['op'],rec['left'],rec['right'])==(n,op,a,b);ap,am=lookup(a);bp,bm=lookup(b)
 ep=plus(ap,bp) if op=='+' else plus(ap,bm) if op=='-' else plus(mul(ap,bp),mul(am,bm));em=plus(am,bm) if op=='+' else plus(am,bp) if op=='-' else plus(mul(ap,bm),mul(am,bp))
 assert all(v>=0 for v in ep.values()) and all(v>=0 for v in em.values())
 target=mul(plus(ap,am,-1),plus(bp,bm,-1)) if op=='*' else plus(plus(ap,am,-1),plus(bp,bm,-1),1 if op=='+' else -1);assert plus(ep,em,-1)==target
 deg=max(max((sum(x.startswith('var:') for x in m) for m in ep),default=0),max((sum(x.startswith('var:') for x in m) for m in em),default=0));assert deg==rec['pair_degree'] and deg<=2
 if n==g['output']:
  assert index==64 and rec['kind']=='output';residual(s['residuals'][nextres],'output',n,target);nextres+=1;continue
 if rec['kind']=='inline':
  assert deg<=2;counts['inline']+=1
  if deg==2:inline_quadratic.append(n)
  pairs[n]=(ep,em);continue
 assert rec['kind']=='materialized' and deg==2;cuts.add(n);counts['materialized']+=1;ix=rec['positive_coordinate'];assert 15<=ix<55 and ix not in occupied;occupied.add(ix);residual(s['residuals'][nextres],'positive',n,plus(variable('var:'+str(ix)),ep,-1));nextres+=1
 if em:
  iy=rec['negative_coordinate'];assert 15<=iy<55 and iy not in occupied;occupied.add(iy);residual(s['residuals'][nextres],'negative',n,plus(variable('var:'+str(iy)),em,-1));nextres+=1;pairs[n]=(variable('var:'+str(ix)),variable('var:'+str(iy)))
 else:
  assert 'negative_coordinate' not in rec;pairs[n]=(variable('var:'+str(ix)),zero)
assert counts=={'inline':37,'materialized':27} and occupied==set(range(1,55)) and nextres==41 and 14+len(occupied-set(range(1,15)))==54
assert cuts=={'Dc2','Delta','E','N0','N1','Na','Nt','V','V2minusY2','X','Y','c2','cTminusR','ell','f2','gap','kY','main_root','normalized_S','normalized_S2','product0','product1','product3','q2','q3','scaled_Ns','tau'} and inline_quadratic
assert max(degree(x['expr']) for x in s['residuals'])==2 and set.union(*(coords(x['expr']) for x in s['residuals']))==set(range(1,55))
# Evaluate only the first residual with all witness variables zero, retaining beta symbolically.
first=evalexpr(s['residuals'][0]['expr']);first0={tuple(x for x in mon if not x.startswith('var:')):coef for mon,coef in first.items() if not any(x.startswith('var:') for x in mon)};beta=variable('port:beta');assert first0=={k:-v for k,v in mul(plus(beta,num(1)),plus(beta,num(1))).items()}
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
q=subprocess.run([sys.executable,str(D/'reviews/nine-sharing-quartic65-59-independent/source_check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(D/'reviews/nine-sharing-quartic65-59-independent/source_result.json').read_bytes()
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'source_binding.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'source-binding-result.json').read_bytes()
print(json.dumps({'status':'PASS','source_gates':65,'inlined':counts['inline'],'quadratic_inlined':inline_quadratic,'materialized':counts['materialized'],'gate_witnesses':40,'residuals':41,'quartic_witnesses':54,'coordinates':55,'first_residual_at_zero':'-(beta+1)^2','scope':'External exact signed-pair gate identities, source-graph binding and quartic upper bound; no Lean model/Jones endpoint or final nine-variable graph/degree.'},indent=2))
