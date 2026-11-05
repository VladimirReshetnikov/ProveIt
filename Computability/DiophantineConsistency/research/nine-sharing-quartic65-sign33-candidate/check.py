#!/usr/bin/env python3
"""Exact free-ring identities for the five-norm sharing candidate; no Lean."""
import pathlib,json,hashlib,gzip,subprocess,sys,collections,random
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-quartic65-sign33-candidate';G=D/'candidates/one-page-padding-staircase-carrier65-2011'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(P/'seed.json')=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75' and sha(P/'build.py')=='bfd718c5f0eced2e362bc7940c61c66769fcb0eaf72ad18ff0bc436056fabb0b'
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
assert len(g['source'])==65 and len(s['gate_records'])==60 and s['omitted_graph_rows']==g['source'][60:] and len(s['residuals'])==24 and s['jones_witness_count']==33 and s['coordinate_count']==34 and s['input_coordinate']==0
normtargets={'N0':1,'N1':1,'Na':1,'Nt':1,'scaled_Ns':'Delta'};assert s['norm_targets']==normtargets
nextres=0;occupied=set(range(1,15));counts=collections.Counter();cuts=set();construction=[];terminal=[]
for index,(row,rec) in enumerate(zip(g['source'][:60],s['gate_records'])):
 n,op,a,b=row;assert (rec['name'],rec['op'],rec['left'],rec['right'])==(n,op,a,b);ap,am=lookup(a);bp,bm=lookup(b)
 ep=plus(ap,bp) if op=='+' else plus(ap,bm) if op=='-' else plus(mul(ap,bp),mul(am,bm));em=plus(am,bm) if op=='+' else plus(am,bp) if op=='-' else plus(mul(ap,bm),mul(am,bp));assert all(v>=0 for v in ep.values()) and all(v>=0 for v in em.values())
 left=plus(ap,am,-1);right=plus(bp,bm,-1);value=mul(left,right) if op=='*' else plus(left,right,1 if op=='+' else -1);assert plus(ep,em,-1)==value
 deg=max(max((sum(x.startswith('var:') for x in m) for m in ep),default=0),max((sum(x.startswith('var:') for x in m) for m in em),default=0));assert deg==rec['pair_degree'] and deg<=2
 if n in normtargets:
  assert rec['kind']=='norm' and rec['target']==normtargets[n];rhs=plus(*lookup('Delta')[:2],-1) if n=='scaled_Ns' else num(1);rr=s['residuals'][nextres];assert rr['target']==normtargets[n];residual(rr,'norm',n,plus(value,rhs,-1));nextres+=1;pairs[n]=(ep,em);terminal.append(n);continue
 if rec['kind']=='inline':assert deg<=2;counts['inline']+=1;pairs[n]=(ep,em);continue
 assert rec['kind']=='materialized' and deg==2;cuts.add(n);counts['materialized']+=1
 if n in {'gap','tau','cTminusR','V','V2minusY2'}:
  ix=rec['sign_coordinate'];sign=rec['sign'];assert sign==(-1 if n=='V2minusY2' else 1);assert 15<=ix<34 and ix not in occupied;occupied.add(ix)
  rr=s['residuals'][nextres];assert rr['sign']==sign;residual(rr,'signed',n,plus(variable('var:'+str(ix)),plus(ep,em,-1),-sign));nextres+=1
  pairs[n]=(variable('var:'+str(ix)),zero) if sign==1 else (zero,variable('var:'+str(ix)))
  construction.append((ix,None,ep,em,sign))
 else:
  ix=rec['positive_coordinate'];assert 15<=ix<34 and ix not in occupied;occupied.add(ix);residual(s['residuals'][nextres],'positive',n,plus(variable('var:'+str(ix)),ep,-1));nextres+=1
  if em:
   iy=rec['negative_coordinate'];assert 15<=iy<34 and iy not in occupied;occupied.add(iy);residual(s['residuals'][nextres],'negative',n,plus(variable('var:'+str(iy)),em,-1));nextres+=1;pairs[n]=(variable('var:'+str(ix)),variable('var:'+str(iy)))
  else:assert 'negative_coordinate' not in rec;iy=None;pairs[n]=(variable('var:'+str(ix)),zero)
  construction.append((ix,iy,ep,em,0))
assert counts=={'inline':36,'materialized':19} and occupied==set(range(1,34)) and nextres==24 and len(terminal)==5 and set(terminal)==set(normtargets)
assert cuts=={'Dc2','Delta','E','V','V2minusY2','X','Y','c2','cTminusR','ell','f2','gap','kY','main_root','normalized_S','normalized_S2','q2','q3','tau'}
assert max(degree(x['expr']) for x in s['residuals'])==2 and set.union(*(coords(x['expr']) for x in s['residuals']))==set(range(1,34))
first=evalexpr(s['residuals'][0]['expr']);first0={m:c for m,c in first.items() if not any(x.startswith('var:') for x in m)};beta=variable('port:beta');assert first0=={k:-v for k,v in mul(plus(beta,num(1)),plus(beta,num(1))).items()}
# Symbolic ring check: Z = Delta * (f² - Delta*(i*c²)²).
delta=variable('delta');f=variable('f');i=variable('i');c=variable('c');c2=mul(c,c);I=mul(i,c2);S=mul(delta,I);Z=plus(mul(delta,mul(f,f)),mul(S,S),-1);strong=plus(mul(f,f),mul(delta,mul(I,I)),-1);assert Z==mul(delta,strong)
def evalpoly(p,v,ports):
 total=0
 for m,coef in p.items():
  t=coef
  for x in m:t*=v[int(x[4:])] if x.startswith('var:') else ports[x[5:]]
  total+=t
 return total
rng=random.Random(4813);negative_cut_assignments=0
for _ in range(8):
 vals={i:rng.randrange(3) for i in range(1,15)};vals[0]=rng.randrange(5);ports={n:rng.randrange(1,5) for n in g['fixed_numerals']};sv={n:vals[i+1]+1 for i,n in enumerate(g['witnesses'])};sv.update(ports)
 for ix,iy,ep,em,sign in construction:
  vp=evalpoly(ep,vals,ports);vm=evalpoly(em,vals,ports);vals[ix]=sign*(vp-vm) if sign else vp
  if vals[ix]<0:negative_cut_assignments+=1
  if iy is not None:vals[iy]=vm
 for n,op,a,b in g['source'][:60]:
  x=a if type(a)==int else sv[a];y=b if type(b)==int else sv[b];sv[n]=x+y if op=='+' else x-y if op=='-' else x*y
 expect=sum((sv[n]-(sv['Delta'] if n=='scaled_Ns' else 1))**2 for n in normtargets);actual=sum(evalpoly(evalexpr(x['expr']),vals,ports)**2 for x in s['residuals']);assert actual==expect
q=subprocess.run([sys.executable,str(D/'reviews/nine-sharing-quartic65-59-independent/source_check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(D/'reviews/nine-sharing-quartic65-59-independent/source_result.json').read_bytes()
print(json.dumps({'status':'PASS_CONDITIONAL_EXTERNAL_SIGN_CANDIDATE','source_rows_used':60,'omitted_product_rows':5,'inline_gates':counts['inline'],'materialized_gates':counts['materialized'],'gate_witnesses':19,'quartic_witnesses':33,'seed_coordinates':34,'residuals':24,'terminal_norms':normtargets,'max_residual_degree':2,'seed_degree_upper':4,'zero_normalization':'first residual = -(beta+1)^2','tested_integer_assignments':8,'negative_cut_assignments_in_tests':negative_cut_assignments,'scope':'Integer gate replay permits negative signed coordinates in tests; model-natural witness construction requires separately proving five sign obligations. All Lean bridge, degree/normalization and Jones/iPRA endpoint unchecked.'},indent=2,sort_keys=True))
