#!/usr/bin/env python3
"""Independent residual audit using exact free-ring term dictionaries."""
import pathlib,json,hashlib,gzip,subprocess,sys,collections
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-quartic67-candidate';G=D/'research/current2011-ordinary67-94-candidate'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
for name,h in [('seed.json','950c6ced32a0283a43a677f640430e15e100f26feddefd577761420f470867a6'),('build.py','872365790b82198b4f56eb6b76a6bbdbe4724c6720e21602685a80080931fd02'),('check.py','f380d93748c1f1a509729cfdf1b7ede3f6a53a1272bd628726e57fa53764d16b'),('result.json','4c97206b8166b8df11218a74fbd7543406b1408b4cb46655f706135907cc9829')]:assert sha(P/name)==h
assert sha(G/'polynomial.json')=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb';g=json.loads((G/'polynomial.json').read_text());s=json.loads((P/'seed.json').read_text());assert s['source_graph_sha256']==sha(G/'polynomial.json') and s['coefficient_binding']==g['coefficient_binding'] and s['fixed_ports']==g['fixed_numerals']
for name,m in g['coefficient_binding']['ports'].items():
 path=(G/g['coefficient_binding']['path']/m['file']).resolve();z=path.read_bytes();raw=gzip.decompress(z);assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==m['bits'] and int.from_bytes(raw,'big')>0
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
# Pair components are exact polynomials over earlier natural witness variables.
zero=num(0);pairs={n:(plus(variable('var:'+str(i+1)),num(1)),zero,True) for i,n in enumerate(g['witnesses'])};pairs.update({n:(variable('port:'+n),zero,True) for n in g['fixed_numerals']})
def lookup(x):
 if type(x)==int:assert x>=0;return num(x),zero,True
 return pairs[x]
def residual(rr,kind,name,expected):assert rr['kind']==kind and rr.get('gate')==name and evalexpr(rr['expr'])==expected
assert len(g['source'])==len(s['gate_records'])==67 and len(s['residuals'])==97 and s['jones_witness_count']==110 and s['coordinate_count']==111 and s['input_coordinate']==0 and s['guard_coordinate']==110
assert s['residuals'][0]=={'kind':'guard','expr':['sub',['var',110],['num',1]]}
nextres=1;occupied=set(range(1,15));counts=collections.Counter()
for index,(row,rec) in enumerate(zip(g['source'],s['gate_records'])):
 n,op,a,b=row;assert (rec['name'],rec['op'],rec['left'],rec['right'])==(n,op,a,b);ap,am,asign=lookup(a);bp,bm,bsign=lookup(b);safe=op in ('+','*') and asign and bsign;assert rec['known_nonnegative']==safe
 apos=plus(ap,am,-1);bpos=plus(bp,bm,-1);target=mul(apos,bpos) if op=='*' else plus(apos,bpos,1 if op=='+' else -1)
 if n==g['output']:
  assert index==66 and rec['output'] is True;residual(s['residuals'][nextres],'output',n,target);nextres+=1;continue
 ix=rec['positive_coordinate'];assert 15<=ix<110 and ix not in occupied;occupied.add(ix);counts['one' if safe else 'two']+=1
 if safe:
  residual(s['residuals'][nextres],'positive',n,plus(variable('var:'+str(ix)),target,-1));nextres+=1;pairs[n]=(variable('var:'+str(ix)),zero,True)
 else:
  iy=rec['negative_coordinate'];assert 15<=iy<110 and iy not in occupied;occupied.add(iy)
  ep=plus(ap,bp) if op=='+' else plus(ap,bm) if op=='-' else plus(mul(ap,bp),mul(am,bm));em=plus(am,bm) if op=='+' else plus(am,bp) if op=='-' else plus(mul(ap,bm),mul(am,bp))
  assert plus(ep,em,-1)==target
  residual(s['residuals'][nextres],'positive',n,plus(variable('var:'+str(ix)),ep,-1));residual(s['residuals'][nextres+1],'negative',n,plus(variable('var:'+str(iy)),em,-1));nextres+=2;pairs[n]=(variable('var:'+str(ix)),variable('var:'+str(iy)),False)
assert counts=={'one':37,'two':29} and occupied==set(range(1,110)) and nextres==97
assert max(degree(x['expr']) for x in s['residuals'])==2 and set.union(*(coords(x['expr']) for x in s['residuals']))==set(range(1,111))
assert 14+counts['one']+2*counts['two']+1==110 and len(s['residuals'])==1+counts['one']+2*counts['two']+1
# At all-zero witnesses the explicit guard residual is -1 and contributes one square.
assert evalexpr(s['residuals'][0]['expr'])==plus(variable('var:110'),num(1),-1)
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS','source_gates':67,'single_gate_witnesses':counts['one'],'paired_gate_witnesses':counts['two'],'residuals':97,'quartic_witnesses':110,'quartic_coordinate_count':111,'scope':'External universal gate identities and structural counts; no Lean nine-variable endpoint, file theorem or final graph/degree.'},indent=2))
