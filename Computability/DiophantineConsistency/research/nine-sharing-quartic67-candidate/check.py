#!/usr/bin/env python3
"""Independently verify signed-gate identities and the concrete quartic recipe."""
import collections,gzip,hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];G=D/'research/current2011-ordinary67-94-candidate';raw=(G/'polynomial.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb';g=json.loads(raw);s=json.loads((P/'seed.json').read_text());assert s['source_graph_sha256']==hashlib.sha256(raw).hexdigest() and s['coefficient_binding']==g['coefficient_binding'] and s['fixed_ports']==g['fixed_numerals']
ports=g['coefficient_binding']['ports'];root=(G/g['coefficient_binding']['path']).resolve()
for name,meta in ports.items():
 p=root/meta['file'];gz=p.read_bytes();raw=gzip.decompress(gz);assert hashlib.sha256(gz).hexdigest()==meta['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==meta['bits'] and int.from_bytes(raw,'big')>0,name
# Sparse commutative polynomials over abstract named variables/ports.
def clean(a):return {m:c for m,c in a.items() if c}
def plus(a,b,sgn=1):
 z=collections.Counter(a)
 for m,c in b.items():z[m]+=sgn*c
 return clean(z)
def times(a,b):
 z=collections.Counter()
 for x,c in a.items():
  for y,d in b.items():z[tuple(sorted(x+y))]+=c*d
 return clean(z)
def atom(x):return {(str(x),):1}
def const(n):return {():n} if n else {}
def pol(t):
 op=t[0]
 if op=='num':return const(t[1])
 if op in ('var','port'):return atom(op+':'+str(t[1]))
 a,b=map(pol,t[1:]);return times(a,b) if op=='mul' else plus(a,b,1 if op=='add' else -1)
def deg(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 a,b=map(deg,t[1:]);return a+b if t[0]=='mul' else max(a,b)
def used(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return used(t[1])|used(t[2])
N=lambda x:['num',x];V=lambda i:['var',i];A=lambda a,b:['add',a,b];Z=N(0);pair={n:(A(V(i+1),N(1)),Z,True) for i,n in enumerate(g['witnesses'])};pair.update({n:(['port',n],Z,True) for n in g['fixed_numerals']});get=lambda x:(N(x),Z,True) if type(x)==int else pair[x]
rows=s['gate_records'];res=s['residuals'];assert len(rows)==67 and len(res)==97 and s['jones_witness_count']==110 and s['coordinate_count']==111 and s['input_coordinate']==0 and s['guard_coordinate']==110
assert res[0]=={'kind':'guard','expr':['sub',V(110),N(1)]};idx=1;coords=set(range(1,15));known=unknown=0
for i,(gr,rr) in enumerate(zip(g['source'],rows)):
 name,op,l,r=gr;assert (rr['name'],rr['op'],rr['left'],rr['right'])==(name,op,l,r);a=get(l);b=get(r);positive=op in ('+','*') and a[2] and b[2];assert rr['known_nonnegative']==positive
 av=plus(pol(a[0]),pol(a[1]),-1);bv=plus(pol(b[0]),pol(b[1]),-1);target=times(av,bv) if op=='*' else plus(av,bv,1 if op=='+' else -1)
 if name==g['output']:
  assert i==66 and rr['output'] is True and res[idx]['kind']=='output' and res[idx]['gate']==name and pol(res[idx]['expr'])==target;idx+=1;continue
 ip=rr['positive_coordinate'];assert 15<=ip<110 and ip not in coords;coords.add(ip);rpos=res[idx];assert rpos['kind']=='positive' and rpos['gate']==name;idx+=1
 if positive:
  known+=1;expected=plus(atom('var:'+str(ip)),target,-1);assert pol(rpos['expr'])==expected;pair[name]=(V(ip),Z,True)
 else:
  unknown+=1;ineg=rr['negative_coordinate'];assert 15<=ineg<110 and ineg not in coords;coords.add(ineg);rneg=res[idx];assert rneg['kind']=='negative' and rneg['gate']==name;idx+=1
  ap,an,bp,bn=pol(a[0]),pol(a[1]),pol(b[0]),pol(b[1])
  ep=plus(ap,bp) if op=='+' else plus(ap,bn) if op=='-' else plus(times(ap,bp),times(an,bn))
  en=plus(an,bn) if op=='+' else plus(an,bp) if op=='-' else plus(times(ap,bn),times(an,bp))
  assert pol(rpos['expr'])==plus(atom('var:'+str(ip)),ep,-1) and pol(rneg['expr'])==plus(atom('var:'+str(ineg)),en,-1)
  assert plus(pol(rpos['expr']),pol(rneg['expr']),-1)==plus(plus(atom('var:'+str(ip)),atom('var:'+str(ineg)),-1),target,-1);pair[name]=(V(ip),V(ineg),False)
assert idx==len(res) and (known,unknown)==(37,29) and coords==set(range(1,110))
assert max(deg(x['expr']) for x in res)==2 and set.union(*(used(x['expr']) for x in res))==set(range(1,111))
# Build natural pair assignments, then independently evaluate the residuals
# and compare their sum of squares to the source graph output squared.
def ev(t,v,p):
 op=t[0]
 if op=='num':return t[1]
 if op=='var':return v[t[1]]
 if op=='port':return p[t[1]]
 a,b=(ev(x,v,p) for x in t[1:]);return a+b if op=='add' else a-b if op=='sub' else a*b
rng=random.Random(1234567)
for _ in range(12):
 vals={i:rng.randrange(3) for i in range(1,15)};vals[0]=1;vals[110]=1;p={n:rng.randrange(1,5) for n in g['fixed_numerals']};sv={n:vals[i+1]+1 for i,n in enumerate(g['witnesses'])};sv.update(p)
 for (name,op,l,r),rr in zip(g['source'],rows):
  x=l if type(l)==int else sv[l];y=r if type(r)==int else sv[r];sv[name]=x+y if op=='+' else x-y if op=='-' else x*y
  if rr.get('output'):continue
  if rr['known_nonnegative']:
   vals[rr['positive_coordinate']]=sv[name];assert sv[name]>=0
  else:
   av=ev(get(l)[0],vals,p);an=ev(get(l)[1],vals,p);bv=ev(get(r)[0],vals,p);bn=ev(get(r)[1],vals,p)
   ep=av+bv if op=='+' else av+bn if op=='-' else av*bv+an*bn;en=an+bn if op=='+' else an+bv if op=='-' else av*bn+an*bv
   assert ep>=0 and en>=0 and ep-en==sv[name];vals[rr['positive_coordinate']]=ep;vals[rr['negative_coordinate']]=en
 value=sum(ev(x['expr'],vals,p)**2 for x in res);assert value==sv[g['output']]**2
print(json.dumps({'status':'PASS_EXTERNAL_CANDIDATE','source_gates':67,'nonnegative_internal_gates':known,'signed_internal_gates':unknown,'residuals':len(res),'jones_witnesses':110,'total_seed_coordinates':111,'maximum_residual_degree':2,'seed_degree_upper':4,'tested_assignments':12,'scope':'External gate identities and witness construction; no Lean quartic/model/Jones proof or nine-variable graph/degree claim.'},sort_keys=True,indent=2))
