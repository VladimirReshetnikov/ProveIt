#!/usr/bin/env python3
"""Third-party audit. Imports no producer/checker/recipe arithmetic code."""
import ast, collections, copy, gzip, hashlib, json, math, os, pathlib, shutil, subprocess, sys, tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]/'scalar'
OUT=pathlib.Path(__file__).resolve().parent
VARIABLES='j C z h r v w T c n s'.split()
PORTS='beta K0 MC MF cone_A cone_B'.split()
def req(x,m):
 if not x: raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
class Poly:
 def __init__(self,x=0):self.t=x if isinstance(x,dict) else ({():x} if x else {})
 @staticmethod
 def var(n):return Poly({((n,1),):1})
 def __add__(a,b):
  if not isinstance(b,Poly):b=Poly(b)
  d=a.t.copy()
  for m,c in b.t.items():d[m]=d.get(m,0)+c
  return Poly({m:c for m,c in d.items() if c})
 __radd__=__add__
 def __neg__(a):return Poly({m:-c for m,c in a.t.items()})
 def __sub__(a,b):return a+-b if isinstance(b,Poly) else a+(-b)
 def __rsub__(a,b):return -a+b
 def __mul__(a,b):
  if not isinstance(b,Poly):b=Poly(b)
  out={}
  for m,c in a.t.items():
   for n,d in b.t.items():
    ex=dict(m)
    for k,e in n:ex[k]=ex.get(k,0)+e
    p=tuple(sorted(ex.items()));out[p]=out.get(p,0)+c*d
  return Poly({m:c for m,c in out.items() if c})
 __rmul__=__mul__
 def __pow__(a,n):
  req(type(n)==int and n>=0,'power');b=Poly(1)
  for _ in range(n):b=b*a
  return b
 def deg(a):return max((sum(e for n,e in m if n in VARIABLES) for m in a.t),default=-1)
 def top(a):
  d=a.deg();return Poly({m:c for m,c in a.t.items() if sum(e for n,e in m if n in VARIABLES)==d})
 def wire(a):return [{'powers':dict(m),'coefficient':str(c)} for m,c in sorted(a.t.items())]

def expr(text,env):
 def rec(n):
  if isinstance(n,ast.Expression):return rec(n.body)
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.Constant):return Poly(n.value)
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -rec(n.operand)
  if isinstance(n,ast.BinOp):
   a=rec(n.left)
   if isinstance(n.op,ast.Pow):return a**n.right.value
   b=rec(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
  raise ValueError(ast.dump(n))
 return rec(ast.parse(text,mode='eval'))

def definitions(free,center):
 return [
 ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),
 ('W','12*w+4'),('X','q*W'),('Y','v' if free else 'q*v'),('E','X*Y'),('a','E+Y'),
 ('H','4*a+3'),('Delta','a*a+4*a+3'),('A','a+2'),
 ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('k','R+1+h*E'),('c2','c*c'),('Yk','Y*k'),('eta','c-Y*k'),
 ('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),
 ('base_budget','k*k*(q*q-Derr)-4*q*q*eta*eta'),
 ('q3','q*q*q'),('Yeta','Y*eta'),('kq3','k*q**3'),
 ('Budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**8' if free else 'k*k*(q*q-Derr)-4*q*q*eta*eta'),
 ('ell','X*Y*Y'),('L','X*Y*Y*k'),('Dt','1+L*(L+k)'),('Dguard','Budget-4'),('Pg','Dt*s'),
 ('P','Dt+(Budget-4)*Dt*Dt*s*s'),('Dm','1+Delta*c*c'),('rDm','r*Dm'),
 ('B','r*A*Dm'),('U','r*c*c*Dm'),('AU','A*U'),('strong','Delta*c*c*AU'),
 ('Df','1+strong'),('Q','Delta*strong'),('delta','Q-1'),('b','c-R+4*A*U*T'),
 ('V','Df*b-c'),('Cy','Q*V*V-1'),('K','X*(3*c-2*X)+2'),
 ('qscale','q**3' if free else 'q*q'),('M','2*qscale'),('Dcar','H*M'),('M2','M*M'),('M4','M**4'),
 ('Dcar2','Dcar*Dcar'),('Dcar3','Dcar**3'),('S','s*r*H*M**5'),('S2','S*S'),
 ('zc','H*M*T+M*K+H*(v-qscale)'),('zc2','zc*zc'),('Ac','(zc*zc+3*Dcar*Dcar)*(zc**3-19*Dcar**3)')
 ]+([] if center=='none' else [('lam','(2*Delta+1)*U' if center=='sharp' else '2*A*A*U'),('shift','lam*V')])+[
 ('Z','S*n-Ac' if center=='none' else 'S*(n+shift)-Ac'),('Z2','Z*Z'),('pa','delta*Z*Z'),('pb','delta*S*S*P'),('pc','4*S*S*B*Df*Cy'),('inner','pa+pb-pc'),('output','inner*inner-4*pa*pb')]

def local_audit(p):
 ns=p['nodes'];names={**p['named_registers'],'output':p['output']}
 aliases={};covered=set();proof=[]
 for i,node in enumerate(ns):
  if node[0] in ('variable','coefficient'):aliases[i]=Poly.var(node[1])
 for name,formula in definitions(p['free_y'],p['center']):
  if name not in names:continue
  node=names[name]
  env={n:Poly.var(n) for n in VARIABLES+PORTS}
  env.update({n:Poly.var(n) for n in names})
  expected=expr(formula,env)
  # Expand to exactly the referenced previously verified registers. This
  # prevents an unverified/self-named cut from laundering a wrong subgraph.
  refs={n.id for n in ast.walk(ast.parse(formula,mode='eval')) if isinstance(n,ast.Name)}
  cuts={}
  for ref in refs:
   ids=[i for i,row in enumerate(ns) if row[0] in ('variable','coefficient') and row[1]==ref]
   idx=ids[0] if ids else names[ref]
   req(idx in aliases,'reference must already be verified: '+ref)
   val=Poly.var(ref)
   if idx in cuts:req(cuts[idx].t==val.t,'ambiguous local alias')
   cuts[idx]=val
  memo={}
  def visit(i):
   covered.add(i)
   if i in cuts:return cuts[i]
   if i in memo:return memo[i]
   row=ns[i]
   if row[0]=='integer':ans=Poly(row[1])
   else:
    req(row[0] in ('add','sub','mul'),'unexpected unbound leaf for '+name+': '+repr(row))
    a,b=visit(row[1]),visit(row[2]);ans=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
   memo[i]=ans;return ans
  actual=visit(node);req(actual.t==expected.t,'definition failed: '+name)
  aliases[node]=Poly.var(name);proof.append(name)
 req(all(i in covered for i,row in enumerate(ns) if row[0] in ('add','sub','mul')),'uncovered arithmetic gate')
 return proof

def identities():
 a={n:Poly.var(n) for n in 'A B U V S W P d'.split()};A,B,U,V,S,W,P,d=[a[n] for n in a]
 D=A*A-1;BF=B+D*A*A*U*U;cy=(d+1)*V*V-1
 records=[]
 for center in ['sharp','simple']:
  lam=(2*D+1)*U if center=='sharp' else 2*A*A*U
  diff=U*U-4*B if center=='sharp' else 4*A*A*U*U-4*B
  req(not (lam*lam-4*BF-diff).t,'center identity')
  z=W+S*lam*V
  raw=d*z*z+d*S*S*P-4*S*S*BF*cy
  cut=d*W*W+2*d*S*lam*V*W+d*S*S*P+S*S*((d*diff-4*BF)*V*V+4*BF)
  req(not (raw-cut).t,'whole inner identity');records.append(center)
 A,c,r,b=[Poly.var(n) for n in 'A c r b'.split()];D=A*A-1;Dm=1+D*c*c;B=r*A*Dm;U=r*c*c*Dm;F=1+D*c**4*B;Q=D*D*c**4*B;V=F*b-c;Cy=Q*V*V-1;Da=(Q-1)*Cy
 req(not (A*U-c*c*B).t,'strong rescaling identity')
 req(not (B*F-B-D*A*A*U*U).t,'BF identity')
 L=Q*b*(V-c)+D*c*c
 req(not (Cy+Dm-F*L).t,'remainder Cy')
 req(not (Da-A*A*Dm-F*(D*F*L-D*Dm-A*A*L)).t,'remainder Da')
 req(not (Da-1-Q*((Q-1)*V*V-1)).t,'Da modulo B')
 # Four conjugates expanded in the rank-four radical algebra.
 z,x,y=[Poly.var(n) for n in ['z','x','y']];acc={0:Poly(1)}
 for sx in [-1,1]:
  for sy in [-1,1]:
   nxt={}
   for i,v in acc.items():
    for j,w in {0:z,1:Poly(sx),2:Poly(sy)}.items():
     val=v*w
     if (i&j)&1:val=val*x
     if (i&j)&2:val=val*y
     nxt[i^j]=nxt.get(i^j,Poly())+val
   acc={i:v for i,v in nxt.items() if v.t}
 req(set(acc)=={0} and acc[0].t==((z*z+y-x)**2-4*z*z*y).t,'four-root norm')
 return {'centers':records,'cofactor_and_coprimality_identities':True,'full_four_factor_norm':True}

def leading(p):
 values=[];ledger=[];names=p['named_registers']
 def get(n):return values[names[n]]
 for i,row in enumerate(p['nodes']):
  if p['center']!='none' and i==names['inner']:
   W=(get('S')*Poly.var('n')-get('Ac')).top()
   diff=get('U')**2-4*get('B') if p['center']=='sharp' else 4*get('A')**2*get('U')**2-4*get('B')
   val=(get('delta')*W**2+2*get('delta')*get('S')*get('lam')*get('V')*W+get('delta')*get('S')**2*get('P')+get('S')**2*((get('delta')*diff-4*get('B')*get('Df'))*get('V')**2+4*get('B')*get('Df'))).top()
   expect=get('S')**2*get('Q')*get('U')**2*get('V')**2
   if p['center']=='simple':expect=4*expect*get('A')**2
   req(val.t==expect.t,'center unique complete highest form')
  elif row[0] in ('variable','coefficient'):val=Poly.var(row[1])
  elif row[0]=='integer':val=Poly(row[1])
  else:
   a,b=values[row[1]],values[row[2]];val=(a*b if row[0]=='mul' else a+b if row[0]=='add' else a-b).top()
  req(val.t,'uncertified complete top cancellation at gate '+str(i))
  # Group formal coefficient-port terms by the actual unknown monomial.
  grouped=collections.defaultdict(list)
  for m,c in val.t.items():grouped[tuple((n,e) for n,e in m if n in VARIABLES)].append(c)
  req(all(all(c>0 for c in cs) or all(c<0 for c in cs) for cs in grouped.values()),'unproved numeric-port cancellation')
  values.append(val);ledger.append({'node':i,'exact_degree':val.deg(),'whole_highest_homogeneous_form':val.wire()})
 out=values[p['output']];req(out.deg()==p['exact_degree'],'exact degree mismatch');req(len(out.t)==1,'top not monomial')
 return {'exact_degree':out.deg(),'highest_homogeneous_form':out.wire(),'all_gate_ledger':ledger}

def topology(p):
 ns=p['nodes'];req(p['coefficient_binding']=='coefficients/BINDING.json','coefficient binding path');req(p['variables']==VARIABLES and p['variable_count']==11 and p['domain']=='unrestricted integers','variable/domain metadata')
 leaves=collections.defaultdict(list);counts=collections.Counter();bound=[]
 for i,row in enumerate(ns):
  if row[0] in ('add','sub','mul'):
   req(len(row)==3 and all(type(x)==int and 0<=x<i for x in row[1:]),'invalid topology');counts[row[0]]+=1
   bound.append(bound[row[1]]+bound[row[2]] if row[0]=='mul' else max(bound[row[1]],bound[row[2]]))
  else:
   req(len(row)==2 and row[0] in ('variable','coefficient','integer'),'invalid leaf');leaves[row[0]].append(row[1]);bound.append(int(row[0]=='variable'))
 req(leaves['variable']==VARIABLES and leaves['coefficient']==PORTS,'exact live leaves')
 req(all(type(x)==int for x in leaves['integer']),'non-integer leaf')
 seen=set()
 def visit(i):
  if i in seen:return
  seen.add(i)
  if ns[i][0] in counts:
   for j in ns[i][1:]:visit(j)
 visit(p['output']);req(len(seen)==len(ns),'dead node')
 req(dict(counts)==p['operation_counts'] and sum(counts.values())==p['operations'],'operation count')
 req(bound[p['output']]==p['syntactic_degree_bound'],'syntactic bound')
 return {'nodes':len(ns),'counts':dict(counts),'operations':sum(counts.values())}

def coefficients():
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());vals={};payloads={}
 req(set(binding['payloads'])==set(PORTS),'exact six payloads')
 for name,record in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/record['file']).read_bytes());v=int.from_bytes(raw,'little')
  req(v>0 and len(raw)==record['raw_bytes'] and v.bit_length()==record['bits'],'numeral size');req(raw[-1]!=0 and sha(raw)==record['raw_sha256'],'minimal authenticated numeral')
  vals[name]=v;payloads[name]={'bits':v.bit_length(),'bytes':len(raw),'raw_sha256':sha(raw)}
 # Independent reconstruction of the entire coefficient tuple from the literal machine.
 actions=[]
 raw=(ROOT/'coefficients/recipe/k215.tm').read_bytes();req(sha(raw)=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090','machine pin')
 for ln in raw.decode().splitlines():
  if ln and not ln.startswith('#'):
   q,b,w,m,t=ln.split();actions.append((int(q),int(b),int(w),m,int(t)))
 req(len(actions)==430 and len({(a,b) for a,b,_,_,_ in actions})==430,'machine action total')
 right=sorted({t for _,_,_,m,t in actions if m=='R'});left=sorted({t for _,_,_,m,t in actions if m=='L'})
 rs={q:i+6 for i,q in enumerate(right)};ls={q:i+205 for i,q in enumerate(left)};hd=lambda q,b:2*q+2+b
 tile=set()
 for q,b,w,m,t in actions:tile.add((0,hd(q,b),rs[t],w) if m=='R' else (ls[t],hd(q,b),0,w))
 for b in (0,1):
  tile.update([(0,hd(215,b),0,hd(215,b)),(0,b,0,b)])
  for q in right:tile.add((rs[q],b,0,hd(q,b)))
  for q in left:tile.add((0,b,ls[q],hd(q,b)))
 tile.update((0,n,0,438) for n in (0,1,432,433));tile.update([(2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)])
 tile.update((1,438,1,n) for n in (434,435,436));tile.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
 start,bad=(2,435,3,1),(5,0,0,0);tile.add(bad);ordered=[start,bad]+sorted(tile-{start,bad})
 req(len(ordered)==943 and [list(t) for t in ordered]==json.loads((ROOT/'coefficients/recipe/wang943_tiles.json').read_text()),'exact full tile list')
 weight=lambda j:1<<(10+2*j);c={}
 for i,t in enumerate(ordered):c[i]=1+sum(weight(10*k+j) for k,x in enumerate(t) for j in range(10) if ((x+512)>>j)&1)+sum(weight(j) for j in range(40,44))
 for k,o in enumerate((1020,1000,980,960)):
  for j in range(10):c[o+2*j]=weight(10*k+j)
 for j,e in enumerate((1095,1096,2195,3296)):c[e]=weight(40+j)
 c[1063]=c[1064]=0;E=set(c);req(len(E)==989,'native support')
 b,L=121,8801;d=b*L;B=1<<d;rho=1<<b
 DC=sum(rho**e for e in (40,41,1100,2200))+sum(v*(rho**(4393-e)+rho**(5495-e)) for e,v in c.items())
 MC=B-1-sum(rho**e for e in E if e!=1)-2*rho**1063
 mu=1022+sum(weight(j) for j in range(44));pad=(2**119-1)*sum(rho**e for e in range(8792,8799))+(2**27-1)*rho**8799
 MF=4+mu*(rho**4393+rho**5495)+sum(rho**(1000+2*j)+rho**(1021+2*j) for j in range(10))+rho**2195+rho**3296+pad
 rebuilt={'beta':B-1,'K0':DC+B*rho,'MC':MC,'MF':MF+B-1,'cone_A':1<<1113,'cone_B':1<<666104}
 req(rebuilt==vals,'complete joint numerical tuple mismatch')
 req((MC%4,MF%8,MC.bit_count(),MF.bit_count())==(2,4,d-989,989),'native masks')
 return {'whole_joint_tuple_rebuilt':True,'all_943_tiles_rebuilt_from_430_actions':True,'MF_already_shifted':True,'payloads':payloads}

def main():
 manifest=json.loads((ROOT/'RELEASE_WHITELIST.json').read_text());req(len(manifest['files'])==131,'release file count')
 for n,r in manifest['files'].items():
  path=pathlib.Path(n);req(not path.is_absolute() and '..' not in path.parts,'unsafe closure path');raw=(ROOT/path).read_bytes();req(len(raw)==r['bytes'] and sha(raw)==r['sha256'],'release pin '+n)
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for n,r in pins['dependencies'].items():
  raw=(ROOT/n).read_bytes();req(len(raw)==r['bytes'] and sha(raw)==r['sha256'],'source pin '+n);req(n in manifest['files'],'source omitted from portable release')
 answer={'status':'PASS','new_independent_auditor':True,'producer_checker_recipe_not_imported':True,'release_files':len(manifest['files']),'source_dependencies':len(pins['dependencies']),'identities':identities(),'coefficients':coefficients(),'equations':[]}
 for path in sorted(ROOT.glob('*cofactor11_*.json')):
  p=json.loads(path.read_text());entry={'name':p['name'],'sha256':sha(path.read_bytes()),'topology':topology(p),'verified_definitions':local_audit(p),'leading':leading(p)};answer['equations'].append(entry)
 mutations=[]
 sample=json.loads((ROOT/'free_cofactor11_sharp.json').read_text())
 for name in ['Dguard','B','strong','pc','lam','inner','Y','P','V','zc','Ac','Q']:
  mutant=copy.deepcopy(sample);idx=mutant['named_registers'][name];row=mutant['nodes'][idx]
  if row[0] in ('variable','coefficient'):row[1]='unauthorized'
  else:row[0]='sub' if row[0]=='add' else 'add'
  try:topology(mutant);local_audit(mutant);leading(mutant)
  except (ValueError,KeyError):mutations.append(name)
  else:raise ValueError('accepted mutation '+name)
 for field in ['exact_degree','operations','variable_count']:
  mutant=copy.deepcopy(sample);mutant[field]+=1
  try:topology(mutant);local_audit(mutant);leading(mutant)
  except (ValueError,KeyError):mutations.append(field)
  else:raise ValueError('accepted metadata mutation')
 answer['rejected_mutations']=mutations
 results=json.loads((ROOT/'RESULTS.json').read_text())
 byname={e['name']:e for e in answer['equations']}
 for record in results['recommended_points']:
  e=byname[record['name']];top=e['leading']['highest_homogeneous_form'][0];powers=dict(top['powers']);beta=powers.pop('beta',0);claimed=record['actual_attained_coefficient']
  req(beta==claimed['beta'] and int(top['coefficient'])==claimed['sign']*math.prod(int(p)**v for p,v in claimed['powers'].items()),'actual leading coefficient receipt')
  req(all(powers.get(n,0)==v for n,v in record['attained_monomial'].items()),'attained monomial receipt')
  req(e['leading']['exact_degree']==record['exact_degree'] and e['topology']['operations']==record['operations'] and e['sha256']==record['graph_sha256'],'recommended metrics receipt')
 answer['all_recommended_result_receipts_independently_verified']=True
 target=OUT/('AUDIT_OPTIMIZED.json' if not __debug__ else 'AUDIT.json');target.write_text(json.dumps(answer,indent=2)+'\n')
 print(json.dumps({'status':'PASS','files':131,'coefficients':'independently rebuilt','points':[{k:v for k,v in {'name':e['name'],'degree':e['leading']['exact_degree'],'operations':e['topology']['operations'],'nodes':e['topology']['nodes']}.items()} for e in answer['equations']],'mutations':mutations},indent=2))
if __name__=='__main__':main()
