#!/usr/bin/env python3
import gzip,hashlib,itertools,json,subprocess,sys
from collections import Counter,defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-ordinary-pair88-46'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'7eb64d753de683c77e67b5e178568facecaba705ead604b7107e9b1610f6a70a','check.py':'5cfcbbf26f3fd4511bb9d3b36c5b2822c2d015c211e4bc4d7b5c88362cad2ed9','freej88.json':'fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb','p73_90.json':'7e230b399dc47497fa18c245bd043fb77adbe37cf0808ec4fb18fe75eaf17f48','result.json':'7bcfc0315c48a258be2d293b629980f1c80716af1952699759ee006f0ff44182'}.items():assert sha(p/n)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement';p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'; paths=[(p115/'circuits/positive13_87_degree51.json','24b9120cc07693ba3fab0bff254c071fae800d14415850c3411651c026e28f0c'),(p115/'coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'),(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(base/'research/ordinary-unit-products/p13_ordinary_degree51.json','c9f5f495249ed13d30393fec5838a85408889d214d2253615f4ba6f60414cf71'),(base/'research/ordinary13-p73-conditional-pair90-54/polynomial.json','3946b8c328d692e829d1f556ffcf78cc559e885f3715ee3509f241f4e75c47c0'),(base/'reviews/ordinary13-p73-conditional-pair90-54-independent/check.py','f73239adb431450a7618f42dd2f61eb80a0a116847e2d75806c901da58d097a9')]
for q,h in paths:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(paths[-1][0])],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
g87=json.loads(paths[0][0].read_text()); b115=json.loads(paths[1][0].read_text());b72=json.loads(paths[2][0].read_text());orig90=json.loads(paths[3][0].read_text());norm54=json.loads(paths[4][0].read_text());g88=json.loads((p/'freej88.json').read_text());g90=json.loads((p/'p73_90.json').read_text())
assert g87['witnesses']==g88['witnesses'] and g87['fixed_numerals']==g88['fixed_numerals'] and g88['witnesses'][0]=='J'
assert norm54['witnesses']==g90['witnesses']==orig90['witnesses'] and norm54['fixed_numerals']==g90['fixed_numerals']==orig90['fixed_numerals'] and g90['witnesses'][0]=='j'
assert g87['source'][-6:]==[['F0','+',1,'A0'],['F1','+',1,'A1'],['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
r=[]
for row in g87['source'][:-6]:r.append(['g80','+','g78','V'] if row[0]=='g80' else ['g81','*','u','g80'] if row[0]=='g81' else row)
r.extend([['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['pair','*','Fa','Fs'],['pairm','-','pair',1],['pair2','*','pairm','pairm'],['sum01','+','A0sq','A1sq'],['out','+','sum01','pair2']]);assert r==g88['source']
assert g90['source']==[['g72','-','g71','Kaux'] if r[0]=='g72' else ['Fs','+',1,'g72'] if r[0]=='Fs' else r for r in norm54['source']]
source={r[0]:r for r in g87['source']}
for row in [['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['Fs','+',1,'g72'],['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Q','g81'],['Fa','-','y2','g82']]:assert source[row[0]]==row
# Independently evaluate P73 ordinary parent and proposed graph on common
# symbolic cuts; this does not identify free-J's J with P73's j.
def atom(s):return {(s,):1}
def add(a,b,s=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
cuts={x:atom(x) for x in ('q3','qm','k','ell','r','Y','Bt','Dstar','U','Delta','c2','V','u','I')};cuts['Q']=atom('Q');cuts['Kaux']=cuts['Q']
def evaluate(g):
 v=dict(cuts)
 def ev(x):return ({():x} if x else {}) if type(x)==int else v.get(x)
 for n,op,a,b in g['source']:
  if n in v:continue
  A,B=ev(a),ev(b)
  if A is not None and B is not None:v[n]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return v
v0,v1=evaluate(orig90),evaluate(g90)
for x,y in [('A0','A0'),('A1','A1'),('Fa','g83'),('Fs','Fs')]:assert v0[x]==v1[y],(x,y)
# Exhaustive residues support the general argument, including arbitrary ports.
for a,f,i,v,y in itertools.product(range(4),repeat=5):
 D=(a*a+4*a+3)%4;Q=D*(f*f-1)%4;Fa=(y*y-Q*(y*y-v*v))%4;Fs=(1+i*i-Q)%4;assert Q in (0,1) and Fa in (0,1) and Fs in (0,1,2)
for q,Z in itertools.product(range(4),repeat=2):
 M=q**3*(q-1);assert M%2==0 and (1+Z*Z-M*M)%4!=3
for a,c,U,Dstar in itertools.product(range(4),repeat=4):
 delta=(a*a+4*a+3)%4;assert (1+Dstar*Dstar-U*U*(1+delta*c*c))%4!=3
P=1000000007;assert all(P%d for d in range(2,int(P**.5)+1));fixed={};assert set(b72['ports'])==set(b115['ports'])=={'beta','K0','MC','MF'}
for n,m in b72['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 packed=(p72/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==m['bits'];fixed[n]=x%P
# Different weighted affine ray and syntactic degrees, separately for each encoding.
def ap(a,b,s):
 out=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(out)>1 and not out[-1]:out.pop()
 return out
def mp(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%P
 while len(out)>1 and not out[-1]:out.pop()
 return out
leaders={}
for label,g,N,Fa in [('freej88',g88,88,'Fa'),('p73_90',g90,90,'g83')]:
 rows=g['source'];assert len(rows)==N and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
 have=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']});val={x:[i+2,i+1] for i,x in enumerate(g['witnesses'])};val.update({x:[n] for x,n in fixed.items()})
 for n,op,a,b in rows:
  assert n not in have and all(type(x)==int or x in have for x in (a,b));d=lambda x:0 if type(x)==int else deg[x];A=[a%P] if type(a)==int else val[a];B=[b%P] if type(b)==int else val[b];deg[n]=d(a)+d(b) if op=='*' else max(d(a),d(b));val[n]=mp(A,B) if op=='*' else ap(A,B,1 if op=='+' else -1);have.add(n)
 need={g['output']}
 for n,op,a,b in reversed(rows):
  if n in need:need.update((a,b))
 assert all(n in need for n,_,_,_ in rows) and set(g['witnesses']+g['fixed_numerals'])<=need
 assert deg[Fa]==13 and deg['Fs']==10 and deg[g['output']]==46 and len(val[g['output']])==47 and val[g['output']][-1]!=0
 assert Counter(r[1] for r in rows)==({'*':48,'+':23,'-':17} if label=='freej88' else {'*':49,'+':25,'-':16});leaders[label]=val[g['output']][-1]
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'graphs':{'freej88':[88,46],'p73_90':[90,46]},'weighted_ray_leaders':leaders,'prime':P,'scope':'External integer-zero and graph/degree checks with separate encodings; no Lean, internal file binding, foundational replay or global frontier claim.'},indent=2))
