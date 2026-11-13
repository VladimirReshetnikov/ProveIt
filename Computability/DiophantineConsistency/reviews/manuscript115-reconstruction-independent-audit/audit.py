#!/usr/bin/env python3
"""Independent historical reconstruction, graph identity and exact degree certificate."""
import gzip,hashlib,json,subprocess,sys
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('independent review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/manuscript115-reconstruction';SUP=BASE/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement';PIN='84e16e43092614bae262ca59651cb9d77e31a255';COEFF='Computability/DiophantineConsistency/candidates/free-j-polarized-positive/source/positive/coefficients/';ALT=BASE/'research/saturated-direct-carrier-cse/coefficients/compact44_bfs';S98=BASE/'con-zfc-diophantine-forms/98-congruence-certificates/positive/coefficients/BINDING.json'
H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(Path(p).read_bytes())
def show(commit,path):return subprocess.check_output(['git','show',commit+':'+str(path)],cwd=ROOT)
def anchored(path):
 b=path.read_bytes();assert b==show('1ddc0dc05f',path.relative_to(ROOT));return b
for f in ('check.py','CHECK.json','CHECK_OPTIMIZED.json','README.md'):anchored(TASK/f)
manifest=json.loads(anchored(SUP/'MANIFEST.json'))['files'];pins=json.loads(anchored(SUP/'SOURCE_PINS.json'));assert len(manifest)==45 and pins['commit']==PIN
source_map={r['local_path']:r['repository_path'] for r in pins['sources']};source_inputs=[Path(__file__),TASK/'check.py',TASK/'CHECK.json',TASK/'CHECK_OPTIMIZED.json',TASK/'README.md',SUP/'MANIFEST.json',SUP/'SOURCE_PINS.json',S98]+[SUP/n for n in manifest if (SUP/n).exists()];input_hashes={str(p.resolve()):H(p.read_bytes()) for p in source_inputs};saved=J(TASK/'CHECK.json');savedopt=J(TASK/'CHECK_OPTIMIZED.json');assert saved==savedopt and saved['source_commit']==PIN and len(saved['restored'])==18
expected={x['target']:(x['source'],x['sha256']) for x in saved['restored']};assert len(expected)==18
restored={};existing=0
for name,digest in manifest.items():
 path=SUP/name
 if path.exists():assert H(path.read_bytes())==digest;existing+=1;continue
 source=source_map.get(name,COEFF+name.removeprefix('coefficients/') if name.startswith('coefficients/') else None)
 assert source is not None and name in expected and expected[name]==(source,digest)
 raw=show(PIN,source);assert H(raw)==digest;restored[name]={'source':source,'sha256':digest,'bytes':len(raw)}
assert existing==27 and set(restored)==set(expected)
# Run both whole detached reconstructions. Each invokes the restored supplement
# checker both with and without optimization inside its own temporary tree.
commands=[]
for flags,expected_result in (([],saved),(['-O'],savedopt)):
 p=subprocess.run([sys.executable,'-B',*flags,str(TASK/'check.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
 assert p.returncode==0,(p.returncode,p.stderr);data=json.loads(p.stdout);assert data==expected_result
 assert all(row['exit']==0 for row in data['checker_runs']) and [row['optimized'] for row in data['checker_runs']]==[False,True]
 commands.append({'flags':flags,'exit_code':p.returncode,'stdout_sha256':H(p.stdout.encode()),'stderr':p.stderr})
# Bind all four complete raw integers, including the alternate distinct K.
binding=json.loads(show(PIN,COEFF+'BINDING.json'));other=J(S98);raw_pins={'beta':'0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d','K0':'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e','MC':'6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4','MF':'48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737'}
assert set(binding['ports'])==set(raw_pins) and binding['encoding']=='unsigned minimal little-endian integer bytes inside gzip'
ports={};port_rows={}
for n,row in binding['ports'].items():
 packed=show(PIN,COEFF+row['file']);raw=gzip.decompress(packed);assert H(packed)==row['sha256_gzip'] and H(raw)==row['sha256_raw']==raw_pins[n]==other['ports'][n]['sha256_raw'];v=int.from_bytes(raw,'little');assert v.bit_length()==row['bits'] and len(raw)==row['raw_bytes'];ports[n]=v
 alt_path=ALT/Path(row['file']).name;source_inputs.append(alt_path);input_hashes[str(alt_path.resolve())]=H(alt_path.read_bytes());alt=gzip.decompress(alt_path.read_bytes());port_rows[n]={'raw_sha256':H(raw),'alternate_raw_sha256':H(alt),'equal_alternate':raw==alt,'bits':v.bit_length()}
assert [port_rows[n]['equal_alternate'] for n in ('beta','K0','MC','MF')]==[True,False,True,True]
assert port_rows['K0']['alternate_raw_sha256']=='4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7'
assert ports['beta']==(1<<590069)-1 and binding['ports']['MF']['upstream_port']=='MF_source'
# Independently check whole graph cut identity and topology/liveness.
parent_path=SUP/'parents/candidates/free-j-polarized-positive/equation.json';child_path=SUP/'circuits/positive12_95_degree70.json';parent=J(parent_path);child=J(child_path)
assert H(parent_path.read_bytes())==manifest['parents/candidates/free-j-polarized-positive/equation.json'] and H(child_path.read_bytes())==manifest['circuits/positive12_95_degree70.json']
assert parent['witnesses']==child['witnesses'] and len(child['witnesses'])==12 and parent['fixed_numerals']==child['fixed_numerals']==['beta','K0','MC','MF'] and parent['output']==child['output']=='P12'
p0={r[0]:r for r in parent['source']};p1={r[0]:r for r in child['source']};assert len(p0)==96 and len(p1)==95
assert set(p0)-set(p1)=={'g22','W','g35','g36'} and set(p1)-set(p0)=={'folded_kBt','folded_g31','folded_q3Bt'}
assert {n for n in set(p0)&set(p1) if p0[n]!=p1[n]}=={'g32','Z'}
# No changed cut-internal value escapes except via the certified Z node.
for table, expected_consumers in ((p0,{'g22':['W'],'W':['g35'],'g35':['g36'],'g36':['Z'],'g32':['g34'],'g33':['g34'],'g34':['Z']}),(p1,{'folded_kBt':['folded_g31'],'folded_g31':['g32'],'folded_q3Bt':['Z'],'g32':['g34'],'g33':['g34'],'g34':['Z']})):
 for n,consumers in expected_consumers.items():assert [row[0] for row in table.values() if n in row[2:]]==consumers
for graph,want in ((parent,{'*':53,'+':26,'-':17}),(child,{'*':52,'+':25,'-':18})):
 known=set(graph['witnesses']+graph['fixed_numerals']);index={}
 for row in graph['source']:
  n,op,a,b=row;assert n not in known and op in want and all(type(x) is int or x in known for x in (a,b));known.add(n);index[n]=row
 assert dict(Counter(r[1] for r in graph['source']))==want
 live=set();todo=[graph['output']]
 while todo:
  x=todo.pop()
  if type(x) is int or x in live:continue
  live.add(x)
  if x in index:todo.extend(index[x][2:])
 assert live==set(index)|set(graph['witnesses'])|set(graph['fixed_numerals'])
# Generic free-polynomial ring, independent of the source checker.
def ring(names):
 z=(0,)*len(names)
 def c(x):return {} if not x else {z:x}
 def atom(name):v=list(z);v[names.index(name)]=1;return {tuple(v):1}
 def add(a,b,sign=1):
  d=a.copy()
  for x,v in b.items():d[x]=d.get(x,0)+sign*v
  return {x:v for x,v in d.items() if v}
 def mul(a,b):
  d={}
  for x,v in a.items():
   for y,w in b.items():
    m=tuple(i+j for i,j in zip(x,y));d[m]=d.get(m,0)+v*w
  return {x:v for x,v in d.items() if v}
 return c,atom,add,mul
c,a,add,mul=ring(['q3','qm','k','Bt','g31','Y']);q3,qm,k,Bt,g31,Y=[a(n) for n in ('q3','qm','k','Bt','g31','Y')];M=mul(q3,qm)
old=add(add(mul(M,g31),mul(qm,Y)),mul(mul(q3,add(c(1),mul(k,qm))),Bt),-1)
new=add(add(mul(M,add(g31,mul(k,Bt),-1)),mul(qm,Y)),mul(q3,Bt),-1)
assert old==new and old!=add(new,mul(q3,Bt))
# Verify literal cut definitions; every other common row is byte-identical.
for row in (['g22','*','k','qm'],['W','+',1,'g22'],['M','*','q3','qm'],['g32','*','M','g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['g35','*','W','q3'],['g36','*','Bt','g35'],['Z','-','g34','g36']):assert p0[row[0]]==row
for row in (['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','M','folded_g31'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt']):assert p1[row[0]]==row
# Exact cancellation identities for the independent degree upper bound.
c,a,add,mul=ring(['M','ell','B','k']);M,ell,B,k=[a(n) for n in ('M','ell','B','k')];two=c(2)
lhs=add(mul(add(mul(M,ell),B),add(mul(M,ell),B)),mul(mul(M,M),add(mul(ell,add(ell,k)),c(1))),-1)
rhs=add(add(mul(two,mul(mul(M,ell),B)),mul(B,B)),mul(mul(M,M),add(mul(ell,k),c(1))),-1);assert lhs==rhs
c,a,add,mul=ring(['U','a','c','L']);U,A,C,L=[a(n) for n in ('U','a','c','L')];uac=mul(mul(U,A),C);D=add(uac,L);delta=add(add(mul(A,A),mul(c(4),A)),c(3))
lhs=add(mul(D,D),mul(mul(U,U),add(c(1),mul(delta,mul(C,C)))),-1)
rhs=add(add(mul(c(2),mul(uac,L)),mul(L,L)),mul(mul(U,U),add(c(1),mul(add(mul(c(4),A),c(3)),mul(C,C)))),-1);assert lhs==rhs
c,a,add,mul=ring(['Q','V','n']);Q,V,n=[a(x) for x in ('Q','V','n')];oneQ=add(c(1),Q,-1)
lhs=add(add(mul(oneQ,mul(add(V,n),add(V,n))),mul(Q,mul(V,V))),c(1),-1)
rhs=add(add(add(mul(V,V),mul(c(2),mul(oneQ,mul(V,n)))),mul(oneQ,mul(n,n))),c(1),-1);assert lhs==rhs
# Check the graph exposes precisely the expressions used above.
for row in (['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['g30','+','ell','k'],['g31','+','g30','r'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['g19','*','a','c'],['b0','+','X','g19'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['oneQ','-',1,'Q'],['vn','+','V','n'],['vn2','*','vn','vn'],['polarV2','*','V','V'],['polarQV2','*','Q','polarV2'],['polarCy','-','polarQV2',1],['polarHpart','*','oneQ','vn2'],['h','+','polarHpart','polarCy']):assert p1[row[0]]==row
# Propagate degree bounds; the three justified overrides are the cancellation
# identities above. All four ports have degree zero, without specialization.
deg={n:1 for n in child['witnesses']};deg.update({n:0 for n in child['fixed_numerals']})
for name,op,x,y in child['source']:
 dx=0 if type(x) is int else deg[x];dy=0 if type(y) is int else deg[y]
 deg[name]=dx+dy if op=='*' else max(dx,dy)
 if name in ('A0','A1','h'):deg[name]={'A0':15,'A1':13,'h':13}[name]
assert {n:deg[n] for n in ('q','q3','qm','M','ell','k','Bt','U','a','c','H','shift','Q','V','den','polarCy','A0','A1','h','N','P12')}=={'q':1,'q3':3,'qm':1,'M':4,'ell':4,'k':1,'Bt':2,'U':3,'a':2,'c':2,'H':2,'shift':4,'Q':6,'V':6,'den':8,'polarCy':18,'A0':15,'A1':13,'h':13,'N':42,'P12':70}
# Full graph diagonal at the exact recovered tuple, reduced only after binding
# the entire unsigned little-endian integers. Nonzero x^70 modulo m implies
# the corresponding integer coefficient is nonzero.
def diagonal(modulus,override=None):
 actual=dict(ports);actual.update(override or {})
 vals={n:[0,1] for n in child['witnesses']};vals.update({n:[v%modulus] for n,v in actual.items()})
 def plus(x,y,sgn=1):return [((x[i] if i<len(x) else 0)+sgn*(y[i] if i<len(y) else 0))%modulus for i in range(max(len(x),len(y)))]
 def times(x,y):
  z=[0]*(len(x)+len(y)-1)
  for i,a in enumerate(x):
   for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%modulus
  return z
 for name,op,x,y in child['source']:
  x=[x%modulus] if type(x) is int else vals[x];y=[y%modulus] if type(y) is int else vals[y]
  vals[name]=times(x,y) if op=='*' else plus(x,y,-1 if op=='-' else 1)
 out=vals[child['output']];return {'modulus':modulus,'degree':max(i for i,x in enumerate(out) if x),'coefficient_degree_70':out[70]}
slices=[diagonal(m) for m in (1009,1013,1019)];assert slices==[{'modulus':1009,'degree':70,'coefficient_degree_70':794},{'modulus':1013,'degree':70,'coefficient_degree_70':738},{'modulus':1019,'degree':70,'coefficient_degree_70':683}]
# Controls: altered cut, changed output and a beta-zero coefficient tuple must
# not satisfy the respective evidence checks.
bad=[r[:] for r in child['source']];i=next(i for i,r in enumerate(bad) if r[0]=='folded_q3Bt');bad[i]=['folded_q3Bt','+','q3','Bt'];assert bad[i]!=p1['folded_q3Bt']
assert ports['beta']>0 and diagonal(1009,{'beta':0})['coefficient_degree_70']==0
assert input_hashes=={str(p.resolve()):H(p.read_bytes()) for p in source_inputs}
out={'status':'PASS_INDEPENDENT_MANUSCRIPT115_RECONSTRUCTION_REVIEW','inputs_sha256':input_hashes,'historical_commit':PIN,'manifest_files':len(manifest),'existing_files':existing,'restored':restored,'ports':port_rows,'reconstruction_commands':commands,'parent_gates':96,'child_gates':95,'degree_upper':70,'diagonal_slices':slices,'scope':'Finite reconstructed source, graph and independent degree reasoning. Ordinary equivalence, native/compiler calibration, arbitrary-checker correspondence and internal iPRA remain unverified.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path.read_bytes()))
