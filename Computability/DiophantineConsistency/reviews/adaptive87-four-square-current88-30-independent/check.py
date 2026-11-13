#!/usr/bin/env python3
"""Independent finite checks; this does not run Lean or prove provider ancestry."""
import gzip, hashlib, itertools, json, resource, sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode): raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2)); resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def require(p,m):
 if not p:raise RuntimeError(m)
pins=json.loads((here/'pins.json').read_bytes())
for p,h in pins.items():require(sha((r/p).read_bytes())==h,'pin '+p)
def obj(p):return json.loads((r/p).read_bytes())
parent=obj('research/adaptive-first-root-factor87/candidate.json');child=obj('research/adaptive87-four-square-current88-30/graph.json')
pr=parent['source'];cr=child['source'];rows={row[0]:row for row in pr}
removed={'Fs','F0','F1','g86','g87','g88','P13'}
tail=[['fa_minus','-','Fa',1],['a0_sq','*','A0','A0'],['a1_sq','*','A1','A1'],['fa_sq','*','fa_minus','fa_minus'],['strong_sq','*','g72','g72'],['sum0','+','a0_sq','a1_sq'],['sum1','+','sum0','fa_sq'],['output','+','sum1','strong_sq']]
require(cr==[x for x in pr if x[0] not in removed]+tail,'complete row cut')
require(parent['witnesses']==child['witnesses'] and parent['fixed_numerals']==child['fixed_numerals'],'coordinate and port equality')
expected=[['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['g38','*','Z','Z'],['g39','*','M','M'],['g30','+','ell','k'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['g71','*','I','I'],['g72','-','g71','Q'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Q','g81'],['Fa','-','y2','g82'],['Fs','+',1,'g72'],['F0','+',1,'A0'],['F1','+',1,'A1'],['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
for x in expected:require(rows.get(x[0])==x,'factor row '+x[0])
known=set(child['witnesses']+child['fixed_numerals']);back={}
for out,op,a,b in cr:
 require(out not in known and op in '+-*' and all(type(t)==int or t in known for t in (a,b)),'topology')
 back[out]=(a,b);known.add(out)
seen=set();leaves=set();stack=[child['output']]
while stack:
 n=stack.pop()
 if n in back:
  if n not in seen:seen.add(n);stack.extend(t for t in back[n] if isinstance(t,str))
 else:leaves.add(n)
require(len(seen)==88 and len(child['witnesses'])==13 and set(child['witnesses']+child['fixed_numerals'])<=leaves,'liveness')
counts={o:sum(row[1]==o for row in cr) for o in '*+-'};require(counts=={'*':48,'+':22,'-':18},'counts')
# Independently exhaust arbitrary residues of the algebraic parameters. Negative integers are covered modulo four.
allvals=set(range(4));n=[0,0,0,0]
for q,z,h in itertools.product(allvals,repeat=3):
 require((1+z*z-(q**3*(q-1))**2*h)%4!=3,'first');n[0]+=1
for a,u,c,d in itertools.product(allvals,repeat=4):
 require((1+d*d-u*u*(1+(a*a+4*a+3)*c*c))%4!=3,'main');n[1]+=1
for a,f,v,y in itertools.product(allvals,repeat=4):
 Q=(a*a+4*a+3)*(f*f-1);require((y*y-Q*(y*y-v*v))%4!=3,'aux');n[2]+=1
for a,f,i in itertools.product(allvals,repeat=3):
 require((1+i*i-(a*a+4*a+3)*(f*f-1))%4!=3,'strong');n[3]+=1
# A product of four integer units is 1 only when every factor is ±1; their mod-4 exclusions force +1.
for units in itertools.product((-1,1),repeat=4):
 if all(x%4!=3 for x in units):require(units==(1,1,1,1),'unit argument')
meta=obj('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json')['coefficient_binding']['ports'];mod=1000000007;ports={}
for name,m in meta.items():
 blob=(r/'candidates/one-page-padding-staircase-carrier65-2011/coefficients'/m['file']).read_bytes();raw=gzip.decompress(blob);x=int.from_bytes(raw,'big')
 require(sha(blob)==m['gzip_sha256'] and sha(raw)==m['raw_sha256'] and len(raw)==m['raw_bytes'] and x.bit_length()==m['bits'],'port '+name);ports[name]=x%mod
 other=obj('research/adaptive-current13-metrics/polynomial.json')['coefficient_binding']['ports'][name]
 other_raw=gzip.decompress((r/'research/adaptive-current13-metrics/coefficients'/other['file']).read_bytes())
 require(other_raw==raw and sha(other_raw)==other['raw_sha256'],'88 port equality '+name)
# Independently evaluate all gates on the diagonal in F_p[t].
def add(x,y,sign):return [((x[i] if i<len(x) else 0)+sign*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))]
def mul(x,y):
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return z
def norm(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
d={n:[0,1] for n in child['witnesses']};d.update({k:[v] for k,v in ports.items()})
def val(x):return d[x] if isinstance(x,str) else [x%mod]
for out,op,a,b in cr:
 x,y=val(a),val(b);d[out]=norm(mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1))
require(len(d['output'])==31 and d['output'][30]==750827028,'degree 30 diagonal')
require([len(d[k])-1 for k in ('A0','A1','Fa','g72')]==[15,13,13,10],'diagonal factor degrees')
print(json.dumps({'scope':'independent finite graph, byte and mod-4 checks; inherited symbolic degree certificate; no Lean','graph_sha256':pins['research/adaptive87-four-square-current88-30/graph.json'],'live_gates':len(seen),'counts':counts,'mod4_cases':n,'port_bytes':sum(v['raw_bytes'] for v in meta.values()),'degree30_diagonal_mod_1000000007':d['output'][30],'pins_sha256':sha((here/'pins.json').read_bytes())},sort_keys=True,indent=2))
