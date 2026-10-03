#!/usr/bin/env python3
"""Independent bounded source, clock-map and exact-degree audit; data only."""
import argparse, hashlib, json, random
from pathlib import Path
from collections import Counter
from fractions import Fraction
AUTHOR_PINS={'py': '9627ffd85f79e5ed2c0174f716e95afcf1f92c0f3035e65c76aaa15f98af34b6', 'json': 'a360d1573dfb12b2e5fb3188bdce3a36e7029c4fc13b86b61969f34d2644b7d1', 'md': '59efd3d56b794f8632c1da48c080083a750895e9897bf213662195e45861167c'}
DEPENDENCIES={'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_target_free_height.md': 'f0bd6c2011ca1aa0dd5e6dbaaea7907d35f13f4dd756fc2786528c80f60f75ff', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/20-event-budget-PROOF.md': 'd74157254a36e53c1568cea383cdcc46dd73adca48a1a9a7eee4e46b51b73922', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/15-clean-targets-CLEAN-TARGET-THEOREM.md': '3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-FOLDED-ADDENDUM.md': '1ce912386db479f63eed0d05f2a7d79649b4d8a03b91bf2080338f1cafaafde8', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-THEOREM.md': '93bf673898816aed526ef943160a9d3dfb950cedc3bf0f59d6ae4d78c7add11d'}
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
STEM='three_mass_direct_clean_clock'
NAMES=['clock_incdec','clock_zero3','clock_nop','clock_positive3']
def need(v,s):
 if not v:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def typed(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(typed(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(typed(v,w)for v,w in zip(a,b))
 return a==b

def load(repo,author_root):
 blobs={}
 for n,h in DEPENDENCIES.items():
  b=(repo/n).read_bytes();need(sha(b)==h,'dependency '+n);blobs[n]=b
 authors={}
 for e,h in AUTHOR_PINS.items():
  p=author_root/(STEM+'.'+e);b=p.read_bytes();need(sha(b)==h,'author '+e);authors[e]=b
 a=json.loads(authors['json']);need(a['source_sha256']==AUTHOR_PINS['py'],'author source receipt binding')
 need(typed(a['dependency_pins'],DEPENDENCIES),'full dependency manifest')
 parent=json.loads(blobs[WIP+'/three_mass_target_free_height.json'])
 for n,h in parent['parent_pins'].items():need(DEPENDENCIES[WIP+'/'+n]==h,'every inherited parent pin')
 for stem in ('three_mass_target_free_height','three_mass_unbounded_endpoint_projection','native_pell_factored_first_coefficient'):
  receipt=json.loads(blobs[WIP+'/'+stem+'.json']);need(receipt['source_sha256']==DEPENDENCIES[WIP+'/'+stem+'.py'],'upstream receipt source '+stem)
 need(a['status']=='PASS'and len(a['forms'])==4 and len(parent['forms'])==4,'exact four saved forms')
 return a,parent

def sos(pairs,prefix):
 differences=[[prefix+'res'+str(i),'-',a,b]for i,(a,b)in enumerate(pairs)]
 squares=[[prefix+'sq'+str(i),'*',r[0],r[0]]for i,r in enumerate(differences)]
 out=[]
 for r,s in zip(differences,squares):out.extend((r,s))
 acc=squares[0][0]
 for i in range(1,len(pairs)):
  name=prefix+'sum'+str(i);out.append([name,'+',acc,squares[i][0]]);acc=name
 return out,acc

def expected(parent):
 need(parent['parameters']==['x','y','T']and parent['domains']=={'parameters':'natural','auxiliaries':'positive'},'literal parent domain')
 tail,out=sos(parent['comparisons'],'ep_');need(parent['polynomial_source']==parent['source']+tail and parent['output']==out,'entire paid parent SOS')
 rows=parent['source'];uses=lambda v:[r[0]for r in rows if v in r[2:]]
 need(uses('T')==[parent['interfaces']['height'],rows[-1][0]],'all parent T consumers')
 need([r for r in rows if 'y'in r[2:]]==[['bridge_final_scaled','*',5,'y']],'all parent y consumers')
 need([r for r in rows if r[0]==parent['interfaces']['height']]==[[parent['interfaces']['height'],'+','bridge_height_without_time','T']],'height uses time once')
 need(rows[-3:]==[[rows[-3][0],'-','clock_quotient_hat',1],[rows[-2][0],'*',rows[-2][2],rows[-3][0]],[rows[-1][0],'+',rows[-2][0],'T']],'literal paid clock quotient')
 need(parent['comparisons'][-1]==[rows[-4][0],rows[-1][0]],'literal packed duration endpoint')
 ren=lambda x:{'T':'U','y':'clean_final_payload'}.get(x,x)if type(x)is str else x
 adjusted=[];radix=[]
 for n,op,a,b in rows:
  if a==131072 and op=='*'and b=='bridge_height_square':radix.append(n);a=262144
  adjusted.append([n,op,ren(a),ren(b)])
 need(len(radix)==1,'sole radix literal edit')
 clock=rows[-4][0];bridge=[['clean_payload_sum','+','x','clean_final_payload'],['clean_payload_ticks','*',192,'clean_payload_sum'],['clean_double_clock_word','*',2,clock],['clean_sum','+','clean_double_clock_word','clean_payload_ticks'],['clean_clock_word','+','clean_sum',208]]
 oldpairs=[[ren(a),ren(b)]for a,b in parent['comparisons']]
 newpairs=oldpairs[:-1]+[['clean_clock_word',oldpairs[-1][1]]]
 newtail,out=sos(newpairs,'clean_')
 return dict(source=adjusted+bridge,polynomial_source=adjusted+bridge+newtail,comparisons=newpairs,output=out,parameters=['x','U'],auxiliaries=parent['auxiliaries']+['clean_final_payload'],domains=parent['domains'],mapping=parent['mapping'],interfaces=parent['interfaces']),adjusted,oldpairs,radix[0]

def walk(packet):
 ports=packet['parameters']+packet['auxiliaries'];need(len(ports)==len(set(ports)),'unique ports')
 known=set(ports);defs={};counts=Counter()
 for n,op,a,b in packet['polynomial_source']:
  need(type(n)is str and n not in known and op in ('+','-','*'),'fresh supported row')
  need(all(type(x)is int or type(x)is str and x in known for x in (a,b)),'closed operand')
  defs[n]=(op,a,b);known.add(n);counts['M'if op=='*'else'A']+=1
 live=set();todo=[packet['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in defs:todo.extend(defs[n][1:])
 need(live==known,'complete live closure, every port and gate')
 # Separate recursive formal-bound and top-coefficient computations. A zero
 # specialized coefficient never lowers the degree bound of an ancestor.
 deg={p:1 for p in ports}
 def bound(n):
  if type(n)is int:return 0
  if n not in deg:
   op,a,b=defs[n];da,db=bound(a),bound(b);deg[n]=da+db if op=='*'else max(da,db)
  return deg[n]
 need(bound(packet['output'])in (1192,2344),'known formal upper bound')
 mod=1000003;top={p:i+2 for i,p in enumerate(ports)}
 def coefficient(n):
  if type(n)is int:return n%mod
  if n not in top:
   op,a,b=defs[n];target=bound(n)
   if op=='*':v=coefficient(a)*coefficient(b)
   else:v=(coefficient(a)if bound(a)==target else 0)+(1 if op=='+'else-1)*(coefficient(b)if bound(b)==target else 0)
   top[n]=v%mod
  return top[n]
 c=coefficient(packet['output']);need(c!=0,'integer degree attained by modular line')
 trace=[[n,bound(n),coefficient(n)]for n,_,_,_ in packet['polynomial_source']]
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],exact_degree=bound(packet['output']),positive_witnesses=len(packet['auxiliaries']),comparisons=len(packet['comparisons']),specialized_leading_coefficient=c,modulus=mod,degree_trace_sha256=sha(stable(trace)),all_gates_and_ports_live=True)

def polyvar(i):return {tuple(1 if j==i else 0 for j in range(4)):1}
def pc(c):return {(0,0,0,0):c}if c else{}
def padd(a,b,sgn=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items()if v}
def pmul(a,b):
 c={}
 for m,x in a.items():
  for n,y in b.items():
   e=tuple(u+v for u,v in zip(m,n));c[e]=c.get(e,0)+x*y
 return {m:v for m,v in c.items()if v}
def formula_bridge(packet,clock):
 C,x,F,rhs=[polyvar(i)for i in range(4)]
 vals={clock:C,'x':x,'clean_final_payload':F}
 for n,op,a,b in packet['source'][-5:]:
  aa=pc(a)if type(a)is int else vals[a];bb=pc(b)if type(b)is int else vals[b]
  vals[n]=pmul(aa,bb)if op=='*'else padd(aa,bb,1 if op=='+'else-1)
 D=padd(padd(pmul(pc(2),C),pmul(pc(192),padd(x,F))),pc(208));need(vals['clean_clock_word']==D,'actual affine bridge expansion')
 old=padd(C,rhs,-1);new=padd(D,rhs,-1);correction=padd(pmul(new,new),pmul(old,old),-1)
 alternative=padd(padd(pmul(D,D),pmul(C,C),-1),pmul(pc(2),pmul(rhs,padd(D,C,-1))),-1)
 need(correction==alternative,'entire SOS replacement correction')
 return dict(variables=['Ctau','x','F','rhs'],expanded_correction=[[list(m),v]for m,v in sorted(correction.items())],ring_identity=True)

def run(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  x=a if type(a)is int else e[a];y=b if type(b)is int else e[b]
  e[n]=x*y if op=='*'else x+y if op=='+'else x-y
 return e

def scalar_checks(packet,adjusted,pairs,seed):
 rnd=random.Random(seed);tail,out=sos(pairs,'ep_');counts=Counter();ports=packet['parameters']+packet['auxiliaries']
 for j in range(8):
  values={p:rnd.randrange(-3,5)for p in ports}
  if j>=5:values={p:Fraction(v,2)for p,v in values.items()}
  e=run(packet['polynomial_source'],values);old=run(adjusted+tail,values)
  for a,b in pairs[:-1]:need(e[a]-e[b]==old[a]-old[b],'unchanged whole residual')
  C,R=pairs[-1];D=packet['comparisons'][-1][0]
  need(e[packet['output']]==old[out]-(e[C]-e[R])**2+(e[D]-e[R])**2,'whole scalar correction')
  need(e[packet['output']]==sum((e[a]-e[b])**2 for a,b in packet['comparisons']),'independent direct full SOS')
  counts['complete_values']+=1;counts['retained_residual_values']+=18
  if j>=5:counts['rational_values']+=1
 return dict(counts)

def instruction(variant,code,N):
 if variant=='clock_incdec'and code==1:return 2,2*N,300*N+8
 if variant=='clock_incdec'and code==2 and N%2==0:return 3,N//2,150*N+8
 if variant!='clock_incdec'and code==1:
  okay=variant=='clock_nop'or variant=='clock_zero3'and N%3!=0 or variant=='clock_positive3'and N%3==0
  if okay:return 2,N,192*N+8
 return (4 if variant=='clock_incdec'else 3),N,192*N+8

def mapping(packet):
 mp=packet['mapping'];need(mp['K']==5 and mp['modulus']==30 and mp['initial']==1,'literal state geometry')
 need(mp['codes']==({'s':1,'a':2,'h':3}if packet['variant']=='clock_incdec'else{'s':1,'h':2}),'exact state labels')
 need(mp['halt']==mp['codes']['h']and mp['trap']==len(mp['codes'])+1,'halting trap assignment')
 checks=0
 for res in range(1,31):
  code=(res-1)%5+1;offset=(res-code)//5+1
  p=[];t=[]
  for quotient in (0,1,7):
   N=6*quotient+offset;cn,nn,tt=instruction(packet['variant'],code,N)
   p.append(5*(nn-1)+cn);t.append(tt)
  expected_map=[p[1]-p[0],p[0]];expected_clock=[t[1]-t[0],t[0]]
  need(mp['table'][res-1]==expected_map and mp['clocks'][res-1]==expected_clock,'actual literal transition/tick coefficients')
  need(p[2]==expected_map[0]*7+expected_map[1] and t[2]==expected_clock[0]*7+expected_clock[1],'affine residue persistence')
  checks+=1
 return checks

def clock_word_coefficients(packet,clock):
 defs={n:(op,a,b)for n,op,a,b in packet['source']};memo={};visited=set()
 def combine(a,b,sign=1):
  out=dict(a)
  for n,c in b.items():out[n]=out.get(n,0)+sign*c
  return {n:c for n,c in out.items()if c}
 def get(n):
  if type(n)is int:return {'constant':n}if n else{}
  if n not in defs:return {n:1}
  if n not in memo:
   op,a,b=defs[n];x,y=get(a),get(b);visited.add(n)
   if op=='*':
    if set(x)<= {'constant'}:memo[n]={k:x.get('constant',0)*v for k,v in y.items()if x.get('constant',0)*v}
    else:
     need(set(y)<= {'constant'},'actual clock cone is affine in hats')
     memo[n]={k:y.get('constant',0)*v for k,v in x.items()if y.get('constant',0)*v}
   else:memo[n]=combine(x,y,1 if op=='+'else-1)
  return memo[n]
 mp=packet['mapping'];by_slope={}
 for (a,d),(c,b)in zip(mp['table'],mp['clocks']):
  if a in by_slope:need(by_slope[a]==c,'same map slope has same physical clock slope')
  by_slope[a]=c
 slopes=sorted(by_slope);base=by_slope[slopes[0]]
 want={'quotient_hat':base,'constant':-base}
 for j,a in enumerate(slopes[1:]):
  c=by_slope[a]-base;want=combine(want,{f'product{j}_hat':c,'constant':-c})
 for j,(c,b)in enumerate(mp['clocks']):want=combine(want,{f'edge{j}_hat':b,'constant':-b})
 need(get(clock)==want,'entire actual packed-clock affine expression matches all literal physical ticks')
 return dict(clock_ancestry_gates=len(visited),complete_affine_coefficients=dict(sorted(want.items())),coefficient_sha256=sha(stable(want)))

def genuine_outer(packet,x,double):
 N=x+1;code=1;path=[5*x+1];ticks=[];quotients=[];residues=[];mp=packet['mapping']
 for step in range(3):
  cn,nn,tick=instruction(packet['variant'],code,N)
  q,r=divmod(path[-1]-1,30);quotients.append(q);residues.append(r);ticks.append(tick);path.append(5*(nn-1)+cn)
  if cn==mp['trap']:return None
  N,code=nn,cn
  if code==mp['halt']:break
 else:raise ValueError('literal fixed program did not halt')
 theta=sum(ticks);F=N;U=2*theta+192*(F+x)+208
 h=2
 while h<=max(path[0]+U,max(quotients)):h*=2
 if double:h*=2
 B=262144*h*h;t=len(ticks);P=B**t;J=(P-1)//(B-1)
 pack=lambda seq:sum(v*B**i for i,v in enumerate(seq))
 E=[pack([int(r==j)for r in residues])for j in range(30)];W=pack(quotients)
 slopes=sorted(set(a for a,d in mp['table']));selected=[pack([q if mp['table'][r][0]==a else 0 for q,r in zip(quotients,residues)])for a in slopes[1:]]
 Ctau=pack(ticks);need((Ctau-theta)%(B-1)==0,'true clock quotient integrality')
 values={n:1 for n in packet['auxiliaries']};values.update(x=x,U=U,clean_final_payload=F,height_slack=h-path[0]-U,quotient_hat=W+1,global_slack=P-J-W-1-sum(selected)-len(selected),clock_quotient_hat=1+2*((Ctau-theta)//(B-1)))
 values.update({f'edge{i}_hat':v+1 for i,v in enumerate(E)});values.update({f'product{i}_hat':v+1 for i,v in enumerate(selected)})
 need(all(values[n]>0 for n in packet['auxiliaries']),'all supplied positive outer and placeholder coordinates')
 e=run(packet['source'],values)
 for ix in (0,1,18):
  a,b=packet['comparisons'][ix];need(e[a]==e[b],'actual outer equation')
 need(e[packet['interfaces']['height']]==h and e[packet['interfaces']['target']]==path[-1],'actual computed height and endpoint')
 H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;Z=(e['native__F3']-8)//16
 need(H&M==Z,'complete joined prescribed AND')
 need(U<h and U<B-1 and U<=4768*30*h*h+4608*h+16,'no-wrap outer fixture')
 return dict(x=x,U=U,F=F,theta=theta,height=h,steps=t,positive_clock_hat=values['clock_quotient_hat'],whole_native_zero_materialized=False)

def verify(repo,author_root):
 author,parent=load(repo,author_root);forms=[];totals=Counter()
 need([f['packet']['variant']for f in author['forms']]==NAMES,'exact variant order')
 for ix,(pf,af)in enumerate(zip(parent['forms'],author['forms'])):
  old=pf['packet'];p=af['packet'];want,adjusted,pairs,radix=expected(old)
  for k,v in want.items():need(typed(p[k],v),'independent entire source/interface '+k)
  need(p['variant']==old['variant']and p['radix_multiplier']==262144 and p['radix_minimum']==max(131072,4768*30+2310),'literal chosen radix recipe')
  need(p['parent_source_sha256']==sha(stable(old['source'])),'actual parent source hash')
  l=walk(p);need(typed(l,p['ledger']),'every author ledger and degree entry')
  need(l['operations']==[597,472,470,473][ix]and l['positive_witnesses']==[59,57,57,57][ix],'complete counts')
  need(l['M']==old['polynomial_ledger']['M']+2 and l['A']==old['polynomial_ledger']['A']+3,'exact entire paid delta')
  need(l['specialized_leading_coefficient']==[667404,476833,476833,476833][ix],'independent nonzero modular coefficient')
  pr=formula_bridge(p,pairs[-1][0]);num=scalar_checks(p,adjusted,pairs,5729+ix);mc=mapping(p);clockproof=clock_word_coefficients(p,pairs[-1][0])
  fixtures=[]
  for x in (0,1,2,5,14,40):
   for d in (False,True):
    f=genuine_outer(p,x,d)
    if f:fixtures.append(f)
  forms.append(dict(variant=p['variant'],ledger=l,source_hash=sha(stable(p['polynomial_source'])),T_consumer_rows=[old['interfaces']['height'],old['source'][-1][0]],y_consumer_rows=['bridge_final_scaled'],radix_edited_row=radix,full_correction=pr,numerical=num,mapping_rows=mc,actual_clock_word=clockproof,outer_fixtures=fixtures))
  totals['complete_sources']+=1;totals['live_gates']+=l['operations'];totals['retained_comparison_identities']+=18;totals['full_finalizers']+=2;totals['exact_degree_certificates']+=1;totals['residue_mapping_and_tick_rows']+=mc;totals['whole_clock_coefficient_identities']+=1;totals['true_outer_AND_fixtures']+=len(fixtures);totals.update(num)
 need(2308*4-4608*2-16==0 and [2308,8-4616,-16]==[2308,-4608,-16],'uniform height-two factorization')
 need(262144>=4768*30+2310 and 131072<4768*30+2310,'increased radix threshold')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS.copy(),dependency_pins=DEPENDENCIES.copy(),counts=dict(totals),forms=forms,scope='Independent data-only audit of all4 complete paid sources, exact source correction and integer polynomial degrees; mathematical proof read separately. No author/ancestor imports, native Pell zero materialization, general public API claim or universal bound.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo-root',type=Path,required=True);ap.add_argument('--author-root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 author_root=a.author_root if a.author_root is not None else a.repo_root/WIP
 r=verify(a.repo_root,author_root)
 if a.expect:need(typed(r,json.loads(a.expect.read_text())),'type-exact independent receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',**r['counts']),sort_keys=True))
if __name__=='__main__':main()
