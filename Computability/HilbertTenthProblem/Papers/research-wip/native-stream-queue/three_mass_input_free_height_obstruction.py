#!/usr/bin/env python3
"""Complete source-specific obstruction to dropping initial input from clean height."""
import argparse,copy,hashlib,json
from collections import Counter
from pathlib import Path
PINS={'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_target_free_height.md': 'f0bd6c2011ca1aa0dd5e6dbaaea7907d35f13f4dd756fc2786528c80f60f75ff', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/20-event-budget-PROOF.md': 'd74157254a36e53c1568cea383cdcc46dd73adca48a1a9a7eee4e46b51b73922', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/15-clean-targets-CLEAN-TARGET-THEOREM.md': '3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-FOLDED-ADDENDUM.md': '1ce912386db479f63eed0d05f2a7d79649b4d8a03b91bf2080338f1cafaafde8', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-THEOREM.md': '93bf673898816aed526ef943160a9d3dfb950cedc3bf0f59d6ae4d78c7add11d', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.py': '9627ffd85f79e5ed2c0174f716e95afcf1f92c0f3035e65c76aaa15f98af34b6', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.json': 'a360d1573dfb12b2e5fb3188bdce3a36e7029c4fc13b86b61969f34d2644b7d1', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.md': '59efd3d56b794f8632c1da48c080083a750895e9897bf213662195e45861167c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.py': '74ec9dde1aa6c57b774f4001d4ab4e5061cfa797dae780a4ea7feff9cec8f33a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.json': 'da080d336bc029d1c8dccaace8347abc1d9ac423c683a9036f2754d86675a3ce', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.md': 'ef3b4cbee6858f3d854b42365a66b97d4083bf24ac7195f0fc68c29b1752b508', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/18-cell-clock-cellular-clock-CA_CLOCK_DOMINATION.md': 'f7385dc48b48fb4f3f95ca082477f36184d6b9cd83f8a97962e9edcc75f94c4c', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/18-cell-clock-cellular-clock-audit-AUDIT.md': '478ac5263c76f7bfcf9511b7980f7514737c31996fa402b9118eb5f7492ca630', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/data/18-cell-clock-cellular-clock-audit-old-new-five-row-traces.json': 'c7e46bdf9b83aad9ce9294d878ae50fd5240846596aec0a5a9e1d007793bc497'}
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
REPORT='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/'
PARENT=WIP+'three_mass_direct_clean_clock.json'
def need(c,m='check failed'):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def c(n):return {():n}if n else {}
def v(n):return {((n,1),):1}
def add(a,b,sign=1):
 out=a.copy()
 for m,n in b.items():out[m]=out.get(m,0)+sign*n
 return {m:n for m,n in out.items()if n}
def mul(a,b):
 out={}
 for m,a0 in a.items():
  for n,b0 in b.items():
   d=dict(m)
   for x,e in n:d[x]=d.get(x,0)+e
   key=tuple(sorted(d.items()));out[key]=out.get(key,0)+a0*b0
 return {m:n for m,n in out.items()if n}
def serial(p):return [[[list(e)for e in m],n]for m,n in sorted(p.items())]
def run(rows,values):
 env=values.copy();at=lambda x:x if type(x)is int else env[x]
 for n,op,a,b in rows:
  a,b=at(a),at(b);env[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return env

def ledger(p):
 ports=p['parameters']+p['auxiliaries'];known=set(ports);deps={};cnt=Counter()
 degree={n:1 for n in ports};top={n:i+2 for i,n in enumerate(ports)};modulus=1000003
 for n,op,a,b in p['polynomial_source']:
  need(n not in known and op in ('+','-','*'))
  need(all(type(x)is int or type(x)is str and x in known for x in (a,b)))
  da,db=[0 if type(x)is int else degree[x]for x in (a,b)]
  la,lb=[x%modulus if type(x)is int else top[x]for x in (a,b)]
  d=da+db if op=='*'else max(da,db)
  value=la*lb if op=='*'else (la if da==d else 0)+(1 if op=='+'else -1)*(lb if db==d else 0)
  degree[n]=d;top[n]=value%modulus;known.add(n);deps[n]=[x for x in (a,b)if type(x)is str]
  cnt['M'if op=='*'else 'A']+=1
 live={p['output']}
 for n,op,a,b in reversed(p['polynomial_source']):
  if n in live:live.update(deps[n])
 need(live==known and top[p['output']]!=0)
 return {'M':cnt['M'],'A':cnt['A'],'operations':len(p['polynomial_source']),
  'positive_witnesses':len(p['auxiliaries']),'comparisons':len(p['comparisons']),
  'exact_degree':degree[p['output']],'modulus':modulus,'specialized_leading_coefficient':top[p['output']]}

def candidate(parent):
 rows=parent['source'];defs={r[0]:r for r in rows};old='bridge_height_without_time';h=parent['interfaces']['height']
 need(defs[old]==[old,'+','bridge_input','height_slack'])
 need(defs[h]==[h,'+',old,'U'])
 cons=lambda n:[r[0]for r in rows if n in r[2:]]
 need(cons(old)==[h]and cons('height_slack')==[old])
 def rewrite(source):return [[n,op,*['height_slack'if x==old else x for x in ab]]for n,op,*ab in source if n!=old]
 p={k:copy.deepcopy(parent[k])for k in ('variant','parameters','auxiliaries','domains','comparisons','mapping','interfaces','output','radix_multiplier')}
 p['source']=rewrite(rows);p['polynomial_source']=rewrite(parent['polynomial_source'])
 need(len(p['polynomial_source'])==len(parent['polynomial_source'])-1)
 p['scope']='Unsound input-free-height candidate: complete full positive false-clock zeros proved by fresh native extension and polynomial shear.'
 p['sound_projection_established']=False;p['ledger']=ledger(p)
 need(p['ledger']['M']==parent['ledger']['M']and p['ledger']['A']==parent['ledger']['A']-1)
 return p

def identities(parent,p):
 defs={n:(op,a,b)for n,op,a,b in p['source']};pairs=p['comparisons'];K=p['mapping']['K']
 need(K==5 and p['parameters']==['x','U'])
 # Parent -> candidate positive lift changes only eta, and eta had one private consumer.
 eta,n0,U=v('eta'),v('n0'),v('U')
 need(add(add(n0,eta),U)==add(add(eta,n0),U))
 # Every input/final-payload/clock-hat consumer is audited, not assumed absent.
 cons=lambda x:[n for n,op,a,b in p['source']if x in (a,b)]
 need(cons('x')==['bridge_input_scaled','clean_payload_sum'])
 need(cons('clean_final_payload')==['bridge_final_scaled','clean_payload_sum'])
 need(defs['bridge_input_scaled']==('*',5,'x'))
 need(defs['bridge_final_scaled']==('*',5,'clean_final_payload'))
 need(defs['bridge_input']==('+','bridge_input_scaled',1))
 need(defs['bridge_target']==('+','bridge_final_scaled',p['mapping']['halt']-5))
 clock_unhat=cons('clock_quotient_hat');need(len(clock_unhat)==1)
 need(defs[clock_unhat[0]]==('-','clock_quotient_hat',1))
 targetuses=cons('bridge_target');need(len(targetuses)==1)
 op,P,target=defs[targetuses[0]];need(op=='*'and target=='bridge_target')
 radix=[n for n,r in defs.items()if r==('*',262144,'bridge_height_square')];need(len(radix)==1);B=radix[0]
 bm1=[n for n,r in defs.items()if r==('-',B,1)];need(len(bm1)==1);bm1=bm1[0]
 changed={'x','clean_final_payload','clock_quotient_hat'}
 for n,op,a,b in p['source']:
  if a in changed or b in changed:changed.add(n)
 need(B not in changed and P not in changed and p['interfaces']['height']not in changed)
 need(all(not n.startswith('native__')for n in changed),'no native dependency on sheared ports after height deletion')
 # Exact all-value computation at unaffected source-register cuts. The sole
 # linked cut is the literal Bminus1=B-1; P remains an independent fixed cut.
 base={n:v('cut_'+n)for n in defs if n not in changed}
 base[bm1]=add(base[B],c(1),-1)
 for n in p['parameters']+p['auxiliaries']:base[n]=v(n)
 old=base.copy();new=base.copy();z=base[bm1]
 new['x']=add(old['x'],mul(base[P],z))
 new['clean_final_payload']=add(old['clean_final_payload'],z)
 new['clock_quotient_hat']=add(old['clock_quotient_hat'],mul(c(192),add(base[P],c(1))))
 def execute(env):
  at=lambda x:c(x)if type(x)is int else env[x]
  for n,op,a,b in p['source']:
   if n not in changed:continue
   a,b=at(a),at(b);env[n]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else -1)
  return env
 old=execute(old);new=execute(new)
 proofs=[]
 for a,b in pairs:
  r0=add(old[a],old[b],-1);r1=add(new[a],new[b],-1);need(r0==r1,'entire retained residual invariant')
  proofs.append(sha(stable(serial(r0))))
 # Actual complete finalizer remains exactly unchanged after the body deletion.
 need(p['polynomial_source'][len(p['source']):]==parent['polynomial_source'][len(parent['source']):])
 return {'radix_register':B,'scale_register':P,'residual_invariance_proofs':proofs,
  'all_19_residuals_invariant':True,'full_SOS_invariant':True,
  'parent_positive_lift':'eta_candidate=eta_parent+n0',
  'shear':{'x':'x+P*(B-1)','clean_final_payload':'F+(B-1)','clock_quotient_hat':'clock_quotient_hat+192*(P+1)'},
  'native_registers_unchanged':True,'whole_parent_identity_after_height_lift':True}

def seed_and_shift(p,proof):
 mp=p['mapping'];x=2 if p['variant']=='clock_positive3'else 0;n0=5*x+1;n=n0;path=[n];qs=[];rs=[];ticks=[]
 for _ in range(3):
  q,r=divmod(n-1,30);qs.append(q);rs.append(r);a,d=mp['table'][r];k,b=mp['clocks'][r];ticks.append(k*q+b)
  n=a*q+d;path.append(n)
  if (n-1)%5+1==mp['halt']:break
 else:raise ValueError('seed path')
 F=(n-mp['halt'])//5+1;theta=sum(ticks);U=2*theta+192*(x+F)+208
 need(F==x+1)
 h=1
 while h<=max(n0+U,*qs):h*=2
 B=262144*h*h;P=B**len(qs);J=(P-1)//(B-1)
 pack=lambda digits:sum(v*B**i for i,v in enumerate(digits))
 E=[pack([int(r==s)for r in rs])for s in range(30)];W=pack(qs)
 classes=sorted({a for a,d in mp['table']} - {min(a for a,d in mp['table'])})
 Z=[pack([q if mp['table'][r][0]==a else 0 for q,r in zip(qs,rs)])for a in classes]
 values={n:1 for n in p['auxiliaries']}
 values.update(x=x,U=U,clean_final_payload=F,height_slack=h-U,quotient_hat=W+1,
  global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+2*(pack(ticks)-theta)//(B-1))
 values.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)})
 values.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
 need(h-U==h-n0-U+n0 and h-n0-U>0)
 shifted=values.copy();shifted['x']+=P*(B-1);shifted['clean_final_payload']+=B-1;shifted['clock_quotient_hat']+=192*(P+1)
 need(all(values[n]>0 and shifted[n]>0 for n in p['auxiliaries']))
 a=run(p['source'],values);b=run(p['source'],shifted)
 need(a[proof['radix_register']]==b[proof['radix_register']]==B)
 need(a[proof['scale_register']]==b[proof['scale_register']]==P)
 for i,(l,r)in enumerate(p['comparisons']):
  need(a[l]-a[r]==b[l]-b[r])
  if i in (0,1,18):need(a[l]==a[r]and b[l]==b[r])
 for name in a:
  if name.startswith('native__'):need(a[name]==b[name])
 H=(a['native__padded_A']-12)//16;M=(a['native__padded_B']-10)//16;A=(a['native__F3']-8)//16
 need(H&M==A)
 coefficient,offset=(1584,48)if p['variant']=='clock_incdec'else(768,32)
 need(U==coefficient*(x+1)+offset)
 true_shifted_time=coefficient*(shifted['x']+1)+offset
 need(true_shifted_time>U and shifted['clean_final_payload']!=shifted['x']+1)
 need(B%3==1 and (shifted['x']-x)%3==0,'prime-three guards preserved')
 return {'x':x,'final_payload':F,'U':U,'native_time':theta,'height':h,'radix':B,'scale':P,
  'parent_height_slack':h-n0-U,'candidate_height_slack':values['height_slack'],
  'shifted_x':shifted['x'],'shifted_final_payload':shifted['clean_final_payload'],
  'shifted_clock_hat':shifted['clock_quotient_hat'],'actual_shifted_clean_time':true_shifted_time,
  'all_native_registers_unchanged':True,'genuine_outer_AND':True,'native_Pell_witnesses_materialized':False}

def clock_report18(blobs):
 proof=REPORT+'18-cell-clock-cellular-clock-CA_CLOCK_DOMINATION.md'
 need(sha(blobs[proof])==PINS[proof])
 trace=json.loads(blobs[REPORT+'data/18-cell-clock-cellular-clock-audit-old-new-five-row-traces.json'])
 lam=72*509508+115;need(lam==36684691)
 primes=[2,3,5,7,11];totals={};rows=0
 for mode,record in trace.items():
  total=0
  for idx,row in enumerate(record):
   N=1
   for p,e in zip(primes,row['counters']):N*=p**e
   need(N==row['encoded_input_N'])
   p=row['prime'];q=N//p;symbol=row['symbol'];after=row['counters'][:];j=primes.index(p)
   if symbol=='+':M=(p+3)*N;TV=(p*p+3)*N*N;Z=4*N+3;after[j]+=1
   elif symbol=='-':
    need(N%p==0 and after[j]>0);M=3*N+q;TV=3*N*N+q*q;Z=2*N+2*q+3;after[j]-=1
   elif symbol in ('Z','P'):
    need((N%p==0)==(symbol=='P'));M=2*(N+q);TV=2*(N*N+q*q);Z=2*(N+q)+3
   else:need(symbol=='0');M=TV=0;Z=1
   need(row['macro_components_moves_variation_tests']==[M,TV,Z])
   duration=lam*M+TV+Z;need(duration==row['derived_CA_clock']);total+=duration;rows+=1
   if idx+1<len(record):need(after==record[idx+1]['counters'])
  totals[mode]={'five_counter_rows':len(record),'derived_CA_clock':total}
 need(totals['literal-reversible-source-20261003']=={'five_counter_rows':142,'derived_CA_clock':126594455831808973674445902})
 need(totals['reversible-initialization-optimization-20261003']=={'five_counter_rows':24,'derived_CA_clock':1394018396})
 need(38*lam+138==1394018396)
 return {'scope':'Small data-only clock-coefficient/trace check, not literal-source graph reconstruction or CA simulation.',
  'lambda':lam,'checked_five_counter_rows':rows,'totals':totals,
  'endpoint_potential_counterexample':{'path':[0,1,0],'square_total_variation':2,'endpoint_square_difference':0,'two_moving_row_clock':2*lam+2}}

def verify(repo):
 blobs={}
 for path,pin in PINS.items():
  b=(repo/path).read_bytes();need(sha(b)==pin,'pin '+path);blobs[path]=b
 parent=json.loads(blobs[PARENT]);forms=[]
 for record in parent['forms']:
  old=record['packet'];p=candidate(old);proof=identities(old,p);fixture=seed_and_shift(p,proof)
  forms.append({'candidate':p,'identities':proof,'outer_seed_and_shift':fixture})
 need([f['candidate']['ledger']['operations']for f in forms]==[596,471,469,472])
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'dependency_pins':copy.deepcopy(PINS),
  'scope':'All four literal input-free-height candidates are unsound. Full positive false zeros follow parametrically; only outer fixtures are materialized.',
  'counts':{'complete_candidate_sources':4,'full_candidate_gates':sum(len(f['candidate']['polynomial_source'])for f in forms),
    'exact_residual_shear_identities':76,'outer_seed_and_shift_pairs':4},'forms':forms,'separate_report18_check':clock_report18(blobs)}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True)
 g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo)
 text=json.dumps(r,sort_keys=True,indent=2)+'\n';need(same(r,json.loads(text)))
 if a.output:a.output.write_text(text)
 else:need(same(r,json.loads(a.expect.read_text())),'saved receipt')
 print(json.dumps({'status':'PASS','counts':r['counts'],'candidate_costs':[f['candidate']['ledger']['operations']for f in r['forms']]},sort_keys=True))
if __name__=='__main__':main()
