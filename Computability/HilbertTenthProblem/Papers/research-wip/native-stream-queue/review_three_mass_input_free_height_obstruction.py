#!/usr/bin/env python3
"""Independent full-DAG lift and formal arbitrary-iterate clock-shear audit."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path
from fractions import Fraction
STEM='three_mass_input_free_height_obstruction'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
AUTHOR_PINS={'py': 'da206f99a5d1413413032208758f170e29f655b6a3cee2529ad30b4fbb62a53c', 'json': '956e5337242e801ba81348fe0181c1bd7a1072c2cc7c7d2fd04509e2cdbdc391', 'md': '01d73d33412d79becf123be6ec1ff006c43875c4f0c3f88bfd4ea7a98bb2ce31'}
PINS={'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.json': 'da080d336bc029d1c8dccaace8347abc1d9ac423c683a9036f2754d86675a3ce', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.md': 'ef3b4cbee6858f3d854b42365a66b97d4083bf24ac7195f0fc68c29b1752b508', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_direct_clean_clock.py': '74ec9dde1aa6c57b774f4001d4ab4e5061cfa797dae780a4ea7feff9cec8f33a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_target_free_height.md': 'f0bd6c2011ca1aa0dd5e6dbaaea7907d35f13f4dd756fc2786528c80f60f75ff', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.json': 'a360d1573dfb12b2e5fb3188bdce3a36e7029c4fc13b86b61969f34d2644b7d1', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.md': '59efd3d56b794f8632c1da48c080083a750895e9897bf213662195e45861167c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_direct_clean_clock.py': '9627ffd85f79e5ed2c0174f716e95afcf1f92c0f3035e65c76aaa15f98af34b6', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/18-cell-clock-cellular-clock-CA_CLOCK_DOMINATION.md': 'f7385dc48b48fb4f3f95ca082477f36184d6b9cd83f8a97962e9edcc75f94c4c', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/18-cell-clock-cellular-clock-audit-AUDIT.md': '478ac5263c76f7bfcf9511b7980f7514737c31996fa402b9118eb5f7492ca630', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/20-event-budget-PROOF.md': 'd74157254a36e53c1568cea383cdcc46dd73adca48a1a9a7eee4e46b51b73922', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/data/18-cell-clock-cellular-clock-audit-old-new-five-row-traces.json': 'c7e46bdf9b83aad9ce9294d878ae50fd5240846596aec0a5a9e1d007793bc497', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/15-clean-targets-CLEAN-TARGET-THEOREM.md': '3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-FOLDED-ADDENDUM.md': '1ce912386db479f63eed0d05f2a7d79649b4d8a03b91bf2080338f1cafaafde8', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/22-clean-clocks-THEOREM.md': '93bf673898816aed526ef943160a9d3dfb950cedc3bf0f59d6ae4d78c7add11d'}
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def equal(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(equal(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(equal(v,w)for v,w in zip(a,b))
 return a==b

def sos(pairs):
 rows=[];squares=[]
 for j,(a,b)in enumerate(pairs):
  r='clean_res'+str(j);s='clean_sq'+str(j)
  rows.extend([[r,'-',a,b],[s,'*',r,r]]);squares.append(s)
 out=squares[0]
 for j,s in enumerate(squares[1:],1):
  name='clean_sum'+str(j);rows.append([name,'+',out,s]);out=name
 return rows,out

def intern(pool,key):
 if key not in pool:pool[key]=len(pool)
 return pool[key]
def graph_expression(rows,ports,pool):
 e=ports.copy()
 def at(v):return intern(pool,('literal',v))if type(v)is int else e[v]
 for n,op,a,b in rows:e[n]=intern(pool,(op,at(a),at(b)))
 return e

def ledger(p):
 ports=p['parameters']+p['auxiliaries'];need(len(set(ports))==len(ports),'distinct ports')
 defs={};counts=Counter();known=set(ports)
 for n,op,a,b in p['polynomial_source']:
  need(n not in known and op in ('+','-','*'),'fresh valid gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'closed gate')
  known.add(n);defs[n]=(op,a,b);counts['M'if op=='*'else'A']+=1
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in defs:todo.extend(defs[n][1:])
 need(live==known,'all gates and coordinates live')
 mod=1000033;degree={n:1 for n in ports};coef={n:j+11 for j,n in enumerate(ports)}
 for n,op,a,b in p['polynomial_source']:
  da,db=[0 if type(v)is int else degree[v]for v in (a,b)]
  ca,cb=[v%mod if type(v)is int else coef[v]for v in (a,b)]
  d=da+db if op=='*'else max(da,db)
  top=ca*cb if op=='*'else (ca if da==d else 0)+(1 if op=='+'else -1)*(cb if db==d else 0)
  degree[n]=d;coef[n]=top%mod
 need(coef[p['output']]!=0,'independent line attains degree bound')
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],exact_degree=degree[p['output']],positive_witnesses=len(p['auxiliaries']),modulus=mod,line_coefficient=coef[p['output']])

class Ring:
 def __init__(self):
  self.names=['x','F','v','B','P','U','cur','nxt','clock','r'];self.zero=(0,)*len(self.names)
 def c(self,n):return {self.zero:n}if n else{}
 def v(self,n):
  e=list(self.zero);e[self.names.index(n)]=1;return {tuple(e):1}
 def add(self,a,b,sign=1):
  c=dict(a)
  for m,v in b.items():c[m]=c.get(m,0)+sign*v
  return {m:v for m,v in c.items()if v}
 def mul(self,a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    t=tuple(i+j for i,j in zip(m,n));c[t]=c.get(t,0)+v*w
  return {m:v for m,v in c.items()if v}
 def digest(self,a):return sha(stable([[list(m),v]for m,v in sorted(a.items())]))
 def substitute(self,a,ports):
  total=self.c(0)
  for m,c in a.items():
   term=self.c(c)
   for i,k in enumerate(m):
    for _ in range(k):term=self.mul(term,ports.get(self.names[i],self.v(self.names[i])))
   total=self.add(total,term)
  return total

def exact_shear(p):
 defs={n:(op,a,b)for n,op,a,b in p['source']};pairs=p['comparisons']
 left,right=pairs[1];op,shift,n0=defs[left];need(op=='+'and n0=='bridge_input','actual transport left')
 op,B,nxt=defs[shift];need(op=='*','actual radix shift')
 op,cur,targetprod=defs[right];need(op=='+','actual transport right')
 op,P,nf=defs[targetprod];need(op=='*'and nf=='bridge_target','actual scaled target')
 need(defs[B]==('*',262144,'bridge_height_square'),'actual radix')
 clock=defs['clean_double_clock_word'];need(clock[:2]==('*',2),'actual packed clock multiplier');clock=clock[2]
 # The only varying supplied ports are x,F,v. All other comparison cones,
 # radix, scale, history words and packed ticks must be independent of them.
 influenced={'x','clean_final_payload','clock_quotient_hat'}
 for n,op,a,b in p['source']:
  if a in influenced or b in influenced:influenced.add(n)
 need(all(n not in influenced for n in (B,P,cur,nxt,clock)),'fixed local cuts')
 need(all(a not in influenced and b not in influenced for j,(a,b)in enumerate(pairs)if j not in (1,18)),'all other17 residuals unchanged')
 need(not any(n.startswith('native__')for n in influenced),'entire native cone unchanged')
 ring=Ring();V={n:ring.v(n)for n in ring.names}
 cuts={B:V['B'],P:V['P'],cur:V['cur'],nxt:V['nxt'],clock:V['clock'],'x':V['x'],'clean_final_payload':V['F'],'clock_quotient_hat':V['v'],'U':V['U']}
 memo=cuts.copy()
 def at(n):
  if type(n)is int:return ring.c(n)
  if n not in memo:
   need(n in defs,'closed local endpoint cone')
   op,a,b=defs[n];a,b=at(a),at(b);memo[n]=ring.mul(a,b)if op=='*'else ring.add(a,b,1 if op=='+'else -1)
  return memo[n]
 rtransport=ring.add(at(left),at(right),-1)
 rclock=ring.add(at(pairs[18][0]),at(pairs[18][1]),-1)
 z=ring.add(V['B'],ring.c(1),-1);step=ring.mul(V['r'],z)
 changes={'x':ring.add(V['x'],ring.mul(V['P'],step)),'F':ring.add(V['F'],step),'v':ring.add(V['v'],ring.mul(ring.c(192),ring.mul(V['r'],ring.add(V['P'],ring.c(1)))))}
 for poly in (rtransport,rclock):need(ring.substitute(poly,changes)==poly,'all-value residual invariant for arbitrary r')
 expected_transport=ring.add(ring.add(ring.mul(V['B'],V['nxt']),ring.add(ring.mul(ring.c(5),V['x']),ring.c(1))),ring.add(V['cur'],ring.mul(V['P'],ring.add(ring.mul(ring.c(5),V['F']),ring.c(p['mapping']['halt']-5)))),-1)
 expected_clock=ring.add(ring.add(ring.mul(ring.c(2),V['clock']),ring.add(ring.mul(ring.c(192),ring.add(V['x'],V['F'])),ring.c(208))),ring.add(ring.mul(z,ring.add(V['v'],ring.c(1),-1)),V['U']),-1)
 need(rtransport==expected_transport and rclock==expected_clock,'full actual endpoint formulas')
 return dict(radix_register=B,scale_register=P,unchanged_residuals=17,arbitrary_r_residual_identities=2,entire_native_cone_unchanged=True,transport_digest=ring.digest(rtransport),clock_digest=ring.digest(rclock))

def evaluate(rows,ports):
 e=ports.copy()
 at=lambda n:n if type(n)is int else e[n]
 for n,op,a,b in rows:
  a,b=at(a),at(b);e[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return e

def verify(repo,author_dir):
 ab={}
 for ext,pin in AUTHOR_PINS.items():
  b=(author_dir/(STEM+'.'+ext)).read_bytes();need(sha(b)==pin,'author pin '+ext);ab[ext]=b
 a=json.loads(ab['json']);need(a['source_sha256']==AUTHOR_PINS['py'],'source receipt binding')
 need(a['dependency_pins']==PINS,'all declared pins')
 blobs={}
 for name,pin in PINS.items():
  b=(repo/name).read_bytes();need(sha(b)==pin,'dependency '+name);blobs[name]=b
 parent=json.loads(blobs[WIP+'/three_mass_direct_clean_clock.json'])
 need(len(a['forms'])==len(parent['forms'])==4,'four exact sources')
 records=[];totals=Counter()
 for author,old in zip(a['forms'],parent['forms']):
  p=author['candidate'];old=old['packet'];h=old['interfaces']['height']
  need(p['variant']==old['variant'],'exact variant')
  for k in ('parameters','auxiliaries','domains','comparisons','mapping','interfaces','output','radix_multiplier'):need(equal(p[k],old[k]),'literal retained interface '+k)
  need([r for r in old['source']if r[0]=='bridge_height_without_time']==[['bridge_height_without_time','+','bridge_input','height_slack']],'parent private addition')
  need([r for r in old['source']if 'bridge_height_without_time'in r[2:]]==[[h,'+','bridge_height_without_time','U']],'sole removed-row consumer')
  expected=[]
  for r in old['source']:
   if r[0]=='bridge_height_without_time':continue
   expected.append([h,'+','height_slack','U']if r[0]==h else r)
  need(p['source']==expected,'entire candidate body independent reconstruction')
  tail,out=sos(p['comparisons']);need(out==p['output'],'literal SOS output')
  need(old['polynomial_source']==old['source']+tail and p['polynomial_source']==p['source']+tail,'both entire paid SOS finalizers')
  bill=ledger(p)
  for k in ('M','A','operations','positive_witnesses','exact_degree'):need(bill[k]==p['ledger'][k],'actual ledger '+k)
  pool={};ports={n:intern(pool,('port',n))for n in old['parameters']+old['auxiliaries']}
  original=graph_expression(old['polynomial_source'],ports,pool);mapped=ports.copy();mapped['height_slack']=original['bridge_height_without_time']
  lifted=graph_expression(p['polynomial_source'],mapped,pool)
  need(all(original[n]==lifted[n]for n,_,_,_ in p['polynomial_source']),'every entire-DAG register agrees under parent lift')
  proof=exact_shear(p)
  # Supplemental off-zero signed/rational whole-polynomial identities.
  for case in range(8):
   values={n:(i+3*case)%5-2 for i,n in enumerate(ports)}
   if case>=5:values={n:Fraction(v,3)for n,v in values.items()}
   e=evaluate(old['polynomial_source'],values);mappedvals=values.copy();mappedvals['height_slack']=values['height_slack']+e['bridge_input']
   child=evaluate(p['polynomial_source'],mappedvals);need(child[p['output']]==e[old['output']],'whole lift numeric identity')
   r=case-3;B=child[proof['radix_register']];P=child[proof['scale_register']]
   changed=mappedvals.copy();changed['x']+=r*P*(B-1);changed['clean_final_payload']+=r*(B-1);changed['clock_quotient_hat']+=192*r*(P+1)
   shifted=evaluate(p['polynomial_source'],changed)
   need(shifted[p['output']]==child[p['output']],'entire SOS numeric invariance')
   need(all(child[l]-child[rr]==shifted[l]-shifted[rr]for l,rr in p['comparisons']),'all residual numeric invariance')
  f=author['outer_seed_and_shift'];N=f['x']+1;coeff,offset=(1584,48)if p['variant']=='clock_incdec'else(768,32)
  need(f['U']==coeff*N+offset,'physical clean seed time')
  need(f['shifted_x']==f['x']+f['scale']*(f['radix']-1),'actual shifted input')
  need(f['shifted_final_payload']==f['final_payload']+f['radix']-1,'actual shifted claimed endpoint')
  need(f['radix']==262144*f['height']**2 and f['height']&(f['height']-1)==0,'dyadic genuine height')
  need(f['radix']%3==1 and (f['shifted_x']-f['x'])%3==0,'successful prime-three guard stays same')
  need(f['actual_shifted_clean_time']==coeff*(f['shifted_x']+1)+offset>f['U'],'strict false time')
  records.append(dict(variant=p['variant'],ledger=bill,full_source_sha256=sha(stable(p['polynomial_source'])),whole_parent_lift_identity=True,whole_arbitrary_iterate_invariance=True,proof=proof,numeric_full_lifts=8,numeric_full_shears=8,rational_each=3))
  totals.update(complete_sources=1,live_gates=bill['operations'],full_finalizers=2,lifted_gate_identities=bill['operations'],residual_invariance_identities=19,whole_numeric_lifts=8,whole_numeric_shears=8,rational_each=3)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,dependency_pins=PINS,counts=dict(totals),forms=records,scope='Independent whole-DAG parent lift, arbitrary-integer-iterate residual symmetry, complete finalizers and exact degrees. Mathematical positive false-zero theorem read separately. No ancestor imports, full native zero materialization or independent Report18 literal graph reconstruction.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--author-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 result=verify(a.repo,a.author_root or a.repo/WIP)
 if a.expect:need(equal(result,json.loads(a.expect.read_text())),'type-exact saved review')
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',**result['counts']),sort_keys=True))
if __name__=='__main__':main()
