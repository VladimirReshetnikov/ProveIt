#!/usr/bin/env python3
"""Independent formal-B audit of the actual505 raw outer range obstruction."""
import argparse,hashlib,json,math,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
AUTHOR={
 'waterfall_packed_range_obstruction.py':'da29a82c4c8140b3c53991081ef3a77149d3d1de39be5b7e5043edd627c349a6',
 'waterfall_packed_range_obstruction.json':'b92c447dbc1b0a0dd0aef6e33ea05e94b4cd4df9c53efe6795e139766b137024',
 'waterfall_packed_range_obstruction.md':'e16165bd366d4c7d46aa4851849946191e47400b6c2979cca0ff762f309dca26'}
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
PINS={WIP+'u15_packed_consumed_affine505.py':'a8716b7ca82f703944993a247da89fa2a9a70ccfb5db11521161014edc4a3533',WIP+'u15_packed_consumed_affine505.json':'6376193a420efc81cffbd7becd51d7b2f84d4d44fa3706e5996e06920e06bca5','SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/data/14-waterfall-UniversalTM15x2.tm.txt':'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae'}
def need(v,m):
 if not v:raise AssertionError(m)
def sha(v):return hashlib.sha256(v).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def A(p,q,s=1):
 r=dict(p)
 for e,c in q.items():r[e]=r.get(e,0)+s*c
 return {e:c for e,c in r.items()if c}
def M(p,q):
 r={}
 for e,c in p.items():
  for f,d in q.items():r[e+f]=r.get(e+f,0)+c*d
 return {e:c for e,c in r.items()if c}
def C(n):return {0:Fraction(n)}if n else{}
def mon(e,c=1):return {e:Fraction(c)}if c else{}
def power(p,n):
 q=C(1)
 for _ in range(n):q=M(q,p)
 return q
def pack(xs):
 q={}
 for i,p in enumerate(xs):q=A(q,M(mon(i),p))
 return q
def evaluate(p,B):return sum(c*B**e for e,c in p.items())
def encoding(p):return [[e,c.numerator,c.denominator]for e,c in sorted(p.items())]
def positive_shift(p,at=512):
 shifted={}
 for e,c in p.items():
  for j in range(e+1):shifted[j]=shifted.get(j,0)+c*math.comb(e,j)*at**(e-j)
 shifted={e:c for e,c in shifted.items()if c}
 need(shifted.get(0,0)>0 and all(c>=0 for c in shifted.values()),'strict polynomial positivity for B>=512')
 return encoding(shifted)
def closure(rows,outputs,assignment):
 nodes={r[0]:r for r in rows};need(len(nodes)==len(rows),'unique source registers');live=set();stack=[v for v in outputs if type(v)is str]
 while stack:
  n=stack.pop()
  if n in live:continue
  live.add(n)
  if n in nodes:stack.extend(v for v in nodes[n][2:]if type(v)is str)
 free=live-set(nodes);need(free<=set(assignment),'outer closure needs no native witnesses')
 chosen=[r for r in rows if r[0]in live];e=dict(assignment)
 for n,o,a,b in chosen:
  need(o in('+','-','*')and all(type(x)is int or type(x)is str and x in e for x in(a,b)),'typed acyclic outer source')
  x=e[a]if type(a)is str else C(a);y=e[b]if type(b)is str else C(b);e[n]=M(x,y)if o=='*'else A(x,y,1 if o=='+'else-1)
 return e,chosen,sorted(free)
def verify(repo,subject):
 for n,h in AUTHOR.items():need(sha((subject/n).read_bytes())==h,'author pin '+n)
 for n,h in PINS.items():need(sha((repo/n).read_bytes())==h,'actual parent pin '+n)
 receipt=json.loads((subject/'waterfall_packed_range_obstruction.json').read_text());saved=json.loads((repo/(WIP+'u15_packed_consumed_affine505.json')).read_text());raw=[f['compiler']for f in saved['forms']if not f['compiler']['ordinary']]
 need(len(raw)==2 and sorted(p['ledger']['polynomial']['operations']for p in raw)==[318,320],'two actual raw forms, not ordinary505 evaluations')
 line=(repo/list(PINS)[-1]).read_text().splitlines()[0];rules=[]
 for q,cell in enumerate(line.split('_')):
  for s in range(2):
   rule=cell[3*s:3*s+3]
   if rule!='---':rules.append((q,s,ord(rule[2])-ord('A'),int(rule[1]=='L'),int(rule[0])))
 need(len(rules)==29,'literal table has29 defined rules')
 transition={(q,s):(n,d,w)for q,s,n,d,w in rules};indices=(0,2,4,13,12,14,17);path=[rules[i]for i in indices]
 need([(q,s)for q,s,*_ in path]==[(0,0),(1,0),(2,0),(6,1),(6,0),(7,0),(8,1)],'specified literal path')
 need(all(path[i][2]==path[i+1][0]for i in range(6))and path[-1][2]==9,'all control transitions and terminal')
 q=s=L=R=0;actual=[]
 for _ in range(7):
  actual.append([q,s,L,R]);q,d,w=transition[q,s]
  if d:s=L%2;L//=2;R=2*R+w
  else:s=R%2;R//=2;L=2*L+w
 need(actual==receipt['actual_first_seven_configurations']and [q,s,L,R]==[0,1,0,2]and actual[-1]==[8,0,0,5],'independent literal false-history simulation')
 B=mon(1);D=mon(1,Fraction(1,64));P=mon(7);J={e:Fraction(1)for e in range(7)}
 left=[C(0),C(0),C(1),C(0),C(0),mon(1,Fraction(1,2)),A(mon(1,Fraction(1,4)),C(1),-1)]
 right=list(map(C,(0,0,0,0,1,2,5)));popped=[C(path[j+1][1]if j<6 else 1)for j in range(7)]
 direction=[p[3]for p in path];writes=[p[4]for p in path];Lf=A(mon(1,Fraction(1,8)),C(1),-1);Rf=C(11)
 H,G,U=map(pack,(left,right,popped));ZL=pack([M(C(d),v)for d,v in zip(direction,left)]);ZR=pack([M(C(d),v)for d,v in zip(direction,right)]);ZU=pack([M(C(d),v)for d,v in zip(direction,popped)])
 aggregate={}
 for p in(H,G,ZL,ZR,ZU):aggregate=A(aggregate,p)
 expected=A(A(A(mon(7,Fraction(1,2)),mon(6,10)),mon(5,5)),A(mon(4,2),mon(2,3)))
 need(aggregate==expected,'entire aggregate family polynomial')
 beta=A(P,aggregate,-1);beta_positive=positive_shift(beta)
 E=[{j:Fraction(1)for j,k in enumerate(indices)if k==i}for i in range(29)]
 assignment={f'edge{i}':A(e,C(1))for i,e in enumerate(E)}
 assignment.update(L0=C(0),R0=C(0),height=D,H=H,G=G,U=U,ZL=ZL,ZR=ZR,ZU=ZU,Lfhat=A(Lf,C(1)),Rf=Rf,bound=beta)
 for n,p in assignment.items():
  if n not in('L0','R0'):positive_shift(p)
 for p in(H,G,U,ZL,ZR,ZU):positive_shift(A(P,p,-1))
 # Independently reconstruct both one-step tape residuals at every position.
 localleft=[];localright=[]
 for j,(d,w)in enumerate(zip(direction,writes)):
  nl=left[j+1]if j<6 else Lf;nr=right[j+1]if j<6 else Rf;r=popped[j]
  localleft.append(A(A(A(M(C(2),nl),M(C(4-3*d),left[j]),-1),C(2*(1-d)*w),-1),M(C(d),r)))
  localright.append(A(A(A(M(C(2),nr),M(C(1+3*d),right[j]),-1),C(2*d*w),-1),M(C(1-d),r)))
 need(localleft==[{}, {}, {}, {}, B,C(-1),{}]and localright==[{}]*7,'only the B,-1 left carry defect')
 need(not pack(localleft)and not pack(localright),'complete telescoped cancellation')
 Dir=pack([C(d)for d in direction]);masks=[M(A(B,C(1),-1),Dir),M(A(B,C(1),-1),Dir),Dir,M(A(D,C(1),-1),J),M(A(D,C(1),-1),J)]+[J]*29
 As=[H,G,U,H,G]+E;Zs=[ZL,ZR,ZU,H,G]+E;relaxed=list(masks);relaxed[3]=M(A(B,C(1),-1),J)
 def join(xs):
  out={}
  for i,p in enumerate(xs):out=A(out,M(mon(7*i),p))
  return out
 Ajoin,Mjoin,Zjoin,relaxedjoin=map(join,(As,masks,Zs,relaxed));delta=M(mon(21),M(A(B,D,-1),J));need(A(Mjoin,delta)==relaxedjoin,'literal lane3 delta, no other mask change')
 symbolic=[];counts=Counter()
 for p in raw:
  relabel=lambda q:{1:9,9:1}.get(q,q)
  need(p['table']==line and p['rules']==[[relabel(q),s,relabel(n),d,w]for q,s,n,d,w in rules],'actual relabeled controller preserves table edge numbering')
  need(p['outer_comparison_count']==5,'all outer comparisons selected')
  r=p['registers'];tags=p['tag_registers'];outputs=[v for pair in p['comparisons'][:5]for v in pair]+[r[n]for n in('B','D','P','J','Hjoin','Mjoin','Zjoin')]+list(tags.values())
  e,chosen,free=closure(p['source'],outputs,assignment);value=lambda v:e[v]if type(v)is str else C(v)
  need(all(not A(value(a),value(b),-1)for a,b in p['comparisons'][:5]),'all five actual outer residual polynomials vanish identically in formal B')
  for name,want in [('B',B),('D',D),('P',P),('J',J),('Hjoin',Ajoin),('Mjoin',Mjoin),('Zjoin',Zjoin)]:need(e[r[name]]==want,'actual semantic word '+name)
  T=mon(238);need(value(tags['A'])==A(Ajoin,mon(238,2))and value(tags['M'])==A(Mjoin,T)and value(tags['Z'])==Zjoin and value(tags['cap'])==mon(239),'all actual disjoint tags and cap')
  symbolic.append({'raw_polynomial_ledger':p['ledger']['polynomial'],'outer_closure_gates':len(chosen),'closure_free_coordinates':free,'all_outer_polynomials_zero':True,'all_joined_words_exact':True})
  counts['actual_formal_outer_residuals']+=5;counts['formal_source_gates']+=len(chosen);counts['formal_join_and_tag_outputs']+=11
 numeric=[]
 for exponent in (9,10,11,12,13,14,15,16,17,20,31,64):
  b=2**exponent;Pval=b**7;values=lambda ps:[int(evaluate(p,b))for p in ps];AA,MM,ZZ,RR=map(values,(As,masks,Zs,relaxed))
  need(all(Fraction(evaluate(p,b)).denominator==1 for p in assignment.values()),'all family coordinates integral at dyadic B')
  need(all(0<=v<Pval for xs in(AA,MM,ZZ,RR)for v in xs),'all lanes canonical within base P')
  need([i for i,(a,m,z)in enumerate(zip(AA,MM,ZZ))if a&m!=z]==[3],'precisely the existing left range lane fails')
  need(all(a&m==z for a,m,z in zip(AA,RR,ZZ)),'all34 lanes under only the left mask relaxation')
  av,mv,zv,rv=[int(evaluate(p,b))for p in(Ajoin,Mjoin,Zjoin,relaxedjoin)];t=Pval**34
  need(av&mv!=zv and av&rv==zv and(av+2*t)&(rv+t)==zv,'complete untagged/tagged relaxed relation')
  need((av+2*t)&(mv+t)!=zv and max(av+2*t,rv+t,zv)<b*t,'retained source rejects with valid tag/cap bounds')
  need(int(evaluate(beta,b))>0,'actual aggregate bound positive')
  if exponent<=16:
   f=next(f for f in receipt['fixtures']if f['B']==b);need(f['beta']==int(evaluate(beta,b))and f['left_digits']==values(left)and f['right_digits']==values(right)and f['Lf']==int(evaluate(Lf,b))and f['Rf']==11,'saved fixture arithmetic')
  numeric.append({'B_exponent':exponent,'left_digit_violations':[i for i,v in enumerate(values(left))if v>=b//64],'only_rejected_lane':3,'complete_relaxed_AND':True})
  counts['numeric_radices']+=1;counts['unchanged_numeric_lanes']+=33;counts['relaxed_numeric_lanes']+=34
 # Bounded exact-type replay of author's fresh CLI, not any historical suite.
 with tempfile.TemporaryDirectory(prefix='waterfall-obstruction-review-')as temp:
  out=Path(temp)/'author.json';cmd=[sys.executable,str(subject/'waterfall_packed_range_obstruction.py'),'--repo',str(repo),'--output',str(out),'--expect',str(subject/'waterfall_packed_range_obstruction.json')]
  proc=subprocess.run(cmd,capture_output=True,text=True,timeout=60);need(proc.returncode==0,'fresh author obstruction replay: '+proc.stderr);need(exact(json.loads(out.read_text()),receipt),'full author saved receipt reproduction');counts['author_obstruction_replays']=1
 return {'status':'PASS_INDEPENDENT_WATERFALL_RANGE_OBSTRUCTION','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'parent_pins':PINS,'counts':dict(counts),'literal_table':line,'edge_indices':list(indices),'actual_first_seven_configurations':actual,'actual_final':[q,s,L,R],'symbolic_forms':symbolic,'aggregate_polynomial':encoding(aggregate),'positive_bound_polynomial':encoding(beta),'bound_at_B512_plus_u':beta_positive,'left_local_residual_polynomials':[encoding(p)for p in localleft],'right_local_residual_polynomials':[encoding(p)for p in localright],'relaxed_mask_delta':encoding(delta),'numeric_fixtures':numeric,'scope':'Actual raw320/318 forms from the505 compiler: complete outer5 equations, all34 typed AND lanes and tags. Symbolic B family plus exact extra-radix checks. No complete native Pell assignment, no ordinary-input-slice zero, no actual nonhalting claim, and no defect in retained compiler.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--repo',type=Path,required=True);a.add_argument('--subject-root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.repo,v.subject_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved independent receipt')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
