"""Construct and audit a conditional 85-gate gap-witness substitution."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;P=D.parent/'adaptive-direct-ordinate86/candidate.json';raw=P.read_bytes();pin='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'
def req(c,msg):
 if not c:raise RuntimeError(msg)
req(hashlib.sha256(raw).hexdigest()==pin,'unexpected parent hash')
j=json.loads(raw);old=j['source'];w=j['witnesses'];ports=j['fixed_numerals']
req(w.count('alpha')==1 and 'C' not in w,'unexpected input names')
req([r for r in old if 'alpha' in r[2:]]==[['C','-','qF','alpha'],['G','+','alpha','g44']],'unexpected alpha uses')
req([r for r in old if r[0]=='g44']==[['g44','*','qF','qm']],'unexpected rank product')
new=[]
for r in old:
 if r[0]=='C':continue
 if r[0]=='g44':new.append(['g44','*','qF','q'])
 elif r[0]=='G':new.append(['G','-','g44','C'])
 else:new.append(r)
w2=['C' if x=='alpha' else x for x in w]
def stats(rows,variables):
 seen=set(variables+ports+['0','1','2','3','4']);table={};kinds={'+':0,'-':0,'*':0}
 for n,op,a,b in rows:
  req(n not in seen and str(a) in seen and str(b) in seen and op in kinds,('topology',n));seen.add(n);table[n]=(n,op,a,b);kinds[op]+=1
 todo=['P13'];live=set()
 while todo:
  x=todo.pop()
  if x in live:continue
  live.add(x)
  if x in table:todo.extend(str(a) for a in table[x][2:])
 return {'rows':len(rows),'live_operations':len(live&set(table)),'operation_breakdown':kinds,'all_witnesses_live':all(x in live for x in variables),'all_ports_live':all(x in live for x in ports)}
a=stats(old,w);b=stats(new,w2);req(a['live_operations']==86 and b['rows']==b['live_operations']==85 and b['all_witnesses_live'] and b['all_ports_live'],'unexpected liveness')
# Exact sparse integer-polynomial arithmetic in q, F and C. q-1 is qm.
def add(a,b):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {k:v for k,v in c.items() if v}
one={(0,0,0):1};q={(1,0,0):1};F={(0,1,0):1};C={(0,0,1):1};qF=sub(q,F);alpha=sub(qF,C);qm=sub(q,one)
req(sub(qF,alpha)==C,'gap substitution failed');req(add(alpha,mul(qF,qm))==sub(mul(qF,q),C),'rank identity failed')
# Under the substitution all untouched rows receive identical inputs; the two
# changed rank rows and removed gap row have just been checked in Z[q,F,C].
req([r for r in old if r[0] not in ('C','g44','G')]==[r for r in new if r[0] not in ('g44','G')],'unexpected changes elsewhere')
out={'name':'adaptive-gap-witness85','scope':'Conditional 85-gate candidate and exact integer-polynomial substitution; no unqualified positive zero-set equivalence, Lean binding, HA theorem, degree or minimality claim.','parent_sha256':pin,'witnesses':w2,'fixed_numerals':ports,'source':new,'output':'P13','operations':85,'operation_breakdown':b['operation_breakdown'],'substitution':'alpha_old = q - F - C_new','conditional_status':'Old-to-new needs q-F-alpha>0; new-to-old needs C<q-F to recover alpha>0.'}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n');result={'parent':a,'candidate':b,'parent_sha256':pin,'candidate_sha256':hashlib.sha256((D/'candidate.json').read_bytes()).hexdigest(),'untouched_rows_structurally_identical':True,'gap_and_rank_exact_integer_polynomial_identities':True,'scope':out['scope']};(D/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
