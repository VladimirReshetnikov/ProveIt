"""Exact local substitution and 86-row graph audit; no zero-set claim."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;P=D.parent/'adaptive-first-root-factor87/candidate.json';raw=P.read_bytes();pin='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8'
if hashlib.sha256(raw).hexdigest()!=pin:raise RuntimeError('parent source pin changed')
def require(ok,message):
 if not ok:raise RuntimeError(message)
j=json.loads(raw);rows=j['source'];w=j['witnesses'];ports=j['fixed_numerals'];require(w.count('u')==1 and 'y' not in w,'unexpected witness names');uses=[(i,row) for i,row in enumerate(rows) if 'u' in row[2:]];require(len(uses)==1 and uses[0][1]==['g78','+','V','u'],'unexpected offset use');require(all(row[0]!='y' for row in rows),'new name conflicts')
new=[]
for row in rows:
 if row[0]=='g78':continue
 new.append([row[0],row[1],*[('y' if a=='g78' else a) for a in row[2:]]])
w2=['y' if x=='u' else x for x in w]
def check(rows,w):
 seen=set(w+ports+['0','1','2','3','4']);table={};kinds={'+':0,'-':0,'*':0}
 for row in rows:
  n,o,a,b=row
  if n in seen or str(a) not in seen or str(b) not in seen or o not in kinds:raise RuntimeError(('invalid row',row))
  seen.add(n);table[n]=row;kinds[o]+=1
 todo=['P13'];live=set()
 while todo:
  n=todo.pop()
  if n in live:continue
  live.add(n)
  if n in table:todo.extend(map(str,table[n][2:]))
 return {'rows':len(rows),'live_operations':len(live&set(table)),'operation_breakdown':kinds,'all_witnesses_live':all(x in live for x in w),'all_ports_live':all(x in live for x in ports)}
a=check(rows,w);b=check(new,w2);require(a['live_operations']==87 and b['live_operations']==86 and b['rows']==86 and b['all_witnesses_live'] and b['all_ports_live'],'unexpected topology or liveness')
# Sparse integer polynomial arithmetic in V, y and Q. Exponents are tuples.
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
V={(1,0,0):1};Y={(0,1,0):1};Q={(0,0,1):1};uold=sub(Y,V);oldy=add(V,uold);oldaux=sub(mul(oldy,oldy),mul(Q,sub(mul(oldy,oldy),mul(V,V))));newaux=sub(mul(Y,Y),mul(Q,sub(mul(Y,Y),mul(V,V))));require(oldaux==newaux,'local identity failed')
wrong=add(Y,V);wrongaux=sub(mul(wrong,wrong),mul(Q,sub(mul(wrong,wrong),mul(V,V))));require(wrongaux!=newaux,'mutated sign was not rejected')
out={'name':'adaptive-direct-positive-ordinate86','scope':'Candidate graph and exact local integer-polynomial substitution only; no natural zero-set equivalence, full Lean binding, HA proof, degree certificate or minimality claim.','parent_sha256':pin,'witnesses':w2,'fixed_numerals':ports,'source':new,'output':'P13','operations':86,'operation_breakdown':b['operation_breakdown'],'removed_row':uses[0][1],'substitution':'u_old = y_new - V','conditional_status':'Requires positive old-offset recovery and both literal zero-set directions in all models.'}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n');result={'parent':a,'candidate':b,'parent_sha256':pin,'candidate_sha256':hashlib.sha256((D/'candidate.json').read_bytes()).hexdigest(),'old_offset_only_used_in_removed_row':True,'retained_rows_unchanged_except_ordinate_substitution':True,'exact_local_polynomial_identity':oldaux==newaux,'mutated_sign_rejected':wrongaux!=newaux,'scope':out['scope']};(D/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
