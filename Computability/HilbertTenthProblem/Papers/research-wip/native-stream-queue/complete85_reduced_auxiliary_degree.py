#!/usr/bin/env python3
"""Complete85/degree155 deformation. Frozen sources are authenticated inert data."""
import argparse,copy,hashlib,json
from collections import Counter,deque
from pathlib import Path
PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete84_scaled_strong_output.md':'6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330',
 'review_complete85_auxiliary_bezout_source.md':'d8e8720f5287ef1069ce46f52369c532fb551d9611935065aa56210295ab2cd9',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d'}
COEFF='auxiliary_reduced_coefficient';OUT='polynomial'
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
P5=['norm_first','norm_main','norm_input','norm_index','norm_transport']
FINAL=[['norm_pair','*','norm_first','norm_main'],['norm_triple','*','norm_pair','norm_input'],
 ['norm_four','*','norm_triple','norm_aux'],['norm_product','*','norm_four','norm_index'],
 ['all_units','*','norm_product','norm_transport'],['seven_units','*','all_units','norm_strong'],
 ['polynomial','-','seven_units','A']]
def ck(v,msg):
 if not v:raise ValueError(msg)
def enc(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def sha(v):return hashlib.sha256(v).hexdigest()
def read(path):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(v):raise ValueError('noninteger JSON '+v)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  ck(type(n)is str and n not in d and o in ['+','-','*'],'SSA/op')
  ck(type(a)in [str,int] and type(b)in [str,int],'operand types');d[n]=(o,a,b)
 return d
def graph(rows,free):
 d=table(rows);seen=set(free);deps={};users={n:[] for n in d}
 for n,o,a,b in rows:
  ck(n not in seen and all(type(v)is int or v in seen for v in [a,b]),'paid topological operands')
  seen.add(n);deps[n]={v for v in [a,b] if v in d}
  for v in deps[n]:users[v].append(n)
 queue=deque(n for n in d if not deps[n]);count=0
 while queue:
  n=queue.popleft();count+=1
  for u in users[n]:
   deps[u].remove(n)
   if not deps[u]:queue.append(u)
 ck(count==len(rows),'independent acyclicity')
 live=set();todo=[OUT]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in d:todo.extend(d[n][1:])
 ck(live==set(d)|set(free),'all rows and supplied ports live')
 cc=Counter(r[1] for r in rows)
 return dict(total=len(rows),M=cc['*'],A=cc['+']+cc['-'])
def con(v):return {():v} if v else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 d=dict(a)
 for m,c in b.items():d[m]=d.get(m,0)+s*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items() if c}
def power(p,n):
 out=con(1)
 for _ in range(n):out=mul(out,p)
 return out
def product(ps):
 out=con(1)
 for p in ps:out=mul(out,p)
 return out
def expand(d,target,cuts):
 memo={n:var(n) for n in cuts}
 def at(n):
  if type(n)is int:return con(n)
  if n not in memo:
   ck(n in d,'uncut input '+n);o,a,b=d[n];aa,bb=at(a),at(b)
   memo[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
  return memo[n]
 return at(target)
def serial(p):return [dict(powers=dict(sorted(Counter(m).items())),coefficient=c) for m,c in sorted(p.items())]
def sum_polys(ps):
 out={}
 for p in ps:out=add(out,p)
 return out

def source_proofs(old,new):
 od,nd=table(old),table(new)
 cuts=set(P5)|{'R16','scaled_f_square','A','aux_u_rhs','y_aux'}
 oldF,newF=expand(od,OUT,cuts),expand(nd,OUT,cuts)
 D,q,u,V,y=[var(n) for n in ['A','R16','scaled_f_square','aux_u_rhs','y_aux']]
 strong=add(u,q,-1);gap=add(power(V,2),power(y,2),-1)
 expected=product([product(var(n) for n in P5),strong,add(strong,D,-1),gap])
 ck(add(newF,oldF,-1)==expected,'actual full finalizer correction')
 normalized=expand(nd,'norm_strong',{'A','R10a','i','f'})
 Ds,c,i,f=[var(n) for n in ['A','R10a','i','f']]
 normalized_strong=add(power(f,2),product([Ds,power(i,2),power(c,4)]),-1)
 ck(normalized==mul(Ds,normalized_strong),'actual scaled strong divisible by Delta')
 reduced=expand(nd,'norm_aux',{'A','f','aux_u_rhs','y_aux'})
 expected_aux=add(product([Ds,add(power(f,2),con(1),-1),gap]),power(y,2))
 ck(reduced==expected_aux,'actual reduced auxiliary factor')
 normalized_cuts=set(P5)|{'A','R10a','i','f','aux_u_rhs','y_aux'}
 integer_outputs={label:expand(defs,OUT,normalized_cuts) for label,defs in [('parent',od),('child',nd)]}
 ck(all(all('A' in mon for mon in p) for p in integer_outputs.values()),'both full outputs vanish identically when Delta=0')
 residues=[]
 for a in range(4):
  for f0 in range(4):
   for i0 in range(4):
    for c0 in range(4):
     DD=((a+1)*(a+3))%4;v=(f0*f0-DD*i0*i0*c0**4)%4
     ck(DD in [0,3] and v!=3,'normalized strong cannot be -1 modulo4')
     residues.append([a,f0,i0,c0,DD,v])
 return dict(full_correction=serial(expected),full_correction_terms=len(expected),
  correction_formula='Fnew-F84=P5*Ns_scaled*(Ns_scaled-Delta)*(V^2-y_aux^2)',
  scaled_strong_normalization=serial(normalized),reduced_auxiliary=serial(reduced),mod4_cases=residues,
  normalized_full_outputs={n:serial(p) for n,p in integer_outputs.items()},
  signed_integer_zero_equivalence='Delta!=0: divide then modulo4 forces normalized strong+1; Delta=0: both actual full outputs vanish identically.',
  symbolic_zero_argument='Delta>0 first; integer product P5*Na_new*Nstrong=1 gives Nstrong=+-1; modulo4 excludes -1. Then Ns_scaled=Delta and the auxiliary factors agree. Same argument at a parent zero gives the converse.')

def degree_proof(packet):
 rows=packet['source'];d=table(rows);fixed=set(packet['fixed_numerals'])
 main_cuts=['wn2','R12','R10a','gam','a4m5'];input_cuts=['W','R12','index_rhs','modulus_multiple','a4m5']
 cancellations={}
 for target,cuts in [('norm_main',main_cuts),('norm_input',input_cuts)]:
  X,a,c,G,H=[var(n) for n in cuts]
  want=sum_polys([power(X,2),product([con(2),a,c,X]),product([con(2),G,X]),
   product([con(2),a,c,G]),power(G,2),product([con(-1),H,power(c,2)])])
  actual=expand(d,target,set(cuts));ck(actual==want,'six-term actual norm cancellation '+target)
  cancellations[target]=actual
 raw={n:0 if n in fixed else 1 for n in packet['free']};deg=dict(raw);top={n:var(n) for n in packet['free']}
 for n,o,a,b in rows:
  da,db=[0 if type(x)is int else raw[x] for x in [a,b]];raw[n]=da+db if o=='*' else max(da,db)
  if n in cancellations:
   terms=[]
   for mon,c0 in cancellations[n].items():terms.append((sum(deg[v] for v in mon),product([con(c0)]+[top[v] for v in mon])))
   deg[n]=max(x[0] for x in terms);top[n]=sum_polys(p for e,p in terms if e==deg[n])
  else:
   da,db=[0 if type(x)is int else deg[x] for x in [a,b]]
   aa,bb=[con(x) if type(x)is int else top[x] for x in [a,b]]
   if o=='*':deg[n]=da+db;top[n]=mul(aa,bb)
   else:
    deg[n]=max(da,db);top[n]=add(aa if da==deg[n] else {},bb if db==deg[n] else {},1 if o=='+' else -1)
  ck(top[n],'unexpected complete leading cancellation '+n)
  ck(all(sum(x not in fixed for x in m)==deg[n] for m in top[n]),'homogeneous weighted leader '+n)
 Q=mul(var('Bm1'),var('Jrep'));k=add(var('eta'),var('zeta'));gamma=add(var('rho'),var('sigma'))
 w,s,h,T,f,ii,dd=[var(n) for n in ['w','s','h','auxiliary_quotient','f','i','delta']]
 C1=add(add(add(add(Q,var('F'),-1),var('Z'),-1),var('alpha'),-1),mul(var('twice_cell_bits'),var('x')),-1)
 transport=add(mul(w,C1),mul(var('transport_quotient'),Q),-1)
 expected=[product([con(-1),power(w,2),power(s,4),power(Q,14),power(k,2)]),
  product([con(8),power(w,2),power(s,3),power(Q,11),k,gamma]),
  product([con(-4),power(dd,2),power(w,5),power(s,5),power(Q,20)]),
  product([power(w,2),power(s,4),power(Q,14),power(k,2),power(T,2),power(f,4)]),
  product([con(-1),h,w,s,power(Q,4)]),transport,
  product([con(-1),power(ii,2),power(w,4),power(s,8),power(Q,28),power(k,4)])]
 ck([deg[n] for n in FACTORS]==[22,18,32,28,7,2,46],'seven exact factor degrees')
 ck([top[n] for n in FACTORS]==expected,'seven full symbolic factor leaders')
 leader=product([con(32),power(Q,91),h,gamma,power(dd,2),power(ii,2),power(k,9),power(w,16),power(s,25),transport,power(T,2),power(f,4)])
 ck(top[OUT]==product(expected)==leader,'full uniform symbolic degree155 leader')
 distinguished=Counter({'Jrep':92,'h':1,'rho':1,'delta':2,'i':2,'eta':9,'w':16,'s':25,'transport_quotient':1,'auxiliary_quotient':2,'f':4,'Bm1':92})
 mon=tuple(sorted(distinguished.elements()));ck(leader.get(mon)==-32,'uniform nonzero monomial coefficient')
 # No fixed numeral except Bm1 occurs with the same dynamic monomial.
 dynamic=tuple(x for x in mon if x not in fixed)
 selected=[(m,c0) for m,c0 in leader.items() if tuple(x for x in m if x not in fixed)==dynamic]
 ck(selected==[(mon,-32)],'no fixed-slice cancellation of distinguished coefficient')
 ck((deg[OUT],raw[OUT],deg['A'],deg[COEFF],deg['aux_u_rhs'])==(155,165,12,14,7),'exact/naive degree guards')
 return dict(exact_degree=155,naive_degree_bound=165,factor_degrees=[deg[n] for n in FACTORS],
  factor_leaders={n:serial(top[n]) for n in FACTORS},full_leader=serial(leader),full_leader_terms=len(leader),
  guarded_cancellations={n:serial(p) for n,p in cancellations.items()},
  bound_for_every_row=deg,naive_for_every_row=raw,
  distinguished_monomial=serial({mon:-32}),uniform_nonzero_coefficient='-32*Bm1^92; Bm1>0 on every valid fixed-program recipe')
def uni_trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def uni_add(a,b,prime,sign=1):
 out=[0]*max(len(a),len(b))
 for i,c in enumerate(a):out[i]=c
 for i,c in enumerate(b):out[i]=(out[i]+sign*c)%prime
 return uni_trim(out)
def uni_mul(a,b,prime):
 out=[0]*(len(a)+len(b)-1)
 for i,c in enumerate(a):
  if c:
   for j,e in enumerate(b):
    if e:out[i+j]=(out[i+j]+c*e)%prime
 return uni_trim(out)
def uni_values(rows,values,prime):
 e=copy.deepcopy(values)
 for n,o,a,b in rows:
  aa=e[a] if type(a)is str else [a%prime];bb=e[b] if type(b)is str else [b%prime]
  e[n]=uni_mul(aa,bb,prime) if o=='*' else uni_add(aa,bb,prime,1 if o=='+' else -1)
 return e
def dense_checks(old,new):
 out=[]
 for B,prime in [(16,1000000007),(32,1000000009)]:
  nums=dict(Bm1=B-1,Kconstant=3,twice_cell_bits=2,inner_bits=1,MC=5,MF=7)
  values={n:[nums[n]] if n in nums else [0,1] for n in new['free']}
  a,b=uni_values(old['source'],values,prime),uni_values(new['source'],values,prime)
  prod=[1]
  for n in P5:prod=uni_mul(prod,a[n],prime)
  correction=uni_mul(uni_mul(uni_mul(prod,a['norm_strong'],prime),uni_add(a['norm_strong'],a['A'],prime,-1),prime),a['aux_square_gap'],prime)
  ck(uni_add(b[OUT],a[OUT],prime,-1)==correction,'complete dense correction')
  ck([len(b[n])-1 for n in FACTORS]==[22,18,32,28,7,2,46],'dense seven factor degrees')
  ck(len(b[OUT])==156 and len(a[OUT])==188,'full dense degrees155/187')
  leading=(-32*(2**10)*5*pow(B-1,91,prime))%prime
  ck(b[OUT][-1]==leading and leading!=0,'dense specialization of uniform leader')
  changed={'L17','norm_aux','norm_four','norm_product','all_units','seven_units',OUT}
  ck(all(a[n]==b[n] for n in table(old['source']) if n not in changed),'all77 unaffected actual values')
  out.append(dict(B=B,prime=prime,parent_degree=187,child_degree=155,child_leading_coefficient=leading,
   child_polynomial_coefficients=b[OUT],parent_polynomial_sha256=sha(enc(a[OUT])),
   full_correction_verified=True,scope='Full-source dense univariate diagnostic; numeral assignments are not claimed to encode valid programs.'))
 return out

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'dependency '+n)
 parent=read(root/'complete84_scaled_strong_output.json');snapshot=enc(parent)
 ck(parent['source_sha256']==PINS['complete84_scaled_strong_output.py'],'parent helper binding')
 old=parent['packet'];od=table(old['source'])
 ck(len(old['source'])==84 and old['ledger']['M']==47 and old['ledger']['A']==37,'literal84 parent count')
 ck(old['exact_degree']==187 and old['factor_exact_degrees']==[22,18,32,60,7,2,46],'exact parent factor contract')
 ck(old['ordinary_input']=='x' and len(old['witnesses'])==18 and len(old['fixed_numerals'])==6,'ordinary18 witness interface')
 guards=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],['n2','*','Lbig','q'],
  ['wn2','*','w','q'],['sn2','*','s','n2'],['UM','*','wn2','sn2'],['R12','+','UM','sn2'],
  ['a_square','*','R12','R12'],['a4','*',4,'R12'],['a4m5','+','a4',3],['A','+','a_square','a4m5'],
  ['c2','*','R10a','R10a'],['Ac2','*','A','c2'],['aux_coefficient_root','*','i','Ac2'],
  ['R16','*','aux_coefficient_root','aux_coefficient_root'],['L16','*','f','f'],
  ['scaled_f_square','*','A','L16'],['norm_strong','-','scaled_f_square','R16'],
  ['H2','*','aux_u_rhs','aux_u_rhs'],['aux_y2','*','y_aux','y_aux'],['aux_square_gap','-','H2','aux_y2'],
  ['L17','*','R16','aux_square_gap'],['norm_aux','+','L17','aux_y2']]+FINAL
 ck(all(od[n]==(o,a,b) for n,o,a,b in guards),'actual discriminant/auxiliary/finalizer source guards')
 ck(COEFF not in od and COEFF not in old['free'],'fresh coefficient name')
 rows=[]
 for row in old['source']:
  if row[0]=='L17':
   rows.append([COEFF,'-','scaled_f_square','A']);rows.append(['L17','*',COEFF,'aux_square_gap'])
  else:rows.append(copy.deepcopy(row))
 nd=table(rows);ck(set(nd)-set(od)=={COEFF} and not(set(od)-set(nd)),'one added producer no deletion')
 ck({n for n in od if od[n]!=nd[n]}=={'L17'},'all83 other parent rows literal')
 ck([r[0] for r in rows if 'R16' in r[2:]]==['norm_strong'],'R16 still paid for scaled strong factor')
 ck(all(nd[n]==(o,a,b) for n,o,a,b in FINAL),'all seven finalizer rows literal')
 ck(graph(old['source'],old['free'])==dict(total=84,M=47,A=37),'parent independent ledger')
 ledger=graph(rows,old['free']);ck(ledger==dict(total=85,M=47,A=38),'complete85 paid ledger')
 child={k:copy.deepcopy(old[k]) for k in ['free','fixed_numerals','ordinary_input','witnesses']}
 child.update(source=rows,source_sha256=sha(enc(rows)),output=OUT,normalized=True,witness_domain='strictly positive integers',
  factors=FACTORS,factor_values_at_positive_zeros=[1,1,1,1,1,1,'A'],
  ledger=dict(ledger,core_M=41,core_A=37,core_total=78,finalizer_M=6,finalizer_A=1,finalizer_total=7),
  exact_degree=155,factor_exact_degrees=[22,18,32,28,7,2,46],full_polynomial_identity=False,
  all_ring_relation='Fnew-F84=P5*norm_strong*(norm_strong-A)*(aux_u_rhs^2-y_aux^2)',
  same_positive_zero_tuples=True,unrestricted_signed_zero_equivalence=True,coordinate_map='identity',
  scope='Complete ordinary-input universal polynomial on the unchanged valid fixed-program recipe; 85/155 improves the 85-operation degree point and does not lower the operation minimum84.')
 proof=source_proofs(old['source'],rows);degree=degree_proof(child);diagnostics=dense_checks(old,child)
 ck(enc(parent)==snapshot,'parent object unchanged')
 return dict(status='PASS_COMPLETE85_REDUCED_AUXILIARY_DEGREE',source_sha256=sha(Path(__file__).read_bytes()),
  pins=PINS,parent_source_sha256=sha(enc(old['source'])),packet=child,
  structural=dict(parent_rows=84,child_rows=85,unchanged_old_definitions=83,changed_old_definitions=['L17'],
   added_definition=[COEFF,'-','scaled_f_square','A'],finalizer_rows=FINAL,
   retained_R16_consumers=['norm_strong'],all_supplied_ports_live=True),
  polynomial_proof=proof,degree=degree,diagnostics=diagnostics,
  scope=dict(predecessor_execution=False,full_source=True,whole_polynomials_identical=False,
   identical_positive_zero_tuples=True,identical_integer_zero_tuples=True,positive_proof='integer unit product then modulo4 strong sign; no prior auxiliary decode',
   new_native_history_fixtures=False,exact_degree_uniform_on_valid_fixed_recipe=True,
   minimum_operation_result_unchanged='84 operations/exact degree187',lower_degree86_choices_not_superseded=True,
   no_minimality_claim=True))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'type-sensitive exact receipt replay')
 print(r['status'],r['packet']['ledger'],r['degree']['exact_degree'])
if __name__=='__main__':main()
