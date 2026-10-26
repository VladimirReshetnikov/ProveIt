"""Independently parse native TeX ports, exact pool chart and every unit pivot.
No renderer, builder, certificate checker, or producer arithmetic is imported.
"""
from pathlib import Path
from collections import defaultdict
import hashlib,json,re,sys
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release')
R=root/'reciprocal';P=root/'report';text=(P/'reciprocal_ledger.tex').read_text()
def need(q,msg):
 if not q:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(p):return {m:c for m,c in p.items() if c}
def poly(ts):
 d={}
 for c,m in ts:
  need(type(c)is int and c and isinstance(m,list) and all(type(i)is int and i>=0 for i in m) and m==sorted(m),'strict literal')
  need(tuple(m)not in d,'duplicate literal monomial');d[tuple(m)]=c
 return d
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return clean(d)
def scale(p,k):return clean({m:c*k for m,c in p.items()})
def mul(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
 return clean(d)
def sub(a,b):return add(a,scale(b,-1))
def prod(ps):
 out={():1}
 for p in ps:out=mul(out,p)
 return out
def sq(p):return mul(p,p)
def variable(v):return {(v,):1}
one={():1}
def tex_poly(s):
 parts=re.findall(r'[+-]?[^+-]+',s);need(''.join(parts)==s,'complete TeX arithmetic parse');out={}
 for part in parts:
  sign=-1 if part.startswith('-')else 1;b=part[1:]if part[:1]in '+-'else part;m=re.match(r'\d+',b);c=int(m[0])if m else 1;b=b[len(m[0]):]if m else b;mon=[]
  while b:
   x=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',b);need(x is not None,'TeX polynomial token');mon.extend([int(x[1])]*int(x[2] or 1));b=b[len(x[0]):]
  need(tuple(mon)not in out,'duplicate printed affine monomial');out[tuple(mon)]=sign*c
 return out
binding=read(P/'RECIPROCAL_LEDGER_BINDING.json');need(binding['tex_sha256']==sha(P/'reciprocal_ledger.tex'),'printed ledger exact hash')
for row in binding['inputs']:need(sha(R/row['path'])==row['sha256'],'ledger normative source hash')
c=read(R/'seeds/joint_13_frame/certificate.json');source=read(R/'source/pell209_affine.json');rows=[poly(r['terms'])for r in source['residuals']]
pair_lines=re.findall(r'^([0-9]+) & \$(.*?)\$ & \$(.*?)\$ & \$(.*?)\$ & \$(.*?)\$ & ([0-9]+) & ([0-9]+)\\\\$',text,re.M)
need(len(pair_lines)==13,'all printed13pairs');pairs={};omega={}
for line,expected in zip(pair_lines,c['pairs']):
 name='index'+line[0];need(name==expected['name'],'printed pair order');vals=[tex_poly(x)for x in line[1:5]]
 for key,value in zip(['k','X','Y','Z'],vals):need(value==poly(expected[key]),'every printed '+key+' coefficient')
 need([int(line[5]),int(line[6])]==[expected['gate_row'],expected['norm_row']],'printed gate/norm indices')
 k,X,Y,Z=vals;pairs[name]=(k,X,Y,Z);omega=add(omega,sq(sub(X,one)),sq(sub(Y,k)))
need(poly(c['Omega'])==omega,'printed actual orientation polynomial')
blocks=[]
for line in text.splitlines():
 m=re.fullmatch(r'([0-9]+) & \$(.*?)\$ & \$(.*?)\$\\\\',line)
 continuation=re.fullmatch(r' & & \$(.*?)\$\\\\',line)
 if m:
  need(int(m[1])==len(blocks),'printed block order');blocks.append({'base':tex_poly(m[2]),'requests':[]});req=m[3]
 elif continuation:need(blocks,'request continuation');req=continuation[1]
 else:continue
 parsed=re.findall(r'\((\d+),([^()]*)\)',req);need(',\\quad'.join('('+a+','+b+')'for a,b in parsed)==req,'all request tokens parsed')
 blocks[-1]['requests'] += [('index'+a,tex_poly(b))for a,b in parsed]
need(len(blocks)==4 and sum(len(b['requests'])for b in blocks)==15,'four blocks fifteen requests')
need('Put $A=x_{130}$ and $d=A-1$.'in text,'printed A,d chart')
A=variable(130);D=sub(A,one)
correction_match=re.search(r'\\widehat E_2=E_2\+R_\{(\d+)\}\+R_\{(\d+)\}',text)
list_match=re.search(r'\\mathcal J=\\\{([0-9,]+)\\\}',text)
need(correction_match and list_match,'printed exact retained-norm corrections')
corrections=[[],[],[int(correction_match[1]),int(correction_match[2])],list(map(int,list_match[1].split(',')))];TE=[]
for j,(b,expected)in enumerate(zip(blocks,c['blocks'])):
 need(b['base']==poly(expected['base']) and b['requests']==[(r['pair'],poly(r['m']))for r in expected['requests']],'every printed base/request coefficient')
 n=b['base'];H={};S={}
 for pair,m in b['requests']:
  k,X,Y,Z=pairs[pair];H=add(H,mul(Y,sub(m,X)));S=add(S,sq(add(m,scale(X,-1),Z)),scale(sq(Y),-1))
 T=add(scale(mul(A,n),2),scale(sq(n),-1),scale(one,-1));E=add(S,scale(mul(n,H),-2),*[rows[i]for i in corrections[j]])
 need(T==poly(expected['T']) and E==poly(expected['E']),'printed corrected Ehat and T reproduce every actual coefficient');TE.append((T,E))
orientation=re.search(r'\\Omega-\(R_\{(\d+)\}\+d x_\{(\d+)\}\)=-R_\{(\d+)\}',text)
need(orientation,'printed orientation exact identity');oi,ov,orr=map(int,orientation.groups());need(sub(omega,add(rows[oi],mul(D,variable(ov))))==scale(rows[orr],-1),'orientation identity every coefficient')
proxy_match=re.search(r'\\Omega\^\{\\prime\}=\\Omega\+R_\{(\d+)\}',text);need(proxy_match,'printed proxy correction');proxy=add(omega,rows[int(proxy_match[1])]);need(proxy==poly(c['orientation_proxy']),'printed orientation proxy every coefficient')
need(r'\mathcal P_I=\sum_{j\in I}\widehat E_j\prod_{h\in I\setminus\{j\}}T_h-z_I\prod_{j\in I}T_j'in text,'literal pool formula')
need(r'\Omega^{\prime} T_0+d\mathcal P_{\{0\}},\qquad\mathcal P_{\{1,2,3\}}'in text,'literal joint ordered rows')
removed_match=re.search(r'except \$([0-9,]+)\$, deletes coordinates \$([0-9,]+)\$',text);need(removed_match,'printed removed source labels');removed_rows=list(map(int,removed_match[1].split(',')));removed_vars=list(map(int,removed_match[2].split(',')))
need('additionally deletes row 135 and coordinate 191'in text and oi==135 and ov==191,'printed joint additional removal')
need(r'\mathcal P_{\{0,1\}}$ followed by $\mathcal P_{\{2,3\}}'in text,'printed sparse seed partition')
seeds={}
for name,partition,fused in [('plain_22',[[0,1],[2,3]],False),('joint_13_frame',[[0],[1,2,3]],True),('plain_13',[[0],[1,2,3]],False)]:
 rm=set(removed_rows)|({oi}if fused else set());rv=set(removed_vars)|({ov}if fused else set());kept=[i for i in range(209)if i not in rv];ren={i:j for j,i in enumerate(kept)};raw=[r for j,r in enumerate(rows)if j not in rm]
 for g,ids in enumerate(partition):
  z=209+g;ren[z]=len(kept)+g;den=prod([TE[i][0]for i in ids]);p=add(*[mul(TE[i][1],prod([TE[j][0]for j in ids if j!=i]))for i in ids],scale(mul(variable(z),den),-1))
  if fused and g==0:p=add(mul(proxy,den),mul(D,p))
  raw.append(p)
 eq=read(R/'seeds'/name/'equation.json');actual=[{tuple(sorted(ren[i]for i in m)):a for m,a in r.items()}for r in raw]
 need(actual==[poly(r['terms'])for r in eq['residuals']],'printed entire '+name+' seed coefficient identity');seeds[name]=eq
# Parse printed four-column blocks, then actually execute their monic substitutions.
def substitute(p,v,replacement):
 d=defaultdict(int);powers={0:one,1:replacement}
 for mon,c in p.items():
  e=mon.count(v)
  if not e:d[mon]+=c;continue
  if e not in powers:powers[e]=prod([replacement]*e)
  rest=tuple(i for i in mon if i!=v)
  for m,a in powers[e].items():d[tuple(sorted(rest+m))]+=c*a
 return clean(d)
proofs=[]
for name,title,seed in [('integer138_degree8','The 138 variable degree eight polynomial',source),('integer114_degree16','The sparse 114 variable degree sixteen polynomial',seeds['plain_22']),('integer113_degree16','The joint 113 variable degree sixteen polynomial',seeds['joint_13_frame'])]:
 body=text.split('\\subsection{'+title+'}',1)[1].split('\\subsection{',1)[0];printed={};columns=[[],[],[]]
 for line in body.splitlines():
  if not re.fullmatch(r'[ 0-9&-]+\\\\',line):continue
  fields=[v.strip()for v in line[:-2].split('&')];need(len(fields)==12,'three complete four-column blocks')
  for start in [0,4,8]:
   block=fields[start:start+4]
   if not any(block):continue
   need(all(re.fullmatch(r'-?\d+',v)for v in block),'printed integer pivot record');j,row,v,epsilon=map(int,block);need(j not in printed,'unique printed ordinal');printed[j]=(row,v,epsilon);columns[start//4].append(j)
 need(sum(columns,[])==list(range(len(printed))),'printed blockwise reading order')
 native=read(R/'equations'/name/'NATIVE_DEFINITION.json');cert=read(R/'equations'/name/'certificate.json');need(set(printed)==set(range(len(native['steps']))),'all ordered printed pivot ordinals');current={j:poly(r['terms'])for j,r in enumerate(seed['residuals'])};deleted=[]
 for j,st in enumerate(native['steps']):
  row,v,eps=printed[j];need((row,v,eps)==(st['row'],st['variable'],st['unit_coefficient']) and eps in [-1,1],'printed and normative pivot equality')
  need(row in current and current[row].get((v,))==eps and all(m==(v,)or v not in m for m in current[row]),'actual current unit pivot and no other occurrence');replacement=scale(sub(current[row],scale(variable(v),eps)),-eps)
  need(replacement==poly(st['definition']) and cert['steps'][j]['deleted_row']==row and cert['steps'][j]['variable']==v and replacement==poly(cert['steps'][j]['definition']),'actual normative pivot polynomial')
  del current[row];deleted.append(v);current={r:substitute(p,v,replacement)for r,p in current.items()}
 keep=[v for v in range(len(seed['variables']))if v not in deleted];need(keep==native['retained_original_indices']==cert['retained_original_indices'] and sorted(current)==native['retained_row_indices']==cert['retained_row_indices'],'printed final ordered complements')
 ren={v:i for i,v in enumerate(keep)};out=[{tuple(sorted(ren[v]for v in m)):c for m,c in current[r].items()}for r in sorted(current)];eq=read(R/'equations'/name/'equation.json');need(out==[poly(r['terms'])for r in eq['residuals']],'entire printed-ledger final polynomial residuals')
 proofs.append({'profile':name,'printed_pivots':len(printed),'variables':len(keep),'residuals':len(out),'literal_final_coefficients_equal':True})
print(json.dumps({'status':'PASS','tex_sha256':sha(P/'reciprocal_ledger.tex'),'printed_pairs':len(pairs),'printed_requests':15,'exact_norm_corrections':corrections,'source_orientation_identity':True,'source_proxy_identity':True,'all_three_seed_coefficients_equal':True,'normative_and_printed_pivots_replayed':proofs,'method':'Independent TeX arithmetic and integer-table parser with fresh exact polynomial ring, no producer or renderer imports.'},indent=2))
