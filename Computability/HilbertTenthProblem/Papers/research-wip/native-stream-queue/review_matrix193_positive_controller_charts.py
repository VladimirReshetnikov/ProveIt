#!/usr/bin/env python3
"""Independent inert-data audit of the six frozen positive controller charts."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path

AUTHOR = {
 'matrix193_positive_controller_charts.py':'b21efd94fab1ce963f39805f46721b5d69c39caf926711764d0a25a6ccbcb1a1',
 'matrix193_positive_controller_charts.json':'73eeb092a3ae9f4a9186a7b05f910024c7839c5f76c09dab535ee5b92668ae12',
 'matrix193_positive_controller_charts.md':'e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c'}
PARENT = {
 'matrix193_composed_output_scout.py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317',
 'matrix193_composed_output_scout.json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37',
 'matrix193_composed_output_scout.md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}
def require(ok, message):
 if not ok: raise ValueError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read_json(path):
 def pairs(xs):
  d={}
  for k,v in xs:
   require(k not in d,'duplicate JSON key'); d[k]=v
  return d
 return json.loads(path.read_text(),object_pairs_hook=pairs)
def identical(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(identical(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(identical(x,y) for x,y in zip(a,b))
 return a==b

# Sparse integer polynomials with sorted variable/exponent tuples. Used only
# at explicitly bounded controller and main-norm cuts, never for the huge DAG.
def constant(k): return {():k} if k else {}
def variable(x): return {((x,1),):1}
def plus(a,b,sign=1):
 out=dict(a)
 for mon,c in b.items():
  out[mon]=out.get(mon,0)+sign*c
  if not out[mon]: del out[mon]
 return out
def times(a,b):
 out={}
 for ma,ca in a.items():
  for mb,cb in b.items():
   m=dict(ma)
   for v,e in mb: m[v]=m.get(v,0)+e
   key=tuple(sorted(m.items())); out[key]=out.get(key,0)+ca*cb
 return {k:v for k,v in out.items() if v}
def arithmetic(op,a,b): return times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
def expand(rows,target,cuts):
 lookup={r[0]:r for r in rows}; env=dict(cuts)
 def get(x):
  if type(x) is int:return constant(x)
  if x not in env:
   require(x in lookup,'unbound polynomial cut '+x)
   _,op,a,b=lookup[x]; env[x]=arithmetic(op,get(a),get(b))
  return env[x]
 return get(target)
def encode(poly): return [[list(map(list,m)),c] for m,c in sorted(poly.items())]

def graph(packet):
 free=packet['free'];require(len(set(free))==len(free),'duplicate free port')
 known=set(free);deps={};counts=Counter()
 for row in packet['source']:
  require(type(row) is list and len(row)==4,'row arity')
  n,op,a,b=row; require(type(n)is str and n not in known and op in ['+','-','*'],'row definition')
  require(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'topological closure')
  deps[n]=(a,b);known.add(n);counts[op]+=1
 live=set();todo=[packet['output']]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:live.add(n);todo.extend(deps.get(n,()))
 require(live==known,'all rows/ports live')
 return {'rows':len(deps),'M':counts['*'],'A':counts['+']+counts['-'],'free_ports':len(free),'positive_witnesses':len(packet['witnesses']),'all_live':True,'array_sha256':digest(canonical(packet['source']))}

def controller(parent,child):
 rows=parent['source'];by={r[0]:r for r in rows};ports=parent['ports'];mp=child['map'];pop=child['population_chart'];flow=child['flow_chart']
 E,S=ports['raw_edges'];h0,h1=ports['edge_hats'][:2];B=ports['B'];J=ports['J'];P=ports['P']
 require(by[E]==[E,'-',h0,1] and by[S]==[S,'-',h1,1],'raw edge hats')
 require(by[P][1]=='+' and by[P][3]==1,'P affine row');prod=by[by[P][2]];bm=prod[2]
 require(prod[1]=='*' and prod[3]==J and by[bm]==[bm,'-',B,1],'P=(B-1)J+1')
 require(by[B]==[B,'*','radix_multiplier',ports['D']],'positive B recipe')
 drow=by[ports['D']];require(drow[1:] == ['+',by[ports['D']][2],'height_slack'],'D slack')
 require(by[drow[2]]==[drow[2],'+','x','Hfix'],'D ordinary input recipe')
 hats=ports['edge_hats'];jexpected=constant(-parent['n'])
 for h in hats:jexpected=plus(jexpected,variable(h))
 require(expand(rows,J,{h:variable(h) for h in hats})==jexpected,'J exact total edge sum')
 tail=rows[-62:];residuals=[]
 for i,(a,b) in enumerate(parent['comparisons']):
  rn=tail[2*i][0];require(tail[2*i]==[rn,'-',a,b],'literal parent comparison')
  require(tail[2*i+1][1:]==['*',rn,rn],'literal parent square');residuals.append(rn)
 squares=[tail[2*i+1][0] for i in range(20)];acc=squares[0]
 for i,row in enumerate(tail[40:59]):
  require(row[1:]==['+',acc,squares[i+1]],'complete SOS sum');acc=row[0]
 require(tail[59][1:]==['+',acc,1] and tail[60][1:]==['*','eight_units',tail[59][0]] and tail[61][1:]==['-',tail[60][0],1],'complete integer finalizer')
 b,j,x,u,e,s=[variable(v) for v in ['b','j','x','u','e','s']]
 cuts={bm:b,B:plus(b,constant(1)),J:j,E:e,S:s,'x':x,'population_quotient':u}
 fr=expand(rows,residuals[18],cuts);pr=expand(rows,residuals[19],cuts)
 require(fr==plus(plus(constant(1),times(b,e)),s,-1),'flow residual identity')
 require(pr==plus(plus(x,times(b,plus(u,constant(1),-1))),e,-1),'population residual identity')
 ee=plus(x,times(b,plus(u,constant(1),-1))) if pop else plus(variable(h0),constant(1),-1)
 ss=plus(constant(1),times(b,ee)) if flow else plus(variable(h1),constant(1),-1)
 newcuts={mp[bm]:b,'x':x,'population_quotient':u}
 for h in [h0,h1]:
  if h in child['free']:newcuts[h]=variable(h)
 require(expand(child['source'],mp[E],newcuts)==ee,'computed LOAD raw exact')
 require(expand(child['source'],mp[S],newcuts)==ss,'computed SWITCH raw exact')
 for flag,h,raw in [(pop,h0,ee),(flow,h1,ss)]:
  if flag:require(expand(child['source'],mp[h],newcuts)==plus(raw,constant(1)),'computed missing hat exact')
 sub=dict(cuts);sub[E]=ee;sub[S]=ss
 for flag,r in [(flow,residuals[18]),(pop,residuals[19])]:
  if flag:require(not expand(rows,r,sub),'removed residual identically zero')
 removed=[h for flag,h in [(pop,h0),(flow,h1)] if flag]
 require(child['free']==[v for v in parent['free'] if v not in removed],'exact free list')
 require(child['witnesses']==[v for v in parent['witnesses'] if v not in removed],'exact witness list')
 require(child['fixed_numerals']==parent['fixed_numerals'] and child['fixture_fixed_bindings']==parent['fixture_fixed_bindings'],'unchanged fixed recipe')
 # Authenticate the special population-only cancellations used in the degree audit.
 left,right=parent['comparisons'][18];src=by[left][2];dst=by[right][3]
 require(by[left][1:]==['+',src,P] and by[right][1:]==['*',B,dst],'flow comparison shape')
 for name,start in [(dst,1),(src,2)]:
  target=constant(-(len(hats)-start))
  for h in hats[start:]:target=plus(target,variable(h))
  require(expand(rows,name,{h:variable(h) for h in hats})==target,'exact remaining-edge controller sum')
 return {'bm':bm,'E':E,'S':S,'h0':h0,'h1':h1,'dst':dst,'src':src,'residuals':residuals,'flow_polynomial':encode(fr),'population_polynomial':encode(pr)}

class Terms:
 def __init__(self):self.ids={}
 def c(self,k):return ('c',k)
 def op(self,o,a,b):
  if a[0]=='c' and b[0]=='c':return self.c(a[1]*b[1] if o=='*' else a[1]+b[1] if o=='+' else a[1]-b[1])
  if o=='*' and self.c(0) in [a,b]:return self.c(0)
  if o=='*' and a==self.c(1):return b
  if o=='*' and b==self.c(1):return a
  if o in ['+','-'] and b==self.c(0):return a
  if o=='+' and a==self.c(0):return b
  if o=='-' and a==b:return self.c(0)
  key=(o,a,b)
  if key not in self.ids:self.ids[key]=len(self.ids)
  return ('node',self.ids[key])

def full_pullback(parent,child,contract):
 ring=Terms();fresh={n:('port',n) for n in child['free']}
 def val(env,v):return ring.c(v) if type(v)is int else env[v]
 for n,o,a,b in child['source']:fresh[n]=ring.op(o,val(fresh,a),val(fresh,b))
 mp=child['map'];old={n:('port',n) for n in child['free']};overrides={}
 for flag,h,raw in [(child['population_chart'],contract['h0'],contract['E']),(child['flow_chart'],contract['h1'],contract['S'])]:
  if flag:old[h]=val(fresh,mp[h]);overrides[raw]=val(fresh,mp[raw])
 certified=[]
 for flag,i in [(child['flow_chart'],18),(child['population_chart'],19)]:
  if flag:overrides[contract['residuals'][i]]=ring.c(0);certified.append(contract['residuals'][i])
 require(sorted(certified)==child['removed_residuals'],'only certified residuals removed')
 for n,o,a,b in parent['source']:old[n]=overrides[n] if n in overrides else ring.op(o,val(old,a),val(old,b))
 for n,target in mp.items():require(old[n]==val(fresh,target),'mapped parent register '+n)
 require(old[parent['output']]==fresh[child['output']],'complete output pullback')
 require(child['retained_residual_wires']==[mp[n] for n in contract['residuals'] if n not in certified],'retained residual inventory')
 return {'all_parent_rows_interpreted':len(parent['source']),'mapped_registers':len(mp),'exact_whole_output':True,'removed_residuals':certified}

def main_expansion(parent):
 aliases={'selection__wn2':'X','selection__R12':'a','selection__R10a':'c','selection__ga':'g','selection__a4m5':'H'}
 p=expand(parent['source'],'selection__R15',{k:variable(v) for k,v in aliases.items()})
 X,a,c,g,H=[variable(v) for v in ['X','a','c','g','H']]
 square=times(plus(plus(X,times(a,c)),times(g,H)),plus(plus(X,times(a,c)),times(g,H)))
 expected=plus(square,times(plus(times(a,a),H),times(c,c)),-1)
 require(p==expected and len(p)==6,'literal six-term main norm')
 return p,aliases

def pure_q(rows,q):
 env={q:{1:1}}
 for n,o,a,b in rows:
  if n==q:continue
  if not all(type(v)is int or v in env for v in [a,b]):continue
  aa=({0:a} if a else {}) if type(a)is int else env[a]
  bb=({0:b} if b else {}) if type(b)is int else env[b]
  if o=='*':
   out={}
   for i,u in aa.items():
    for j,v in bb.items():out[i+j]=out.get(i+j,0)+u*v
  else:
   out=dict(aa)
   for j,v in bb.items():out[j]=out.get(j,0)+(v if o=='+' else -v)
  env[n]={i:v for i,v in out.items() if v}
 return env

def degrees(parent,child,contract,main_poly,aliases):
 mod=1000000007;mp=child['map'];q=mp[parent['ports']['Q']];qp=pure_q(child['source'],q);env={}
 # Fresh line, distinct from both author leader checks and dense diagnostics.
 for i,n in enumerate(child['free']):
  c=child['fixture_fixed_bindings'][n]%mod if n in child['fixed_numerals'] else ((i+5)**3+11)%mod
  env[n]=(0 if n in child['fixed_numerals'] else 1,c) if c else (-1,0)
 def get(v):return env[v] if type(v)is str else ((0,v%mod) if v%mod else (-1,0))
 overrides=[]
 for n,o,a,b in child['source']:
  da,ca=get(a);db,cb=get(b)
  if o=='*':value=(-1,0) if min(da,db)<0 else (da+db,ca*cb%mod)
  else:
   d=max(da,db);value=(d,((ca if da==d else 0)+(cb if db==d else 0)*(1 if o=='+' else -1))%mod)
  if n in qp and n!=q:
   poly=qp[n]
   if poly:
    d=max(poly);dq,cq=env[q];value=(d*dq,poly[d]*pow(cq,d,mod)%mod)
   else:value=(-1,0)
  if child['population_chart'] and not child['flow_chart']:
   for key,start in [('dst',1),('src',2)]:
    if n==mp[contract[key]]:
     value=(1,sum(env[h][1] for h in parent['ports']['edge_hats'][start:])%mod);overrides.append(key)
  if n==mp['selection__R15']:
   variable_leads={label:get(mp[old]) for old,label in aliases.items()};terms=[]
   for mon,coef in main_poly.items():
    d=0;c=coef%mod
    for var,e in mon:
     vd,vc=variable_leads[var];d+=vd*e;c=c*pow(vc,e,mod)%mod
    terms.append((d,c,mon))
   largest=max(d for d,c,mon in terms);top=[t for t in terms if t[0]==largest]
   require(len(top)==1 and dict(top[0][2])=={'a':1,'c':1,'g':1,'H':1},'unique maximal six-term main norm')
   value=(largest,top[0][1]);overrides.append('main norm six-term expansion')
  if value==(0,0):value=(-1,0)
  require(value[0]<0 or value[1]!=0,'unexpected leader cancellation '+n)
  env[n]=value
 s=4 if child['chart']=='both' else 3;N=parent['L']+parent['m']+4;d=N*s+1;lm=max(e['length'] for e in parent['extraction'])
 expected=[5*d-s+4,9*d-2*s+5,6*d+14,4*d-s+2,4*d-s+2,8*d-2*s+4,s]
 factor_names=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
 factors=[]
 for name,target in zip(factor_names,expected):
  require(env[mp[name]][0]==target,'factor degree '+name);factors.append([name,*env[mp[name]]])
 require(env[q][0]==s and env[mp[parent['ports']['q']]][0]==d,'scale degrees')
 residual_degrees=[env[n][0] for n in child['retained_residual_wires']]
 require(max(residual_degrees)==s*(2*lm-1),'exact largest residual degree')
 degree=(36*N+4*lm-8)*s+67
 require(env[child['output']][0]==degree==child['ledger']['proved_exact_degree'],'complete degree')
 leaders=[e['products'][j]['coefficients'][0] for e in parent['extraction'] for j in [0,1]]
 require(parent['padding']%2==0 and parent['padding']//2>max(map(abs,leaders)),'valid-numeral population tie nonvanishing')
 return {'modulus':mod,'fresh_slope':'(i+5)^3+11 in the recorded free-list order','all_rows_processed':len(child['source']),'exact_degree':degree,'leading_coefficient_mod':env[child['output']][1],'native_factors':factors,'residual_degrees':residual_degrees,'pure_Q_polynomials':len(qp),'certified_special_overrides':overrides,'population_tie_margin_verified':True}

def run(root,author_root):
 for directory,pins in [(root,PARENT),(author_root,AUTHOR)]:
  for name,pin in pins.items():require(digest((directory/name).read_bytes())==pin,'pin '+name)
 parent=read_json(root/'matrix193_composed_output_scout.json');author=read_json(author_root/'matrix193_positive_controller_charts.json')
 require(author['source_sha256']==AUTHOR['matrix193_positive_controller_charts.py'] and author['pins']==PARENT,'author receipt provenance')
 require(parent['source_sha256']==PARENT['matrix193_composed_output_scout.py'],'parent source provenance')
 require(len(parent['packets'])==2 and len(author['packets'])==6,'packet inventory')
 results=[]
 for i,child in enumerate(author['packets']):
  old=parent['packets'][i//3];require(child['name']==old['name'] and child['chart']==['flow','population','both'][i%3],'packet order')
  require(child['population_chart']==(i%3!=0) and child['flow_chart']==(i%3!=1),'chart flags')
  ledger=graph(child);require(all(ledger[k]==child['ledger'][k] for k in ['M','A','positive_witnesses']),'count metadata')
  require(ledger['rows']==child['ledger']['total'],'total metadata')
  ctl=controller(old,child);pull=full_pullback(old,child,ctl);main,aliases=main_expansion(old);deg=degrees(old,child,ctl,main,aliases)
  results.append({'layout':child['name'],'chart':child['chart'],'ledger':ledger,'flow_polynomial':ctl['flow_polynomial'],'population_polynomial':ctl['population_polynomial'],'main_norm_polynomial':encode(main),'pullback':pull,'degree_check':deg})
 require([r['ledger']['rows'] for r in results]==[298,300,295,1674,1676,1671],'six expected paid arrays')
 return {'schema':'independent-positive-controller-charts-review-v1','review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR,'parent_pins':PARENT,'results':results,'total_rows_checked':sum(r['ledger']['rows'] for r in results),'scope':{'predecessor_or_author_code_executed':False,'all_ring_pullbacks':True,'positive_integer_zero_bijection':'proved in companion, valid fixed recipe and natural x','global_multivariate_output_expansion':False,'new_accepting_or_native_Pell_fixture':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=run(a.root,a.author_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:require(identical(result,read_json(a.expect)),'type-exact review receipt')
 print('PASS: six full arrays, 5914 rows, controller/main-norm expansions, exact whole-source pullbacks, independent degree leaders')
if __name__=='__main__':main()
