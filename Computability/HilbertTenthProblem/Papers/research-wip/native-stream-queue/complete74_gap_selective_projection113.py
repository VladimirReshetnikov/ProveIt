#!/usr/bin/env python3
"""A complete degree-28 universal SOS and 256 selective positive graph projections.

All inherited sources are authenticated JSON, never imported Python modules.
The finite family is not a lower bound on other universal polynomial circuits.
"""
from __future__ import annotations
import argparse,copy,hashlib,itertools,json,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('run without -O')
PINS={
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
 'complete75_positive_elimination.json':'03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703',
 'complete75_positive_elimination.md':'59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b',
 'complete75_positive_root89.py':'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72',
 'complete75_positive_root89.md':'7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085',
 'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
}
DEFINITIONS={'q':('q',0),'C':('marked_rhs',4),'k':('R10b',7),'a':('R12',9),'c':('R10a',6),'d':('R14',10),'kappa':('index_rhs',15),'mu':('exponent_rhs',18)}
DEFAULT=('q','C','k','d','kappa','mu')
CONSTANTS=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def need(ok,message):
 if not ok: raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k])for k in a)
 if type(a)in(tuple,list):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def authenticate(root):
 root=Path(root)if root is not None else Path(__file__).resolve().parent
 for n,pin in PINS.items():need(sha((root/n).read_bytes())==pin,'parent pin '+n)
 return root

def canonical_parent(*,root=None):
 root=authenticate(root)
 p=json.loads((root/'complete74_factored_first_norm.json').read_text())['forms'][0]['packet']
 need(p['mode']=='raw30'and len(p['source'])==74 and len(p['comparisons'])==19,'literal raw74 interface')
 return p

def selection(eliminated):
 need(type(eliminated)is tuple and all(type(v)is str for v in eliminated),'exact tuple selection')
 need(eliminated==tuple(v for v in DEFINITIONS if v in eliminated),'canonical ordered subset')
 return eliminated

def execute(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b]
  d[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return d

def inspect(rows,free,terminals):
 ready=set(free);deps={};degrees={v:0 if v in CONSTANTS else 1 for v in free};m=0
 for n,op,a,b in rows:
  need(type(n)is str and n not in ready and op in ('+','-','*'),'fresh operation')
  need(all(type(v)is int or type(v)is str and v in ready for v in(a,b)),'exact closed operands')
  da=0 if type(a)is int else degrees[a];db=0 if type(b)is int else degrees[b]
  degrees[n]=da+db if op=='*'else max(da,db);deps[n]=(a,b);ready.add(n);m+=op=='*'
 live=set();stack=list(terminals)
 while stack:
  v=stack.pop()
  if type(v)is str and v not in live:live.add(v);stack.extend(deps.get(v,()))
 need(set(deps)<=live and set(free)<=live,'all gates and supplied coordinates live')
 return {'operations':len(rows),'M':m,'A':len(rows)-m,'all_gates_live':True,'free':sorted(free)},degrees

def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out += [[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
 name='square_0'
 for i in range(1,len(pairs)):
  nextname=f'sum_{i}';out.append([nextname,'+',name,f'square_{i}']);name=nextname
 return out,name

def _build(p,eliminated):
 selection(eliminated)
 aliases={v:DEFINITIONS[v][0]for v in eliminated if v!='q'}
 nodes={n:[op,a,b]for n,op,a,b in p['source']}
 guards={'UM':['*','wn2','sn2'],'ksn2':['*','k','sn2'],'first_root_base':['*','UM','ksn2'],'first_next':['+','first_root_base','k'],'L9':['*','first_root_base','first_next'],'tau_square':['*','tau','tau'],'R9':['-','tau_square',1]}
 need(all(exact(nodes[n],r)for n,r in guards.items()),'raw independent k and first root source')
 need([r[0]for r in p['source']if 'tau'in r[2:]]==['tau_square'],'private root coordinate')
 need([r[0]for r in p['source']if 'first_next'in r[2:]]==['L9'],'private first-next register')
 nodes['tau_square']=['*','tau_gap','tau_gap'];nodes['R9']=['-',1,'tau_square'];del nodes['first_next']
 nodes['twice_tau_gap']=['+','tau_gap','tau_gap'];nodes['first_signed_gap']=['-','twice_tau_gap','k'];nodes['L9']=['*','first_root_base','first_signed_gap']
 if 'q'in eliminated:
  del nodes['qm1'];nodes['q']=['+','repunit',1];aliases['qm1']='repunit'
 witnesses=[n if n!='tau'else'tau_gap'for n in p['witnesses']if n not in eliminated]
 rows=[];done=set(witnesses+CONSTANTS+['x']);active=set()
 def visit(v):
  if type(v)is int:return v
  v=aliases.get(v,v)
  if v not in done:
   need(v not in active,'acyclic definitions');active.add(v)
   op,a,b=nodes[v];a=visit(a);b=visit(b);rows.append([v,op,a,b]);done.add(v);active.remove(v)
  return v
 deleted=[DEFINITIONS[v][1]for v in eliminated];pairs=[];indices=[]
 for i,(a,b)in enumerate(p['comparisons']):
  if i in deleted:continue
  if i==5:a,b=b,a
  pairs.append([visit(a),visit(b)]);indices.append(i)
 free=witnesses+CONSTANTS+['x'];cert,degrees=inspect(rows,free,[v for pair in pairs for v in pair]);poly,output=finalize(rows,pairs);ledger,_=inspect(poly,free,[output])
 need((cert['operations'],cert['M'],cert['A'])==(75,40,35),'complete comparison cost')
 def deg(v):return 0 if type(v)is int else degrees[aliases.get(v,v)]
 residual_degrees=[max(deg(a),deg(b))for a,b in pairs]
 # Exact polynomial cancellation formulas, not equations assumed at zeros.
 if 'd'in eliminated:
  v=max(deg('wn2'),deg('ga')+deg('a4m5'))
  residual_degrees[indices.index(11)]=max(2*v,deg('a')+deg('c')+v,deg('a4m5')+2*deg('c'))
 if 'mu'in eliminated:
  v=max(deg('W'),deg('rho')+deg('a4m5'))
  residual_degrees[indices.index(17)]=max(2*v,deg('a')+deg('kappa')+v,deg('a4m5')+2*deg('kappa'))
 upper=2*max(residual_degrees)
 return {'eliminated':list(eliminated),'parameters':['x'],'fixed_numerals':CONSTANTS[:],'witnesses':witnesses,'domains':'ordinary input and all witnesses strictly positive integers; fixed numerals use the inherited admissible compiler slice',
  'source':rows,'comparisons':pairs,'retained_original_comparison_indices':indices,'polynomial_source':poly,'output':output,'certificate_ledger':cert,'polynomial_ledger':ledger,
  'residual_degree_bounds':residual_degrees,'polynomial_degree_upper_bound':upper,'exact_polynomial_degree':upper,
  'restoration_registers':{v:aliases.get(v,v)for v in eliminated},'first_root_restoration':{'old_coordinate':'tau','new_coordinate':'tau_gap','formula':'tau=first_root_base+tau_gap'},
  'comparison_map':[{'old_index':i,'new_index':indices.index(i)if i in indices else None,'deleted_definition':next((v for v in eliminated if DEFINITIONS[v][1]==i),None)}for i in range(19)],
  'theorem':'Complete positive-zero bijection with frozen raw30 parent; full integer graph identity of SOS; fixed ordinary-input program theorem unchanged.',
  'scope':'One of 256 subsets of the eight specified positive definitions after the first-root gap change; no global optimality claim.'}

def build(eliminated=DEFAULT,*,root=None):return _build(canonical_parent(root=root),selection(eliminated))
def rewrite(supplied,eliminated=DEFAULT,*,root=None):
 p=canonical_parent(root=root);need(exact(supplied,p),'only complete raw30 selected parent');return _build(p,selection(eliminated))

def checked(packet,*,root=None):
 need(type(packet)is dict and type(packet.get('eliminated'))is list,'exact packet/selection')
 need(all(type(v)is str for v in packet['eliminated']),'exact selected names')
 p=build(tuple(packet['eliminated']),root=root);need(exact(packet,p),'complete canonical packet');return p

def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']

def degree_certificate(packet,*,root=None):return _degree_audit(checked(packet,root=root))

def assignment(p,values,signed):
 need(type(signed)is bool and type(values)is dict,'exact assignment/mode')
 need(set(values)==set(p['polynomial_ledger']['free'])and all(type(k)is str and type(v)is int for k,v in values.items()),'exact full integer assignment')
 if not signed:need(all(v>0 for v in values.values()),'strict positive supplied domain')

def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);assignment(p,values,signed);return execute(p['polynomial_source'],values)[p['output']]

def restore_assignment(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);assignment(p,values,signed);d=execute(p['source'],values)
 old={k:v for k,v in values.items()if k!='tau_gap'};old.update({k:d[v]for k,v in p['restoration_registers'].items()});old['tau']=d['first_root_base']+values['tau_gap']
 if not signed:need(all(v>0 for v in old.values()),'unconditional positive restoration')
 return old

def project_assignment(packet,oldvalues,*,signed=False,root=None):
 p=checked(packet,root=root);old=canonical_parent(root=root);assignment(old,oldvalues,signed);d=execute(old['source'],oldvalues)
 need(all(d[old['comparisons'][DEFINITIONS[v][1]][0]]==d[old['comparisons'][DEFINITIONS[v][1]][1]]for v in p['eliminated']),'selected definition graph required')
 new={k:v for k,v in oldvalues.items()if k not in p['eliminated']and k!='tau'};new['tau_gap']=oldvalues['tau']-d['first_root_base'];assignment(p,new,signed)
 return new

class Intern:
 def __init__(self):self.data={}
 def atom(self,v):return self.node(('atom',type(v).__name__,v))
 def node(self,key):
  if key not in self.data:self.data[key]=len(self.data)
  return self.data[key]
 def op(self,op,a,b):return self.node((op,a,b))
 def run(self,rows,leaves,cuts=None):
  d=dict(leaves)
  for n,op,a,b in rows:
   d[n]=self.op(op,self.atom(a)if type(a)is int else d[a],self.atom(b)if type(b)is int else d[b])
   if cuts and n in cuts:d[n]=cuts[n]
  return d

def graph_proof(old,p):
 d=Intern();leaves={v:d.atom(v)for v in p['polynomial_ledger']['free']};qcut=d.atom('PROVED_REPUNIT_Q_MINUS_ONE');firstcut=d.atom('PROVED_FIRST_RESIDUAL')
 newcuts={'repunit':qcut}if 'q'in p['eliminated']else{}
 new=d.run(p['source'],leaves,newcuts)
 restored={v:leaves[v]for v in old['polynomial_ledger']['free']if v in leaves}
 restored.update({v:new[reg]for v,reg in p['restoration_registers'].items()});restored['tau']=d.op('+',new['first_root_base'],leaves['tau_gap'])
 oldcuts={'qm1':qcut,'repunit':qcut}if 'q'in p['eliminated']else{}
 oe=d.run(old['source'],restored,oldcuts)
 get=lambda env,v:d.atom(v)if type(v)is int else env[v]
 rows=0
 for i,(a,b)in enumerate(old['comparisons']):
  if i==5:
   need(oe['first_root_base']==new['first_root_base'],'same actual restored L')
   need(oe['k']==get(new,p['restoration_registers'].get('k','k')),'actual raw k or selected R10b')
   # L(L+k)-(L+g)^2+1 = 1-g^2-L(2g-k).
   # Actual defining rows are guarded in _build; this polynomial expansion
   # is independently exercised in verify through sparse bivariate algebra.
   rows+=1;continue
  if i not in p['retained_original_comparison_indices']:need(get(oe,a)==get(oe,b),'deleted graph residual exactly zero')
  else:
   j=p['retained_original_comparison_indices'].index(i);aa,bb=p['comparisons'][j]
   need(get(oe,a)==get(new,aa)and get(oe,b)==get(new,bb),'same full retained operands')
  rows+=1
 need(rows==19,'all old comparisons mapped')
 return {'old_comparisons':19,'deleted_zero_residuals':len(p['eliminated']),'retained_exact_residuals':len(p['comparisons']),'full_SOS_graph_identity':True}

# Sparse bivariate arithmetic in a uniform scaling t and Bm1=b.
def plus(a,b,sign=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items()if v}
def times(a,b):
 c={}
 for(i,j),v in a.items():
  for(k,l),w in b.items():c[i+k,j+l]=c.get((i+k,j+l),0)+v*w
 return{k:v for k,v in c.items()if v}
def polynomial_run(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a={(0,0):a}if type(a)is int else d[a];b={(0,0):b}if type(b)is int else d[b]
  d[n]=times(a,b)if op=='*'else plus(a,b,1 if op=='+'else-1)
 return d

def _degree_audit(p):
 # Internal audit consumes the generated canonical packet, not a caller API.
 # Every constant except Bm1 receives an independent dependency tag below;
 # candidate highest norm forms must exclude these tags.
 free=p['polynomial_ledger']['free'];d={v:(0,{v})if v in CONSTANTS else(1,set())for v in free}
 def get(v):return(0,set())if type(v)is int else d[v]
 def add(a,b):return a if a[0]>b[0]else b if b[0]>a[0]else(a[0],a[1]|b[1])
 def mul(a,b):return(a[0]+b[0],a[1]|b[1])
 for n,op,a,b in p['source']:d[n]=mul(get(a),get(b))if op=='*'else add(get(a),get(b))
 def norm(a,z,v,H):return add(add(mul(v,v),mul(mul(a,z),v)),mul(H,mul(z,z)))
 rd=[]
 alias=lambda v:p['restoration_registers'].get(v,v)
 for i,(a,b)in zip(p['retained_original_comparison_indices'],p['comparisons']):
  upper=add(get(a),get(b))
  if i==11 and 'd'in p['eliminated']:upper=norm(get(alias('a')),get(alias('c')),add(get('wn2'),mul(get('ga'),get('a4m5'))),get('a4m5'))
  if i==17 and 'mu'in p['eliminated']:upper=norm(get(alias('a')),get(alias('kappa')),add(get('W'),mul(get('rho'),get('a4m5'))),get('a4m5'))
  rd.append(upper)
 need([x[0]for x in rd]==p['residual_degree_bounds'],'degree cut accounting')
 maximum=max(x[0]for x in rd);candidates=[j for j,v in enumerate(rd)if v[0]==maximum]
 need(all(rd[j][1]<={'Bm1'}for j in candidates),'uniform top does not depend on remaining program numerals')
 values={v:{(1,0):3 if v=='tau_gap'else 1}for v in free if v not in CONSTANTS};values.update({v:{(0,0):i+2}for i,v in enumerate(CONSTANTS)});values['Bm1']={(0,1):1}
 env=polynomial_run(p['source'],values);leaders=[]
 for j in candidates:
  a,b=p['comparisons'][j];aa={(0,0):a}if type(a)is int else env[a];bb={(0,0):b}if type(b)is int else env[b]
  residual=plus(aa,bb,-1);top={power:v for(t,power),v in residual.items()if t==maximum}
  if top and(all(v>0 for v in top.values())or all(v<0 for v in top.values())):
   leaders.append({'residual_index':j,'old_comparison_index':p['retained_original_comparison_indices'][j],'degree':maximum,'uniform_Bm1_leading_coefficients':[[k,v]for k,v in sorted(top.items())]})
 need(bool(leaders),'nonzero sign-definite leading form for every Bm1>0')
 return {'exact_degree':2*maximum,'proof':'SOS upper bound plus a sign-definite nonzero t-leading residual polynomial in Bm1>0; all other fixed numerals absent from that degree','leaders':leaders,'top_fixed_dependencies':sorted(set().union(*(rd[j][1]for j in candidates)))}

def selections():return[tuple(v for v,b in zip(DEFINITIONS,bits)if b)for bits in itertools.product((False,True),repeat=8)]
def pareto(records):
 return[r for r in records if not any(s['operations']<=r['operations']and s['degree']<=r['degree']and(s['operations'],s['degree'])!=(r['operations'],r['degree'])for s in records)]

def local_expansions():
 def add(a,b,sign=1):
  c=dict(a)
  for k,v in b.items():c[k]=c.get(k,0)+sign*v
  return{k:v for k,v in c.items()if v}
 def mul(a,b):
  c={}
  for i,v in a.items():
   for j,w in b.items():
    k=tuple(x+y for x,y in zip(i,j));c[k]=c.get(k,0)+v*w
  return{k:v for k,v in c.items()if v}
 one={(0,0,0):1};L={(1,0,0):1};k={(0,1,0):1};g={(0,0,1):1}
 left=add(mul(L,add(L,k)),add(mul(add(L,g),add(L,g)),one,-1),-1)
 right=add(add(one,mul(g,g),-1),mul(L,add(add(g,g),k,-1)),-1)
 need(left==right,'exact first residual graph identity')
 aa={(1,0,0,0):1};z={(0,1,0,0):1};v={(0,0,1,0):1};H={(0,0,0,1):1};one4={(0,0,0,0):1}
 leftnorm=add(add(mul(add(mul(aa,z),v),add(mul(aa,z),v)),mul(add(mul(aa,aa),H),mul(z,z)),-1),one4,-1)
 rightnorm=add(add(add(mul(v,v),mul(mul(aa,z),v)),mul(mul(aa,z),v)),add(mul(H,mul(z,z)),one4),-1)
 need(leftnorm==rightnorm,'all-value normalized norm degree identity')
 return {'first_residual_coefficients':[[list(k),v]for k,v in sorted(left.items())],'norm_degree_cut_coefficients':[[list(k),v]for k,v in sorted(leftnorm.items())]}

def verify(root):
 root=authenticate(root);parent=canonical_parent(root=root);rng=random.Random(11328);forms=[];records=[]
 counts={'complete_forms':0,'graph_residual_identities':0,'full_numeric_graph_identities':0,'signed_cases':0,'rational_cases':0,'positive_restorations':0,'residual_values':0,'public_roundtrips':0,'public_evaluations':0,'guard_rejections':0,'copy_checks':0}
 representatives={(),DEFAULT,tuple(DEFINITIONS),('q','C','k','c','d','kappa','mu'),('q','C','k','a','c','d','mu')}
 for elim in selections():
  p=_build(parent,elim);proof=graph_proof(parent,p);degree=_degree_audit(p)
  n=len(elim);need(p['polynomial_ledger']['operations']==131-3*n and len(p['witnesses'])==30-n and len(p['comparisons'])==19-n,'finite-family complete formulas')
  counts['complete_forms']+=1;counts['graph_residual_identities']+=19
  for case in range(8):
   vals={v:rng.randint(-3,4)if case<4 else rng.randint(1,4)for v in p['witnesses']+['x']}
   vals.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case==3:vals={k:Fraction(v,3)if k not in CONSTANTS else v for k,v in vals.items()}
   d=execute(p['polynomial_source'],vals)
   full={k:v for k,v in vals.items()if k!='tau_gap'};full.update({v:d[reg]for v,reg in p['restoration_registers'].items()});full['tau']=d['first_root_base']+vals['tau_gap']
   old=execute(parent['polynomial_source'],full)
   need(old[parent['output']]==d[p['output']],'complete SOS graph identity')
   counts['full_numeric_graph_identities']+=1;counts['signed_cases']+=case<4;counts['rational_cases']+=case==3
   for i,(a,b)in enumerate(parent['comparisons']):
    val=old[a]-old[b]
    if i in p['retained_original_comparison_indices']:
     j=p['retained_original_comparison_indices'].index(i);l,r=p['comparisons'][j];need(val==d[l]-d[r],'every retained residual value')
    else:need(val==0,'deleted graph comparison vanishes')
    counts['residual_values']+=1
   if case>=4:need(all(v>0 for v in full.values()),'all restored positive before equations');counts['positive_restorations']+=1
   if elim in representatives and case in (0,4):
    signed=case==0
    need(exact(restore_assignment(p,vals,signed=signed,root=root),full),'public restoration')
    need(exact(project_assignment(p,full,signed=signed,root=root),vals),'public inverse graph map');counts['public_roundtrips']+=1
    need(evaluate(p,vals,signed=signed,root=root)==d[p['output']],'public evaluator');counts['public_evaluations']+=1
  rec={'eliminated':list(elim),'operations':p['polynomial_ledger']['operations'],'degree':degree['exact_degree'],'witnesses':len(p['witnesses']),'equations':len(p['comparisons'])};records.append(rec)
  forms.append({'packet':p,'graph_proof':proof,'degree_certificate':degree})
 family=pareto(records);need([(r['operations'],r['degree'])for r in family]==[(113,28),(110,68),(110,68),(107,84)],'enumerated family frontier')
 known=json.loads((root/'complete86_first_root_partitions.json').read_text())['census']['combined_frontier']
 oldpoints=[{'operations':r['operations'],'degree':r['exact_degree'],'witnesses':19,'origin':'frozen_first_root_grouping_union'}for r in known]
 newpoints=[dict(r,origin='selective_gap_graph_family')for r in family]
 combined=pareto(oldpoints+newpoints)
 need([r for r in combined if r['origin']=='selective_gap_graph_family']==[dict(family[0],origin='selective_gap_graph_family')],'only113/28 extends selected existing operation-degree frontier')
 for elim in representatives:
  p=_build(parent,elim);one={v:1 for v in p['polynomial_ledger']['free']}
  bads=[]
  for field in ('source','comparisons','witnesses','eliminated'):
   q=copy.deepcopy(p);q[field]=tuple(q[field]);bads.append(q)
  for field in ('source','polynomial_source'):
   for i,row in enumerate(p[field]):
    for j in (2,3):
     if type(row[j])is int:
      for val in (float(row[j]),bool(row[j])):
       q=copy.deepcopy(p);q[field][i][j]=val;bads.append(q)
  for value in (float(p['exact_polynomial_degree']),True):
   q=copy.deepcopy(p);q['exact_polynomial_degree']=value;bads.append(q)
  q=copy.deepcopy(p);q['source'].append(['no_op','+',1,0]);bads.append(q)
  q=copy.deepcopy(p);q['comparison_map'][0]['new_index']=False;bads.append(q)
  for q in bads:
   try:checked(q,root=root)
   except ValueError:counts['guard_rejections']+=1
   else:raise AssertionError('noncanonical packet accepted')
  for key,value in [('x',0),('tau_gap',0),('x',True),('x',1.0),('eta',-1)]:
   bad=dict(one);bad[key]=value
   try:evaluate(p,bad,root=root)
   except ValueError:counts['guard_rejections']+=1
   else:raise AssertionError('invalid domain accepted')
  try:evaluate(p,one,signed=1,root=root)
  except ValueError:counts['guard_rejections']+=1
  else:raise AssertionError('numeric signed flag accepted')
  # The inverse positivity condition is required away from zeros.
  full=restore_assignment(p,one,root=root);full['tau']=1
  try:project_assignment(p,full,root=root)
  except ValueError:counts['guard_rejections']+=1
  else:raise AssertionError('nonpositive inverse gap accepted')
  signed=project_assignment(p,full,signed=True,root=root);need(signed['tau_gap']<=0 and restore_assignment(p,signed,signed=True,root=root)==full,'signed off-zero inverse identity')
  if elim:
   bad=dict(full);bad[elim[0]]+=1
   try:project_assignment(p,bad,signed=True,root=root)
   except ValueError:counts['guard_rejections']+=1
   else:raise AssertionError('off-graph input accepted')
  for field in ('source','polynomial_source','comparison_map'):
   q=build(elim,root=root);q[field].clear();need(exact(build(elim,root=root),p),'fresh nested public packet');counts['copy_checks']+=1
  q=polynomial_source(p,root=root);q.clear();need(exact(build(elim,root=root),p),'fresh source copy');counts['copy_checks']+=1
 for sel in ([],('k','q'),('q','q'),('unknown',),(True,),('q',False)):
  try:build(sel,root=root)
  except ValueError:counts['guard_rejections']+=1
  else:raise AssertionError('invalid subset accepted')
 for mutation in ('source','mode','noop'):
  q=copy.deepcopy(parent)
  if mutation=='source':q['source'][0][2]=True
  elif mutation=='mode':q['mode']='positive22'
  else:q['source'].append(['noop','+',1,0])
  try:rewrite(q,root=root)
  except ValueError:counts['guard_rejections']+=1
  else:raise AssertionError('invalid selected parent accepted')
 q=canonical_parent(root=root);q['source'].clear();need(exact(canonical_parent(root=root),parent),'parent copy');counts['copy_checks']+=1
 with tempfile.TemporaryDirectory(prefix='gap113_pin_guard_')as tmp:
  target=Path(tmp)
  for name in PINS:(target/name).write_bytes((root/name).read_bytes())
  build(root=target);counts['warm_pin_rejections']=0
  for name in PINS:
   original=(target/name).read_bytes();(target/name).write_bytes(original+b'\n')
   try:build(root=target)
   except ValueError:counts['warm_pin_rejections']+=1
   else:raise AssertionError('modified source accepted')
   (target/name).write_bytes(original)
 # Small exact Pell fixtures are first-equation components, not full zeros.
 pell=[]
 for X in (1,2,8,32):
  for Y in (1,2,3):
   V=X*Y*Y;P=2*V+1;chi0,chi1=1,P;psi0,psi1=0,1
   for index in range(1,7):
    T=chi1;k=2*psi1;L=V*k;g=T-L
    need(T*T-L*(L+k)==1 and g>0 and g*g+L*(2*g-k)==1,'exact positive first-norm fixture')
    pell.append({'X':X,'Y':Y,'index':index,'root':T,'k':k,'gap':g})
    chi0,chi1=chi1,2*P*chi1-chi0;psi0,psi1=psi1,2*P*psi1-psi0
 counts['local_positive_first_norm_components']=len(pell)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True)
 need(proc.returncode!=0 and 'run without -O' in proc.stderr,'optimized-mode rejection');counts['optimized_mode_rejections']=1
 return {'status':'PASS_COMPLETE_GAP_SELECTIVE_PROJECTION113','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'counts':counts,'local_symbolic_identities':local_expansions(),'finite_family':{'subsets':256,'records':records,'frontier':family,'known_parent_frontier':oldpoints,'combined_operation_degree_frontier':combined,'scope':'Exactly eight named positive definitions; all256 complete literal schedules emitted. No minimum over other coordinate maps, finalizers or compilers.'},'forms':forms,'first_norm_components':pell,'scope':'Complete fixed-program ordinary-input universal theorem, positive witnesses, unbounded computation duration. New113-operation degree28 SOS has24 witnesses;74 comparison and86 polynomial operation minima remain separate achieved bounds.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 result=verify(a.root)
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'typed saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'counts':result['counts'],'frontier':result['finite_family']['frontier']},sort_keys=True))
if __name__=='__main__':main()
