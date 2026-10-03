#!/usr/bin/env python3
"""Exact factored-first-norm transfer of three complete75 comparison sources.
Reads authenticated source and receipt bytes only; no historical imports.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run this audit without -O')
PINS={
 'complete75_half_binomial.py':'5383b009a41abc19bb4c94e3f25c96ccfd4122d6a016c27b54fda0a75f7acab5',
 'complete75_half_binomial.json':'a46ffb29e0d0db2f6c531edb442f0b5adb0f29a8a3f13dcdd8be9c64b4d17ea0',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
 'complete75_positive_elimination.json':'03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703',
 'complete75_signed_projection_elimination101.py':'5a781fdacabab7feda2a8879c1cc207936045a1e4aa063c064a0bfffcdc9b4c8',
 'complete75_signed_projection_elimination101.json':'00de69d028b79d3837bbd892a202d78d95092711d68ca6f40bf7d5e2ab20c3e3'}
MODES=('raw30','positive22','signed20')
CONSTANTS=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
BLOCK=('UM2','scaled_norm_coefficient','ratio_product2','L9')

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def execute(rows,values):
 env=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  env[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return env

def inspect(rows,terminals):
 need(type(rows)is list and all(type(r)is list and len(r)==4 for r in rows),'exact source rows')
 names=[r[0] for r in rows];need(all(type(n)is str for n in names) and len(names)==len(set(names)),'unique exact names')
 free={v for _,_,a,b in rows for v in (a,b) if type(v)is str and v not in names};ready=set(free);deps={};counts=Counter()
 for n,op,a,b in rows:
  need(type(op)is str and op in ['+','-','*'] and n not in ready,'valid fresh gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in (a,b)),'exact typed closed operands')
  ready.add(n);deps[n]=(a,b);counts[op]+=1
 live=set()
 def visit(v):
  if type(v)is int or v in free or v in live:return
  need(v in deps,'missing terminal/dependency');live.add(v)
  for x in deps[v]:visit(x)
 for t in terminals:visit(t)
 need(live==set(names),'every paid gate live')
 return {'operations':len(rows),'M':counts['*'],'A':counts['+']+counts['-'],'free':sorted(free),'all_gates_live':True}

def finalizer(certificate,comparisons):
 rows=copy.deepcopy(certificate);squares=[]
 for i,(a,b) in enumerate(comparisons):
  r='residual_'+str(i);s='square_'+str(i);rows.extend([[r,'-',a,b],[s,'*',r,r]]);squares.append(s)
 out=squares[0]
 for i,s in enumerate(squares[1:],1):n='sum_'+str(i);rows.append([n,'+',out,s]);out=n
 return rows,out

def canonical_parent(root,mode='signed20'):
 need(type(mode)is str and mode in MODES,'exact selected mode');root=Path(root)
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'parent pin '+n)
 base=json.loads((root/'complete75_half_binomial.json').read_text())['source']
 pos=json.loads((root/'complete75_positive_elimination.json').read_text())
 signed=json.loads((root/'complete75_signed_projection_elimination101.json').read_text())['source']
 if mode=='raw30':
  rows=base['schedule'];comparisons=[r['equality'] for r in base['sources']];indices=list(range(19));witnesses=None;degree=52
 elif mode=='positive22':
  rows=pos['polynomial_schedule'][:75];comparisons=pos['retained_equalities'];indices=pos['retained_equality_indices'];witnesses=pos['retained_positive_witnesses'];degree=84
 else:
  rows=signed['polynomial_schedule'][:75];comparisons=signed['comparisons'];indices=signed['retained_original_comparison_indices'];witnesses=signed['positive_witnesses'];degree=84
 terminals=[x for pair in comparisons for x in pair];ledger=inspect(rows,terminals)
 need((ledger['operations'],ledger['M'],ledger['A'])==(75,41,34),'complete parent ledger')
 if witnesses is None:witnesses=sorted(set(ledger['free'])-set(CONSTANTS)-{'x'})
 need(set(ledger['free'])==set(witnesses+CONSTANTS+['x']),'full supplied interface')
 need((len(witnesses),len(comparisons))=={'raw30':(30,19),'positive22':(22,11),'signed20':(20,9)}[mode],'parent arity/equations')
 polynomial,output=finalizer(rows,comparisons)
 if mode!='raw30':need(exact(polynomial,pos['polynomial_schedule'] if mode=='positive22' else signed['polynomial_schedule']),'literal inherited SOS schedule')
 return {'mode':mode,'source':rows,'comparisons':comparisons,'original_comparison_indices':indices,'witnesses':witnesses,'fixed_numerals':CONSTANTS[:],'ordinary_input':'x','certificate_ledger':ledger,'polynomial_source':polynomial,'output':output,'polynomial_ledger':inspect(polynomial,[output]),'exact_polynomial_degree':degree}

def rewrite(root,mode='signed20',supplied=None):
 parent=canonical_parent(root,mode)
 if supplied is not None:need(exact(supplied,parent),'only entire canonical selected parent packet')
 rows=parent['source'];d={n:[op,a,b] for n,op,a,b in rows}
 need(exact(d['UM'],['*','wn2','sn2']),'E=XY is computed, not assumed')
 need(d['ksn2'][0]=='*' and d['ksn2'][2]=='sn2','literal kY register');k=d['ksn2'][1]
 need(k==('k' if mode=='raw30' else 'R10b'),'actual selected k port')
 want={'UM2':['*','UM','UM'],'scaled_norm_coefficient':['+','UM2','wn2'],'ratio_product2':['*','ksn2','ksn2'],'L9':['*','scaled_norm_coefficient','ratio_product2']}
 need(all(exact(d[n],v) for n,v in want.items()),'literal four-gate first coefficient')
 for private,consumer in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
  need({n for n,op,a,b in rows if private in (a,b)}=={consumer},'private old register consumers')
  need(all(private not in pair for pair in parent['comparisons']),'private old register is comparison output')
 need('first_root_base' not in d and 'first_next' not in d,'fresh intermediate names')
 new=[]
 for n,op,a,b in rows:
  if n=='L9':new.extend([['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base',k],['L9','*','first_root_base','first_next']])
  elif n not in BLOCK:new.append([n,op,a,b])
 out=copy.deepcopy(parent);out['source']=new;out['certificate_ledger']=inspect(new,[x for pair in out['comparisons'] for x in pair])
 out['polynomial_source'],out['output']=finalizer(new,out['comparisons']);out['polynomial_ledger']=inspect(out['polynomial_source'],[out['output']])
 out['transformation']={'parent_mode':mode,'parent_source_sha256':sha(json.dumps(rows,separators=(',',':')).encode()),'same_supplied_coordinates':True,'all_value_polynomial_identity':True,'coefficient_identity':'(E²+X)*(kY)² = L*(L+k), E=XY, L=E*(kY)','actual_k_port':k,'removed_private_registers':['UM2','scaled_norm_coefficient','ratio_product2'],'new_registers':['first_root_base','first_next'],'unchanged_comparison_indices':list(range(len(out['comparisons'])))}
 need((out['certificate_ledger']['operations'],out['certificate_ledger']['M'],out['certificate_ledger']['A'])==(74,40,34),'74 fully paid comparison operations')
 need(out['polynomial_ledger']['operations']=={'raw30':130,'positive22':106,'signed20':100}[mode],'full SOS paid total')
 return out

def checked(root,packet):
 need(type(packet)is dict and type(packet.get('mode'))is str,'exact packet/mode')
 expected=rewrite(root,packet['mode']);need(exact(packet,expected),'only complete canonical child packet');return expected

def evaluate(root,packet,values,signed=False):
 need(type(signed)is bool,'exact signed mode');p=checked(root,packet)
 need(type(values)is dict and set(values)==set(p['polynomial_ledger']['free']),'exact full input dictionary')
 need(all(type(n)is str and type(v)is int for n,v in values.items()),'exact integer input/coordinates')
 if not signed:need(all(v>0 for v in values.values()),'strictly positive supplied coordinates/fixed numeral ports')
 return execute(p['polynomial_source'],values)[p['output']]


def coefficient_identity(parent,child):
 # Full sparse expansion at independent X,Y,k, including actual E and kY.
 z=(0,0,0)
 def add(a,b,sign=1):
  c=a.copy()
  for n,v in b.items():c[n]=c.get(n,0)+sign*v
  return {n:v for n,v in c.items() if v}
 def mul(a,b):
  c={}
  for n,v in a.items():
   for m,w in b.items():
    q=tuple(x+y for x,y in zip(n,m));c[q]=c.get(q,0)+v*w
  return {n:v for n,v in c.items() if v}
 def run(rows,kname):
  e={'wn2':{(1,0,0):1},'sn2':{(0,1,0):1},kname:{(0,0,1):1}}
  for n,op,a,b in rows:
   if n in e:continue
   if (type(a)is int or a in e) and (type(b)is int or b in e):
    aa={z:a} if type(a)is int else e[a];bb={z:b} if type(b)is int else e[b]
    e[n]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
  return e['L9']
 kname=child['transformation']['actual_k_port'];a=run(parent['source'],kname);b=run(child['source'],kname)
 need(a==b=={(2,4,2):1,(1,2,2):1},'actual literal first coefficient identity')
 return [[list(n),v] for n,v in sorted(a.items())]

def whole_identity(parent,child):
 inter={}
 def intern(v):
  if v not in inter:inter[v]=len(inter)
  return inter[v]
 def run(rows):
  e={}
  for n,op,a,b in rows:
   if n=='L9':e[n]=intern(('proved_first_coefficient',));continue
   aa=intern(('int',a)) if type(a)is int else e.get(a,intern(('input',a)))
   bb=intern(('int',b)) if type(b)is int else e.get(b,intern(('input',b)))
   e[n]=intern((op,aa,bb))
  return e
 a=run(parent['polynomial_source']);b=run(child['polynomial_source']);checks=0
 need(exact(parent['comparisons'],child['comparisons']),'same literal comparison list')
 for i,(lhs,rhs) in enumerate(parent['comparisons']):
  for n in [lhs,rhs]:need(a.get(n,intern(('input',n)))==b.get(n,intern(('input',n))),'same actual comparison operand');checks+=1
  need(a['residual_'+str(i)]==b['residual_'+str(i)],'same residual');checks+=1
 need(a[parent['output']]==b[child['output']],'whole literal SOS identity')
 return checks+1

def dense(rows,values):
 def add(a,b,sgn=1):
  c=[(a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e=dict(values)
 for n,op,a,b in rows:
  a=[a] if type(a)is int else e[a];b=[b] if type(b)is int else e[b]
  e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return e

def verify(root):
 forms=[];rng=random.Random(74100);counts=Counter()
 for mode in MODES:
  p=canonical_parent(root,mode);c=rewrite(root,mode,copy.deepcopy(p));identity=coefficient_identity(p,c);counts['exact_comparison_residual_output_DAG_identities']+=whole_identity(p,c)
  for case in range(96):
   values={n:(rng.randrange(-4,5) if case%2 else rng.randrange(1,5)) for n in p['witnesses']+['x']}
   if case>=80:values={n:Fraction(v,3) for n,v in values.items()};counts['rational_complete_cases']+=1
   B=[16,32,64,128][case%4];values.update(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
   a=execute(p['polynomial_source'],values);b=execute(c['polynomial_source'],values)
   need(a[p['output']]==b[c['output']],'whole polynomial equality')
   for i,(lhs,rhs) in enumerate(p['comparisons']):need(a[lhs]-a[rhs]==b[lhs]-b[rhs],'every residual equality');counts['numeric_residual_identities']+=1
   for n in (set(a)&set(b)):need(a[n]==b[n],'every shared source register');counts['shared_register_identities']+=1
   counts['complete_numeric_cases']+=1;counts['signed_complete_cases']+=case%2
   if case<80:need(evaluate(root,c,values,signed=bool(case%2))==b[c['output']],'public canonical evaluation');counts['public_evaluations']+=1
  degree_checks=[]
  for B in [16,32]:
   slopes={n:(i%3)+1 for i,n in enumerate(c['witnesses']+['x'])};params=dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
   env={n:[0,v] for n,v in slopes.items()};env.update({n:[v] for n,v in params.items()});v=dense(c['polynomial_source'],env);degree=len(v[c['output']])-1
   want=(slopes['w']**4*slopes['s']**8*slopes['k']**4*slopes['q']**36 if mode=='raw30' else 16*(B-1)**60*slopes['delta']**4*slopes['w']**10*slopes['s']**10*slopes['Jrep']**60)
   need(degree==c['exact_polynomial_degree'] and v[c['output']][-1]==want,'full exact degree/leading source coefficient')
   degree_checks.append({'B':B,'degree':degree,'leading_coefficient_sha256':sha(str(want).encode()),'full_coefficients_sha256':sha(json.dumps(v[c['output']]).encode())})
  bads=[]
  for packet in [p,c]:
   family=[]
   for field in ['source','comparisons','witnesses']:
    bad=copy.deepcopy(packet);bad[field]=tuple(bad[field]);family.append(bad)
   for i,row in enumerate(packet['source']):
    bad=copy.deepcopy(packet);bad['source'][i][1]='+' if row[1]!='+' else '-';family.append(bad)
    for j in [2,3]:
     if type(row[j])is int:
      for x in [float(row[j]),bool(row[j])]:bad=copy.deepcopy(packet);bad['source'][i][j]=x;family.append(bad)
   bad=copy.deepcopy(packet);bad['certificate_ledger']['operations']=float(bad['certificate_ledger']['operations']);family.append(bad)
   bad=copy.deepcopy(packet);bad['source'].append(['unused_noop','+',1,0]);family.append(bad)
   for bad in family:
    try:rewrite(root,mode,bad) if packet is p else checked(root,bad)
    except ValueError:counts['malformed_parent_child_rejections']+=1
    else:raise ValueError('noncanonical packet accepted')
  # Defensive copies, including nested metadata and lists.
  a=canonical_parent(root,mode);a['source'][0][0]='poison';need(exact(canonical_parent(root,mode),p),'parent returned copy')
  a=rewrite(root,mode);a['source'][0][0]='poison';a['witnesses'].append('poison');need(exact(rewrite(root,mode),c),'child returned copy');counts['defensive_copy_checks']+=2
  vals={n:1 for n in c['polynomial_ledger']['free']}
  for x in [True,1.0,0,-1]:
   bad=dict(vals);bad['x']=x
   try:evaluate(root,c,bad)
   except ValueError:counts['malformed_coordinate_rejections']+=1
   else:raise ValueError('bad positive domain accepted')
  forms.append({'mode':mode,'parent_certificate':p['certificate_ledger'],'parent_polynomial':p['polynomial_ledger'],'packet':c,'first_coefficient_expansion':identity,'degree_checks':degree_checks})
 return {'status':'PASS_COMPLETE74_COMPARISON_TRANSFER','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'forms':forms,'counts':dict(counts),'scope':'Each complete source has exactly the same comparisons and same full SOS polynomial as its own authenticated parent on all integer/rational tuples. Domain/program/input/unbounded-duration obligations and all supplied witnesses are unchanged. Comparison cost74; polynomial costs130/106/100 do not improve the separate86 universal polynomial bound.'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'typed saved receipt mismatch')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledgers':[(x['mode'],x['packet']['certificate_ledger']['operations'],x['packet']['polynomial_ledger']['operations']) for x in r['forms']]},sort_keys=True))
if __name__=='__main__':main()
