#!/usr/bin/env python3
"""Fresh composition of three pinned matrix arithmetic packets, all read as data.
Sparse ring-audit utilities are source-copied from the authenticated hat packet;
no predecessor module is imported or executed.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
'matrix193_structured_coefficient_scout.py':'39ab5c942af5bd6d725d2c17e89d2222e3e44bf26cc59e3c1bad1d4e011e10a9',
'matrix193_structured_coefficient_scout.json':'ebdc03c29dc9469896aa858312c95400a77adf853116e6819c514fb4e587d032',
'matrix193_structured_coefficient_scout.md':'8e49bed183eed196768951d3a86febc6cbd8d0a2e8898387c41b3b0e0ebeced3',
'matrix193_hat_packing_scout.py':'0f1df101e2e7eb598c5252ecc676289ecc984ee2fee321f66471a225fabec8f6',
'matrix193_hat_packing_scout.json':'7ba450619fac0d057c33a5d4a64ff18f78a922b5bea8637db269d7b8584a221c',
'matrix193_hat_packing_scout.md':'e424a750e626fd0d174692e13ad82b284949da22d49db1419fa20ec20ca111fd',
'matrix193_bounded_high_output.py':'5ffccf1c76fcb27b1e68573a717c7fcb12f6e1d7afce47be2b2b30b54b2b6f63',
'matrix193_bounded_high_output.json':'9fee15c95d916813f425db0f306c9f0e50990540fe9284fc00c46cc380cb5039',
'matrix193_bounded_high_output.md':'7f5a5bab9bff8518881a16a7c9d32916ce4ca1ff9dcbaa18f7fab7d452da654c',
'matrix193_balanced_output_scout.json':'63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf',
'matrix193_balanced_output_scout.md':'cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_text(),object_pairs_hook=obj)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def trim(a):
 a=list(a)
 while a and a[-1]==0:a.pop()
 return tuple(a)
def polyop(op,a,b):
 if op=='*':
  if not a or not b:return ()
  z=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):z[i+j]+=x*y
 else:z=[(a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
 return trim(z)
def pure_values(rows,Q):
 val={Q:(0,1)}
 for n,op,l,r in rows:
  if n==Q:continue
  if all(type(v)is int or v in val for v in [l,r]):val[n]=polyop(op,trim([l]) if type(l)is int else val[l],trim([r]) if type(r)is int else val[r])
 return val

def high_edits(packet,free_parent):
 p=copy.deepcopy(packet);edits={};records=[];removed=set();added=set()
 for rec in p['extraction']:
  for j,prod in enumerate(rec['products']):
   pre=rec['side']+'_dot'+str(j)+'_';n=prod['high'];half=rec['half_low_scale'];edits[n]=[n,'-',pre+'high_hat',half]
   records.append({'wire':n,'new_hat':pre+'high_hat','paid_half_scale':half,'old_positive':pre+'high_positive','old_negative':pre+'high_negative'})
   removed.update([pre+'high_positive',pre+'high_negative']);added.add(pre+'high_hat')
 for i,row in enumerate(p['source']):
  if row[0] in edits:
   x=next(v for v in records if v['wire']==row[0]);ck(row==[row[0],'-',x['old_positive'],x['old_negative']],'old high row');p['source'][i]=edits[row[0]]
 ck(set(free_parent['free'])==(set(p['free'])-removed)|added,'new full port set')
 ck(set(free_parent['witnesses'])==(set(p['witnesses'])-removed)|added,'new witnesses')
 p['free']=free_parent['free'];p['witnesses']=free_parent['witnesses'];return p,records

def compile_component(hat,balanced,structured):
 insert=hat['stage_counts']['packing']+63;prefix=hat['source'][:insert];newq=hat['ports']['Q'];oldq=balanced['ports']['Q'];oval=pure_values(balanced['source'],oldq);nval=pure_values(prefix,newq)
 available={():0,(1,):1}
 for n,pol in nval.items():available.setdefault(pol,n)
 component=structured['coefficient_component'];cnames={r[0] for r in component};external=sorted({v for r in component for v in r[2:] if type(v)is str and v not in cnames})
 mapping={};bindings=[]
 for old in external:
  ck(old in oval and oval[old] in available,'existing paid coefficient dependency '+old);mapping[old]=available[oval[old]];bindings.append({'structured_parent_register':old,'hat_parent_register':mapping[old],'ascending_coefficients_in_Q':list(oval[old])})
 rows=[];merged=[]
 def value(x):return trim([x]) if type(x)is int else nval[x]
 for n,op,l,r in component:
  a=mapping.get(l,l);b=mapping.get(r,r);pol=polyop(op,value(a),value(b))
  if pol in available:mapping[n]=available[pol];merged.append({'component_register':n,'reused_register':mapping[n]})
  else:
   name='mix'+str(len(rows));rows.append([name,op,a,b]);mapping[n]=name;nval[name]=pol;available[pol]=name
 replacement={};certs=[]
 for hs,bs in zip(hat['extraction'],balanced['extraction']):
  for hp,bp in zip(hs['products'],bs['products']):
   new=mapping[structured['replacement'][bp['polynomial']]];want=trim(list(reversed(hp['coefficients'])));ck(nval[new]==want,'all four transplant coefficients');replacement[hp['polynomial']]=new;certs.append({'hat_output':hp['polynomial'],'new_output':new,'ascending_coefficients':list(want)})
 return insert,rows,replacement,{'external_equal_Q_bindings':bindings,'reused_component_rows':merged,'new_emitted_component_rows':len(rows),'coefficient_certificates':certs}

def compose(hat,bounded,balanced,structured=None):
 p,high=high_edits(hat,bounded);component=[];replace={};audit={}
 if structured is not None:
  insert,component,replace,audit=compile_component(hat,balanced,structured)
  p['source']=p['source'][:insert]+component+[[n,op,replace.get(l,l),replace.get(r,r)] for n,op,l,r in p['source'][insert:]]
  for rec in p['extraction']:
   for prod in rec['products']:prod['polynomial']=replace[prod['polynomial']]
 deps={n:(l,r) for n,op,l,r in p['source']};live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(deps.get(x,()))
 p['source']=[row for row in p['source'] if row[0] in live];known=set(p['free']);degree={x:0 if x in p['fixed_numerals'] else 1 for x in known}
 for n,op,l,r in p['source']:
  ck(n not in known and all(type(v)is int or v in known for v in [l,r]),'topology');known.add(n);degree[n]=degree.get(l,0)+degree.get(r,0) if op=='*' else max(degree.get(l,0),degree.get(r,0))
 ck(known==live,'all source and ports live');ct=Counter(r[1] for r in p['source']);p['stage_counts']['outer_producers']=len(p['source'])-p['stage_counts']['packing']-63-62
 p['ledger']={'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'residuals':20,'all_live':True,'proved_exact_degree':bounded['ledger']['proved_exact_degree'],'syntactic_degree_upper':degree[p['output']],'literal_count':len({v for row in p['source'] for v in row[2:] if type(v)is int})}
 p['composition']={'high_edits':high,'coefficient_splice':audit,'replacement':replace,'removed_hat_rows':[r[0] for r in hat['source'] if r[0] not in live],'live_component_rows':[r for r in component if r[0] in live]};return p

def exact_equivalence(old,new):
 # A fresh sparse interpreter at identical paid D,B,P,Q cuts. Coefficient
 # words are checked in full before their four outputs become shared atoms.
 def con(x):return {():x} if x else {}
 def atom(x):return {((x,1),):1}
 def plus(a,b,sign=1):
  z=dict(a)
  for k,v in b.items():
   z[k]=z.get(k,0)+sign*v
   if not z[k]:del z[k]
  return z
 def times(a,b):
  z={}
  for k,v in a.items():
   for h,w in b.items():
    t=dict(k)
    for name,e in h:t[name]=t.get(name,0)+e
    t=tuple(sorted(t.items()));z[t]=z.get(t,0)+v*w
  return {k:v for k,v in z.items() if v}
 def engine(p):
  rows={r[0]:r for r in p['source']};free=set(p['free']);memo={p['ports'][k]:atom(k) for k in ['D','B','P','Q']}
  def unfold(x):
   _,op,a,b=rows[x];aa=sym(a);bb=sym(b)
   return times(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
  def sym(x):
   if type(x)is int:return con(x)
   if x not in memo:memo[x]=atom(x) if x in free else unfold(x)
   return memo[x]
  return sym,unfold,memo
 ck(old['free']==new['free'] and old['witnesses']==new['witnesses'],'identical supplied coordinates')
 ck(old['groups']==new['groups'] and old['fixed_numerals']==new['fixed_numerals'],'identical fixed table and numerals')
 os,ou,om=engine(old);ns,nu,nm=engine(new)
 for key in ['D','B','P','Q']:ck(ou(old['ports'][key])==nu(new['ports'][key]),'paid boundary definition '+key)
 for key in ['J','Qhalf']:ck(os(old['ports'][key])==ns(new['ports'][key]),'shared paid value '+key)
 word_terms=[]
 for idx,(o,n) in enumerate(zip([x for e in old['extraction'] for x in e['products']],[x for e in new['extraction'] for x in e['products']])):
  ck(o['coefficients']==n['coefficients'],'identical signed coefficient list')
  a=os(o['polynomial']);b=ns(n['polynomial']);ck(a==b,'entire coefficient word')
  word_terms.append(len(a));om[o['polynomial']]=nm[n['polynomial']]=atom('coefficient_word_'+str(idx))
 cuts={}
 ck(old['native_cut_bindings'].keys()==new['native_cut_bindings'].keys(),'native boundary names')
 for key in old['native_cut_bindings']:
  a=os(old['native_cut_bindings'][key]);b=ns(new['native_cut_bindings'][key]);ck(a==b,'exact native packing '+key);cuts[key]=len(a)
 def native_rows(p):
  st=p['stage_counts']['packing'];back={v:k for k,v in p['native_cut_bindings'].items()}
  return [[name,op,back.get(a,a),back.get(b,b)] for name,op,a,b in p['source'][st:st+63]]
 ck(native_rows(old)==native_rows(new),'complete literal native block at proved equal cuts')
 residuals=[]
 ck(len(old['comparisons'])==len(new['comparisons'])==20,'comparison count')
 for i,((a,b),(c,d)) in enumerate(zip(old['comparisons'],new['comparisons'])):
  oa=plus(os(a),os(b),-1);na=plus(ns(c),ns(d),-1);ck(oa==na,'exact full residual '+str(i));residuals.append(len(oa))
 for p in [old,new]:
  tail=p['source'][-62:];squares=[]
  for i,(a,b) in enumerate(p['comparisons']):
   ck(tail[2*i][1:]==['-',a,b] and tail[2*i+1][1:]==['*',tail[2*i][0],tail[2*i][0]],'literal residual square');squares.append(tail[2*i+1][0])
  current=squares[0]
  for i in range(19):ck(tail[40+i][1:]==['+',current,squares[i+1]],'literal SOS join');current=tail[40+i][0]
  ck(tail[59][1:]==['+',current,1] and tail[60][1:]==['*','eight_units',tail[59][0]] and tail[61][1:]==['-',tail[60][0],1],'literal complete finalizer')
 return {'all_ring_identity':'F_composed=F_bounded_high on identical supplied coordinates','coefficient_word_terms':word_terms,'native_cut_terms':cuts,'all_twenty_residual_terms_at_proved_cuts':residuals,'native_rows':63,'literal_finalizer_rows':62,'positive_witness_map':'identity'}


def evaluate(p,v,mod):
 env=dict(v)
 for n,op,l,r in p['source']:
  a=env[l] if type(l)is str else l;b=env[r] if type(r)is str else r
  env[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
 return env

def modular_checks(parent,child):
 rng=random.Random(1681+child['n']);out=[]
 for mod in [1000000007,1000000009]:
  for case in range(8):
   v={x:rng.randrange(-50,51) for x in child['free']}
   if case%2==0:v.update(child['fixture_fixed_bindings'])
   a=evaluate(parent,v,mod);b=evaluate(child,v,mod)
   def value(env,x):return env[x] if type(x)is str else x
   for key in parent['native_cut_bindings']:ck(a[parent['native_cut_bindings'][key]]==b[child['native_cut_bindings'][key]],'mod native cut')
   for (l,r),(u,w) in zip(parent['comparisons'],child['comparisons']):ck((value(a,l)-value(a,r))%mod==(value(b,u)-value(b,w))%mod,'mod residual')
   ck(a[parent['output']]==b[child['output']],'mod full polynomial');out.append({'modulus':mod,'case':case,'fixed_binding_used':case%2==0,'output':b[child['output']]})
 return out

def degree_guard(p):
 # This authenticates the exact nonzero SWITCH coefficient used by the uniform
 # bounded-high tie proof. The full degree itself transfers by polynomial identity.
 ct=[];off=0
 for rec in p['extraction']:
  last=p['groups'][off+rec['length']//2-1];ck(1 not in last['edges'],'SWITCH absent from last block selector')
  for j,prod in enumerate(rec['products']):ct.append({'side':rec['side'],'column':j,'length':rec['length'],'last_selector_edges':last['edges'],'first_forward_coefficient':prod['coefficients'][0],'switch_leader_coefficient':'padding*radix_multiplier/2, implemented by the paid integer half-padding'})
  off+=rec['length']//2
 ck(p['n']>1 and p['padding']>0 and p['padding']%2==0 and p['groups'][-1]['kind']=='SWITCH' and p['groups'][-1]['edges']==[1],'positive even padding and SWITCH')
 return {'native_degree':34039 if p['n']==99 else 1351,'largest_extraction_residual_degree':4*max(r['length'] for r in p['extraction'])-2,'switch_nonzero_certificates':ct,'exact_full_degree':p['ledger']['proved_exact_degree']}

def build(root,artifacts):
 for n,h in PINS.items():
  path=(root if n.startswith('matrix193_balanced_output_scout.') else artifacts)/n
  ck(sha(path.read_bytes())==h,'pin '+n)
 def read(stem):
  r=parse(artifacts/(stem+'.json'));ck(r['source_sha256']==PINS[stem+'.py'],'source/receipt pin '+stem);return r
 hat=read('matrix193_hat_packing_scout');bounded=read('matrix193_bounded_high_output');structured=read('matrix193_structured_coefficient_scout');balanced=parse(root/'matrix193_balanced_output_scout.json')
 packets=[];proofs=[];mods=[];degrees=[]
 for i in range(2):
  old=balanced['packets'][i];high=bounded['packets'][i];hp=hat['packets'][i]
  rebuilt,relations=high_edits(old,high);ck(rebuilt['source']==high['source'],'entire frozen bounded-high literal chart')
  child=compose(hp,high,old,structured['packet'] if i==1 else None)
  proof=exact_equivalence(high,child);proof['bounded_high_literal_chart']=relations
  packets.append(child);proofs.append(proof);mods.append(modular_checks(high,child));degrees.append(degree_guard(child))
 ck([(p['ledger']['total'],p['ledger']['M'],p['ledger']['A'],p['ledger']['positive_witnesses']) for p in packets]==[(303,126,177,51),(1679,801,878,146)],'full ledgers')
 ck(len(packets[1]['composition']['live_component_rows'])==633 and len(packets[1]['composition']['removed_hat_rows'])==1344,'coefficient splice ledger')
 return {'schema':'matrix193-composed-output-v1','pins':PINS,'source_sha256':sha(Path(__file__).read_bytes()),'status':'complete uniform ordinary-input alternate matrix route; composition of three frozen packets','scope':{'predecessor_code_executed':False,'exact_identity_to_bounded_high_parent':True,'positive_zero_projection_to_balanced_parent':'retain every common non-high supplied port; high_hat=high_positive-high_negative+paid T_half','universal84_unchanged':True,'new_giant_native_or_outer_fixture_claim':False},'packets':packets,'all_ring_equivalence':proofs,'uniform_degree_guards':degrees,'modular_checks':mods,'inherited_actual_outer_evidence':bounded['actual_atomic_outer_fixture'],'inherited_outer_replayed':False}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root,a.artifacts or a.root)
 if a.write:a.write.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,parse(a.expect)),'exact typed receipt mismatch')
 print('PASS: complete1679=801M+878A/146w;diagnostic303/51w;all-ring cuts/native/residuals/finalizers;32 modular checks')
if __name__=='__main__':main()
