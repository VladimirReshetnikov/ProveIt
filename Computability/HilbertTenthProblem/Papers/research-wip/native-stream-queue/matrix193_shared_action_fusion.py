#!/usr/bin/env python3
"""Paid fixed-matrix fusion in all four complete matrix193 coefficient graphs.
Only authenticated frozen JSON is read; no predecessor module is loaded.
"""
import argparse,hashlib,json,copy
from pathlib import Path
from collections import Counter,deque
PINS={
 'matrix193_joint_state_factor.py':'a146ffe90c441c288a71acef624e58ec5b35f8f210747fdcc76fcb7210df6df7',
 'matrix193_joint_state_factor.json':'dfcd4ae7ab908804b141a0fe4feb93be8b31c3cc776a3ad2fbe78136ce71e154',
 'matrix193_joint_state_factor.md':'d0032f9c9ba8975983c7fabf5399e6b1b590751598a61e53879d0a80f95fffce',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
REMOVED=['cp'+str(i) for i in list(range(484,492))+list(range(494,502))+[503,506]]
OLD={
 'cp484':('*',-489,'cp480'),'cp485':('*',-895,'cp483'),'cp486':('+','cp484','cp485'),
 'cp487':('*',271,'cp480'),'cp488':('*',496,'cp483'),'cp489':('+','cp487','cp488'),
 'cp490':('*','cp486','r138'),'cp491':('*','cp489','r138'),
 'cp494':('*',-489,'cp415'),'cp495':('*',-895,'cp493'),'cp496':('+','cp494','cp495'),
 'cp497':('*',271,'cp415'),'cp498':('*',496,'cp493'),'cp499':('+','cp497','cp498'),
 'cp500':('*','cp496','cp129'),'cp501':('*','cp499','cp129'),
 'cp503':('+','cp502','cp490'),'cp504':('+','cp503','cp500'),
 'cp506':('+','cp505','cp491'),'cp507':('+','cp506','cp501')}
NEW=[
 ('fusion_u0','*','r138','cp480'),('fusion_v0','*','cp129','cp415'),
 ('fusion_s0','+','fusion_u0','fusion_v0'),
 ('fusion_u1','*','r138','cp483'),('fusion_v1','*','cp129','cp493'),
 ('fusion_s1','+','fusion_u1','fusion_v1'),
 ('fusion_a0','*',-489,'fusion_s0'),('fusion_b0','*',-895,'fusion_s1'),
 ('fusion_out0','+','fusion_a0','fusion_b0'),
 ('fusion_a1','*',271,'fusion_s0'),('fusion_b1','*',496,'fusion_s1'),
 ('fusion_out1','+','fusion_a1','fusion_b1')]
def ck(v,msg):
 if not v:raise ValueError(msg)
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def sha(x):return hashlib.sha256(x).hexdigest()
def read(p):
 def obj(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(v):raise ValueError('noninteger JSON '+v)
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_float=bad,parse_constant=bad)
def table(rows):
 out={}
 for row in rows:
  ck(type(row)is list and len(row)==4,'row shape');n,o,a,b=row
  ck(type(n)is str and n not in out and o in ['+','-','*'],'SSA/op')
  ck(all(type(x)in [str,int] for x in [a,b]),'operand types');out[n]=tuple(row[1:])
 return out
def graph(rows,ports,fixed,output):
 d=table(rows);known=set(ports);deps={};users={n:[] for n in d};deg={n:0 if n in fixed else 1 for n in ports}
 for n,o,a,b in rows:
  ck(n not in known and all(type(x)is int or x in known for x in [a,b]),'sequential operands')
  deps[n]={x for x in [a,b] if x in d}
  for x in deps[n]:users[x].append(n)
  da,db=[0 if type(x)is int else deg[x] for x in [a,b]]
  deg[n]=da+db if o=='*' else max(da,db);known.add(n)
 queue=deque(n for n in d if not deps[n]);visited=0
 while queue:
  n=queue.popleft();visited+=1
  for u in users[n]:
   deps[u].remove(n)
   if not deps[u]:queue.append(u)
 ck(visited==len(d),'independent Kahn acyclicity')
 live=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in d:todo.extend(d[n][1:])
 ck(live==set(d)|set(ports),'every row/port live')
 c=Counter(row[1] for row in rows)
 return dict(total=len(d),M=c['*'],A=c['+']+c['-'],syntactic_degree=deg[output],live_ports=len(ports))
def trim(a):
 while a and a[-1]==0:a.pop()
 return tuple(a)
def poly(o,a,b):
 if o=='*':
  out=[0]*max(0,len(a)+len(b)-1)
  for i,c in enumerate(a):
   if c:
    for j,d in enumerate(b):
     if d:out[i+j]+=c*d
 else:
  out=[0]*max(len(a),len(b))
  for i,c in enumerate(a):out[i]+=c
  for i,c in enumerate(b):out[i]+=c if o=='+' else -c
 return trim(out)
def all_values(rows,Q,seeds,intern):
 env=dict(seeds);ps={};qbinding=None
 for n,o,a,b in rows:
  av=intern(('integer',a)) if type(a)is int else env[a]
  bv=intern(('integer',b)) if type(b)is int else env[b]
  if n==Q:
   qbinding=intern((o,av,bv));env[n]=qbinding;ps[n]=(0,1)
  elif (type(a)is int or a in ps) and (type(b)is int or b in ps):
   ck(qbinding is not None,'pure-Q cone starts after actual Q')
   pa=trim([a]) if type(a)is int else ps[a];pb=trim([b]) if type(b)is int else ps[b]
   ps[n]=poly(o,pa,pb);env[n]=intern(('Z[actualQ]',qbinding,ps[n]))
  else:env[n]=intern((o,av,bv))
 return env,ps

def finalizer(d,output,unit):
 rows={};res=[]
 def take(n):rows[n]=d[n];return d[n]
 o,p,one=take(output);ck(o=='-' and one==1,'full output offset')
 o,u,s=take(p);ck(o=='*' and u==unit,'native product binding')
 o,ss,one=take(s);ck(o=='+' and one==1,'SOS plus1')
 todo=[ss]
 while todo:
  n=todo.pop();o,a,b=take(n)
  if o=='+':todo.extend([b,a])
  else:
   ck(o=='*' and a==b,'SOS square');take(a);res.append(a)
 return rows,res

def ordered(d,ports,output):
 done=set(ports);visiting=set();rows=[]
 def visit(n):
  if type(n)is int or n in done:return
  ck(n in d and n not in visiting,'defined acyclic dependency '+str(n))
  visiting.add(n);o,a,b=d[n];visit(a);visit(b);visiting.remove(n)
  done.add(n);rows.append([n,o,a,b])
 visit(output);ck(set(d)<=done,'all definitions live')
 return rows

def local_identity():
 # Sparse polynomials in (u0,u1,v0,v1,p,q,z0,z1), independent of Q.
 dim=8
 def c(a):return {(0,)*dim:a} if a else {}
 def x(i):return {tuple(int(j==i) for j in range(dim)):1}
 def op(o,a,b):
  out=dict(a) if o!='*' else {}
  if o=='*':
   for u,av in a.items():
    for v,bv in b.items():
     k=tuple(i+j for i,j in zip(u,v));out[k]=out.get(k,0)+av*bv
  else:
   for k,bv in b.items():out[k]=out.get(k,0)+(bv if o=='+' else -bv)
  return {k:v for k,v in out.items() if v}
 seeds={n:x(i) for i,n in enumerate(['cp480','cp483','cp415','cp493','r138','cp129','cp502','cp505'])}
 def expand(defs):
  e=dict(seeds)
  for n,(o,a,b) in defs.items():e[n]=op(o,c(a) if type(a)is int else e[a],c(b) if type(b)is int else e[b])
  return e
 old=expand(OLD)
 new_defs={r[0]:tuple(r[1:]) for r in NEW}
 new_defs.update(cp504=('+','cp502','fusion_out0'),cp507=('+','cp505','fusion_out1'))
 new=expand(new_defs)
 ck(all(old[n]==new[n] for n in ['cp504','cp507']),'independent eight-port distributivity')
 return {n:[dict(exponents=list(k),coefficient=v) for k,v in sorted(old[n].items())] for n in ['cp504','cp507']}

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 pa=read(root/'matrix193_joint_state_factor.json');maps=read(root/'matrix193_entry_controller_charts.json')
 snap=enc(pa);ck(pa['source_sha256']==PINS['matrix193_joint_state_factor.py'],'parent helper binding')
 ck(len(pa['packets'])==4,'four parents')
 local=local_identity();packets=[];pool={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 for j,old in enumerate(pa['packets']):
  mp={} if j==0 else maps['packets'][j-1]['map'];m=lambda n:mp.get(n,n) if type(n)is str else n
  od=table(old['source']);nd=dict(od)
  ck(sha(enc(old['source']))==old['source_sha256'],'parent source binding')
  comp={r[0] for r in old['coefficient_component']}
  ck(len(comp)==540,'parent coefficient component540')
  for n,(o,a,b) in OLD.items():ck(od[m(n)]==(o,m(a),m(b)),'literal source guard '+n)
  removed={m(n) for n in REMOVED};edited={m('cp504'),m('cp507')}
  ck(removed|edited<=comp,'private edit belongs to coefficient component')
  users={n:sorted(r[0] for r in old['source'] if n in r[2:]) for n in removed}
  ck(all(set(v)<=removed|edited for v in users.values()),'every old private consumer')
  for n in removed:del nd[n]
  added={}
  for n,o,a,b in NEW:
   ck(n not in nd,'fresh name');added[n]=(o,m(a),m(b));nd[n]=added[n]
  nd[m('cp504')]=('+',m('cp502'),'fusion_out0');nd[m('cp507')]=('+',m('cp505'),'fusion_out1')
  rows=ordered(nd,old['free'],old['output']);new=copy.deepcopy(old)
  new['source']=rows;new['source_sha256']=sha(enc(rows))
  ck(set(nd)-set(od)==set(added) and set(od)-set(nd)==removed,'literal18 deletions12 additions')
  ck({n for n in set(nd)&set(od) if nd[n]!=od[n]}==edited,'only two retained definitions changed')
  new_comp=comp-removed|set(added);new['coefficient_component']=[r for r in rows if r[0] in new_comp]
  cc=Counter(r[1] for r in new['coefficient_component'])
  new['component_ledger']=dict(total=len(new_comp),M=cc['*'],A=cc['+']+cc['-'])
  ck(new['component_ledger']==dict(total=534,M=288,A=246),'534 coefficient rows')
  g0=graph(old['source'],old['free'],old['fixed_numerals'],old['output'])
  g1=graph(rows,new['free'],new['fixed_numerals'],new['output'])
  ck(g1['total']==g0['total']-6 and g1['M']==g0['M']-4 and g1['A']==g0['A']-2,'complete paid saving4M2A')
  ck(g1['total']==[1399,1396,1396,1393][j],'new full counts')
  Q=m('r108');seeds={n:intern(('port',n)) for n in old['free']}
  v0,p0=all_values(old['source'],Q,seeds,intern);v1,p1=all_values(rows,Q,seeds,intern)
  ck(v0[Q]==v1[Q],'actual computed Q binding')
  ck(p0[m('r138')]==p1[m('r138')]==(0,)*18+(1,),'paid Q18')
  ck(p0[m('cp129')]==p1[m('cp129')]==(0,)*60+(1,),'paid Q60')
  common=set(od)&set(nd);ck(all(v0[n]==v1[n] for n in common),'every retained register all-ring identity')
  word_checks=[]
  for cert in old['coefficient_certificates']:
   n=cert['wire'];want=trim(cert['ascending_coefficients'][:])
   ck(p0[n]==p1[n]==want,'full coefficient word '+n)
   word_checks.append(dict(wire=n,entries=len(cert['ascending_coefficients']),dense_sha256=sha(enc(list(want)))))
  f0,r0=finalizer(od,old['output'],m('eight_units'));f1,r1=finalizer(nd,new['output'],m('eight_units'))
  ck(f0==f1 and r0==r1==old['retained_residual_wires'],'complete finalizer/residual sequence literal')
  ck(len(f1)==[50,47,47,44][j],'actual finalizer size')
  ck(all(v0[n]==v1[n] for n in r0+[m('eight_units'),new['output']]),'native/residual/full output identities')
  ck(all(nd[n]==od[n] for n in set(od)-comp),'all non-coefficient rows literal')
  ck(len(old['shared_selector_component'])==242 and all(nd[r[0]]==tuple(r[1:]) for r in old['shared_selector_component']),'242 selectors literal')
  lits0={x for r in old['source'] for x in r[2:] if type(x)is int}
  lits1={x for r in rows for x in r[2:] if type(x)is int}
  ck(lits0==lits1 and len(lits1)==143,'same143 fixed literals')
  new['ledger'].update(total=g1['total'],M=g1['M'],A=g1['A'],syntactic_degree_upper=g1['syntactic_degree'])
  ck(new['ledger']['exact_degree']==[35587,53345,53347,71105][j],'same-polynomial degree transfer')
  ck(new['ledger']['positive_witnesses']==[141,140,140,139][j] and new['ledger']['supplied_ports']==len(new['free']),'supplied interface ledger')
  new['parent_reference']=dict(receipt='matrix193_joint_state_factor.json',packet_index=j,source_sha256=old['source_sha256'])
  new['proof']=dict(actual_Q=Q,private_consumer_map=users,removed=sorted(removed),added=sorted(added),
   edited=sorted(edited),all_retained_values_equal=len(common),coefficient_words=word_checks,
   finalizer_names=list(f1),finalizer_rows=len(f1),residuals=r1,
   full_output_identity='F_shared_action_fusion = F_joint_state_factor on identical supplied coordinates',
   degree_basis='exact same polynomial on same supplied coordinates; inherited pinned uniform degree',
   identity_method='actual-Q-bound dense Z[Q] normalization and shared structural interning of every retained register')
  packets.append(new)
 ck(enc(pa)==snap,'parent object immutable')
 return dict(status='PASS_MATRIX193_SHARED_ACTION_FUSION',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
  matrix_right_action=[[-489,271],[-895,496]],independent_cut_identity=local,
  old_definitions={n:list(v) for n,v in OLD.items()},new_definitions=[list(r) for r in NEW],packets=packets,
  scope=dict(full_sources=4,complete_all_ring_identity=True,all_common_registers_identical=True,
   positive_projection='identical supplied coordinates to immediate parent in each chart',
   fixed_program_recipe='unchanged',native_extension='inherited unchanged',
   degree='inherited exact uniform degree by identical full polynomial',
   diagnostic_sources=0,new_history_fixtures=0,predecessor_execution=False,
   local_or_global_minimality_claim=False,relation_to_complete84='separate matrix route; complete84 unchanged'))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();result=build(a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(enc(result)==enc(read(a.expect)),'typed exact receipt replay')
 print(result['status'],[p['ledger']['total'] for p in result['packets']])
if __name__=='__main__':main()
