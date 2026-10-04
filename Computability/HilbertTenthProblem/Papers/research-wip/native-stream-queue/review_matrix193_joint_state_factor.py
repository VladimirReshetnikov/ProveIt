#!/usr/bin/env python3
"""Independent dense-Z[Q] and literal-source review; no author imports."""
import argparse,hashlib,json
from collections import Counter,deque
from pathlib import Path
AUTHOR={
 'matrix193_joint_state_factor.py':'a146ffe90c441c288a71acef624e58ec5b35f8f210747fdcc76fcb7210df6df7',
 'matrix193_joint_state_factor.json':'dfcd4ae7ab908804b141a0fe4feb93be8b31c3cc776a3ad2fbe78136ce71e154',
 'matrix193_joint_state_factor.md':'d0032f9c9ba8975983c7fabf5399e6b1b590751598a61e53879d0a80f95fffce'}
PARENTS={
 'matrix193_cleanup_tail_fusion.py':'52113307be60663b792a5ac62a7dc18ca35355d1a534faba4163c9b6d6047089',
 'matrix193_cleanup_tail_fusion.json':'61cbef79077bc3c5527c71f0abbeaac967f3d342f83bb8b9019ccdaa89857fe1',
 'matrix193_cleanup_tail_fusion.md':'0791bf4f25ae06e5ea4729de70da27d201524b57596756d991ad1af8253ebcc6',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
BLOCKS=[('r143',12,[('cp113','cp112'),('cp134','cp133'),('cp145','cp144'),('cp148','cp147')],['cp235','cp238']),
 ('r145',48,[('cp166','cp165'),('cp177','cp176'),('cp155','cp154'),('cp182','cp181')],['cp267','cp270']),
 ('cp383',66,[('cp384','cp381'),('cp387','cp386'),('cp390','cp389'),('cp393','cp392')],['cp474','cp477']),
 ('r143',12,[('cp396','cp395'),('cp399','cp398'),('cp402','cp401'),('cp405','cp404')],['cp446','cp449']),
 ('cp117',78,[('cp363','cp362'),('cp372','cp371'),('cp354','cp353'),('cp375','cp374')],['cp462','cp465'])]
EDITS={'cp121':('*','cp383','cp120'),'cp438':('*','cp434','r161'),'cp439':('*','cp437','r161'),
 'cp490':('*','cp486','r138'),'cp491':('*','cp489','r138')}
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

def independent_rewrite(old,m):
 d=table(old);out=dict(d);aliases={};adds={};restored=[]
 for power,e,pairs,targets in BLOCKS:
  power=m(power)
  for name,unscaled in pairs:
   name,unscaled=m(name),m(unscaled);o,a,b=d[name]
   ck(o=='*' and Counter([a,b])==Counter([power,unscaled]),'original four-product guard')
   aliases[name]=unscaled
  for name in targets:
   name=m(name);ck(d[name][0]=='+','original output addition')
   fresh='joint_factor_'+name;ck(fresh not in d and fresh not in adds,'fresh sum')
   adds[fresh]=d[name];out[name]=('*',fresh,power);restored.append(name)
 for name,(o,a,b) in EDITS.items():out[m(name)]=(o,m(a),m(b))
 out.update(adds)
 for name in aliases:del out[name]
 out={n:(o,aliases.get(a,a),aliases.get(b,b)) for n,(o,a,b) in out.items()}
 return out,aliases,adds,restored

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

def build(root,author_root):
 for base,pins in [(root,PARENTS),(author_root,AUTHOR)]:
  for n,h in pins.items():ck(sha((base/n).read_bytes())==h,'pin '+n)
 pa=read(root/'matrix193_cleanup_tail_fusion.json');ca=read(author_root/'matrix193_joint_state_factor.json')
 maps=read(root/'matrix193_entry_controller_charts.json');snap=enc(pa)
 ck(ca['source_sha256']==AUTHOR['matrix193_joint_state_factor.py'],'author self binding')
 ck(pa['source_sha256']==PARENTS['matrix193_cleanup_tail_fusion.py'],'parent self binding')
 pool={}
 def intern(t):
  if t not in pool:pool[t]=len(pool)
  return pool[t]
 results=[]
 for j,(old,new) in enumerate(zip(pa['packets'],ca['packets'])):
  mp={} if j==0 else maps['packets'][j-1]['map'];m=lambda n:mp.get(n,n) if type(n)is str else n
  for k in ['variant','free','fixed_numerals','witnesses','fixture_fixed_bindings','output','retained_residual_wires',
   'coefficient_certificates','selector_words','selector_ledger']:
   ck(enc(old[k])==enc(new[k]),'literal interface '+k)
  od,nd=table(old['source']),table(new['source'])
  expected,aliases,added,restored=independent_rewrite(old['source'],m)
  ck(expected==nd,'entire independent four-array rewrite')
  ck(set(od)-set(nd)==set(aliases) and set(nd)-set(od)==set(added),'exact names removed/added')
  ck(len(aliases)==20 and len(added)==10,'20 deletions10 restorations')
  g0=graph(old['source'],old['free'],old['fixed_numerals'],old['output'])
  g1=graph(new['source'],new['free'],new['fixed_numerals'],new['output'])
  ck(g1['total']==g0['total']-10 and g1['M']==g0['M']-10 and g1['A']==g0['A'],'whole paid ledger')
  ck(g1['total']==[1405,1402,1402,1399][j],'expected full count')
  ck(sha(enc(old['source']))==old['source_sha256'] and sha(enc(new['source']))==new['source_sha256'],'source hashes')
  component=set(r[0] for r in old['coefficient_component'])|set(added)
  ck(len(old['coefficient_component'])==550,'parent component550')
  for row in pa['packets'][0]['coefficient_component']:
   ck(od[m(row[0])]==(row[1],m(row[2]),m(row[3])),'full550 chart source map')
  actual_component=[r for r in new['source'] if r[0] in component]
  ck(actual_component==new['coefficient_component'] and len(actual_component)==540,'new actual component540')
  cc=Counter(r[1] for r in actual_component);ck(cc['*']==292 and cc['+']+cc['-']==248,'component292M248A')
  ck(all(nd[n]==r for n,r in od.items() if n not in component),'all external rows literal')
  ck(len(new['shared_selector_component'])==242 and all(tuple(r[1:])==od[r[0]]==nd[r[0]] for r in new['shared_selector_component']),'242 selectors literal')
  seeds={n:intern(('port',n)) for n in old['free']};Q=m('r108')
  v0,p0=all_values(old['source'],Q,seeds,intern);v1,p1=all_values(new['source'],Q,seeds,intern)
  ck(v0[Q]==v1[Q],'actual upstream Q binding, not independent cut')
  for n,e in [('r143',12),('r145',48),('cp383',66),('cp117',78),('r161',72),('r138',18)]:
   ck(p0[m(n)]==p1[m(n)]==(0,)*e+(1,),'paid Q power '+n)
  changed=[];same=0
  for n in sorted(set(od)&set(nd)):
   if v0[n]==v1[n]:same+=1;continue
   ck(n in component and n in p0 and n in p1 and p0[n] and p1[n],'only pure-Q computed intermediates differ')
   candidates=[e for e in [12,48,66,78] if p0[n]==(0,)*e+p1[n]]
   ck(len(candidates)==1,'exact shifted internal polynomial')
   changed.append([n,candidates[0],sha(enc(list(p0[n]))),sha(enc(list(p1[n])))])
  ck(len(changed)==124 and Counter(r[1] for r in changed)==Counter({12:56,48:34,66:20,78:14}),'all124 shifted values')
  ck(same==[1271,1268,1268,1265][j],'every other retained value identity')
  all_restored=restored+[m(x) for x in ['cp438','cp439','cp490','cp491']]
  ck(len(set(all_restored))==14 and all(v0[n]==v1[n] for n in all_restored),'14 exact terminal restorations')
  words=[]
  for cert in old['coefficient_certificates']:
   n=cert['wire'];want=trim(cert['ascending_coefficients'][:])
   ck(p0[n]==p1[n]==want,'entire coefficient vector')
   words.append(dict(name=n,entries=len(cert['ascending_coefficients']),dense_sha256=sha(enc(list(want)))))
  f0,r0=finalizer(od,old['output'],m('eight_units'));f1,r1=finalizer(nd,new['output'],m('eight_units'))
  ck(f0==f1 and r0==r1==old['retained_residual_wires'],'actual complete finalizer/residual sequence')
  ck(len(f1)==[50,47,47,44][j],'full finalizer ledger')
  ck(all(v0[n]==v1[n] for n in r0+[m('eight_units'),new['output']]),'every residual/native product/full output identity')
  ck(old['ledger']['exact_degree']==new['ledger']['exact_degree']==[35587,53345,53347,71105][j],'same-variable exact-degree transfer')
  lits0={x for r in old['source'] for x in r[2:] if type(x)is int};lits1={x for r in new['source'] for x in r[2:] if type(x)is int}
  ck(lits0==lits1 and len(lits1)==143,'fixed literal set unchanged')
  results.append(dict(variant=old['variant'],source_rows=g1['total'],graph=g1,coefficient_rows=540,
   removed=sorted(aliases),introduced=sorted(added),changed_internal_polynomials=changed,retained_values_equal=same,
   terminal_restorations=all_restored,coefficient_words=words,finalizer_rows=len(f1),residuals=r1,
   actual_Q=Q,whole_polynomial_identity=True,exact_degree=new['ledger']['exact_degree']))
 ck(len(results)==4 and len(ca['packets'])==4,'four full arrays')
 ck(enc(pa)==snap,'parent object immutable')
 return dict(status='PASS_INDEPENDENT_JOINT_STATE_FACTOR_REVIEW',source_sha256=sha(Path(__file__).read_bytes()),
  author_pins=AUTHOR,parent_pins=PARENTS,results=results,total_rows=sum(r['source_rows'] for r in results),
  total_coefficient_entries=sum(w['entries'] for r in results for w in r['coefficient_words']),
  scope=dict(author_execution=False,predecessor_execution=False,full_source_reconstruction=True,
   full_integer_polynomial_identity=True,positive_zero_map='identical supplied coordinates to immediate cleanup parent',
   degrees='inherited by exact whole-polynomial equality',new_native_fixtures=False))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();result=build(a.root,a.author_root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(enc(result)==enc(read(a.expect)),'typed exact review receipt')
 print(result['status'],result['total_rows'],'rows',result['total_coefficient_entries'],'coefficient entries')
if __name__=='__main__':main()
