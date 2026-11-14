#!/usr/bin/env python3
"""New U208 release verifier. Supplied files are data, never imported/executed.
Python 3.10+. No third-party dependencies. --full runs the separately pinned,
self-authored symbolic engine; otherwise only finite checks are replayed.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parent
PIN={'parent':'4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1','native':'bdf724e5a4c5d25567a8b51d50db8ff8b6da3e42b0f03a73794f470171fdcbbe','dense':'5d487fb3ea29a84bedffec600af660ffeb8de3711838d67c41b01aec50c2a4ed','source':'912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3'}
def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));require((q,b)not in t,'duplicate row');require(b in(0,1)and w in(0,1)and d in('L','R'),'alphabet/direction');t[q,b]=(w,1 if d=='R'else-1,z)
 return t
def census(t,n,halt):
 s={q for q,b in t};require(len(s)==n and len(t)==2*n,'state/row count');require(set(t)=={(q,b)for q in s for b in(0,1)},'total rows');require({z for w,d,z in t.values()}-s=={halt},'halt convention');return s

def canon(t):
 ids={0:0};queue=[0];out=[]
 for q in queue:
  rows=[]
  for b in(0,1):
   if(q,b)not in t:rows.append(None);continue
   w,d,z=t[q,b]
   if z not in ids:ids[z]=len(ids);queue.append(z)
   rows.append([w,d,ids[z]])
  out.append(rows)
 return out,ids

def local(parent,child):
 census(parent,209,254);census(child,208,254)
 rho=lambda q:211 if q==172 else q
 require(set(child)==set(parent)-{(172,0),(172,1)},'removed label172')
 for(q,b),(w,d,z)in parent.items():
  if q==172:continue
  want=(0,-1,214)if(q,b)==(211,0)else(w,d,rho(z));require(child[q,b]==want,'literal recipe')
 inc=lambda q:sorted((s,b,w,d)for(s,b),(w,d,z)in parent.items()if z==q)
 require(inc(172)==[(116,0,0,1)] and inc(116) and all(w==1 and d==1 for s,b,w,d in inc(116)),'172 guard')
 x=parent[214,0][2]
 require(inc(211)==[(x,0,0,-1),(x,1,1,1)],'211 incoming')
 require(inc(x)==[(132,1,1,1),(199,1,1,1),(214,0,0,1)],'conditional-tag incoming')
 require(inc(214) and all(w==1 and d==1 for s,b,w,d in inc(214)),'helper incoming')
 cases=[]
 for q,b,env,n in [(172,0,{-2:1,-1:0,0:0},7),(172,1,{-2:1,-1:0,0:1},1),(211,0,{-1:1,0:0},3),(211,1,{0:1},1)]:
  w,d,z=parent[q,b];want=dict(env);want[0]=w;tape=dict(env);head=0;state=211;trace=[]
  for _ in range(n):
   require(head in tape,'unknown exterior read');bit=tape[head];ww,dd,zz=child[state,bit];trace.append([state,head,bit,ww,dd,zz]);tape[head]=ww;head+=dd;state=zz;require(state!=254,'internal halt')
  require((state,head,tape)==(rho(z),d,want),'complete-tape endpoint')
  cases.append({'old_state':q,'bit':b,'known_cells':env,'steps':n,'trace':trace,'endpoint':[state,head]})
 return {'ordinary_rows':414,'cases':cases,'bounds':[1,7],'status':'PASS'}

def cfg(s):
 addr={a:i for i,(a,o,v)in enumerate(s)};require(len(addr)==len(s),'unique source')
 def first(p):
  for k in range(65):
   t=(p+'0'*65)[:k]
   if t in addr:require(set(p[k:])<={'0'},'stray source suffix');return addr[t]
  raise ValueError('source target')
 def strip(p,b,n):
  if not n:return p
  for k in range(len(p)-1,-1,-1):
   if p[k]==b:
    n-=1
    if not n:return p[:k]
  return ''
 def inc(p):return format((int(p or'0',2)+1)%2**len(p),'0'+str(len(p))+'b')if p else''
 out=[]
 for p,o,a in s:
  require(set(p)<={'0','1'} and o in('CH','CI','CD','CB','CC'),'source grammar')
  edges=[]if o=='CH'else[first(inc(p))]if o=='CI'else[first(inc(strip(p,'0',1))),first(inc(p))]if o=='CD'else[first(inc(strip(p,'0',a)))]if o=='CB'else[first(strip(p,'1',a))]
  out.append([o,a,edges])
 return out

def startup(t):
 q=h=0;ones=set();trace=hashlib.sha256()
 for _ in range(48140):
  b=int(h in ones);trace.update(f'{q},{h},{b};'.encode());w,d,z=t[q,b];ones.add(h)if w else ones.discard(h);h+=d;q=z
 return q,h,sorted(ones),trace.hexdigest()

def frame(r,s):
 require(r[:2]==(84,-2),'startup state/head');ones=set(r[2]);pc=s[136][0];require(pc=='001100110101010','startup PC');require({v for v in ones if v<=54}=={-3,54}|{i-2 for i,b in enumerate(pc)if b=='1'},'PC/header');pos=55;physical=[]
 for _ in range(52):
  require(pos not in ones,'separator');j=pos+1
  while j in ones:j+=1
  require(j>=pos+2,'positive encoding');physical.append(j-pos-2);pos=j
 require(not any(v>=pos for v in ones),'right exterior');regs=[physical[j]for j in(6,2,0,4,3,7,8,5,1)];require(regs==[1,0,13,0,0,1,0,0,1]and physical[9:]==[1]*43,'register frame');require(len(ones)==120,'one count')
 g=cfg(s);r0=[1,0,4,0,0,1,0,0,1];i=106
 for _ in range(141):
  op,arg,e=g[i]
  if op=='CI':r0[arg]+=1;i=e[0]
  elif op=='CD':p=r0[arg]>0;r0[arg]-=p;i=e[p]
  elif op in('CB','CC'):i=e[0]
  else:raise ValueError('unexpected source halt')
 require(i==136 and r0==regs,'interior source bridge')
 return {'steps':48140,'trace_sha256':r[3],'native_state':84,'head':-2,'header':54,'one_cells':120,'pc':pc,'source_ordinal':136,'logical_registers':regs,'spares':43,'bridge_steps':141}

def compare():
 names=['plain','compatibility','folds','composed','joint'];ts={n:read(ROOT/'baselines'/n/'native.tm')for n in names};ss={n:json.loads((ROOT/'baselines'/n/'sites.json').read_text())for n in names};cg={n:canon(t)[0]for n,t in ts.items()}
 for n,t in ts.items():
  census(t,209,254);require(len(canon(t)[1])==210,'graph reachability');m={int(k):int(v)for k,v in json.loads((ROOT/'baselines'/n/'state_map.json').read_text())['native_to_dense'].items()};m[254]=209;require(m[0]==0 and len(set(m.values()))==210,'baseline bijection');require(read(ROOT/'baselines'/n/'dense.tm')=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in t.items()},'baseline dense')
  require(cfg(ss[n])==cfg(ss['compatibility']),'common source CFG')
 require(cg['plain']==cg['folds']==cg['composed']==cg['joint']and cg['plain']!=cg['compatibility'],'two graph classes');require(ts['folds']==ts['joint'],'byte-identical graph tables')
 wit=json.loads((ROOT/'evidence/comparison_isomorphisms.json').read_text())
 for key,n in [('U209_ConPA_Compatible_Folds_2026-10-29','folds'),('U209_ConPA_Composed_2026-10-29','composed'),('U209_ConPA_Joint_2026-10-29','joint')]:
  non={int(k):v for k,v in wit[key]['nonidentity_map'].items()};m={q:non.get(q,q)for q in canon(ts['plain'])[1]};require(m[0]==0 and m[254]==254 and len(set(m.values()))==210,'witness bijection');require({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in ts['plain'].items()}==ts[n],'isomorphism witness')
 return {'classes':[['plain','folds','composed','joint'],['compatibility']],'machine_packets':5,'supplemental_PDF_only_packets':1,'witnesses_checked':3,'rows_per_witness':418,'same_ordinal_CFG':True,'different_source_addresses':sum(a[0]!=b[0]for a,b in zip(ss['plain'],ss['compatibility']))}

def runtime(t,sites,expected_steps=1250564):
 require(__debug__ and not sys.flags.optimize,'full runtime requires enabled assertions')
 rt=ROOT/'code/runtime'
 for n,h in {'symbolic_runtime.py':'0912a45ac7fe147a4fc2816665af7d254788caf11d29a6420124da6959877a46','independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'}.items():require(sha(rt/n)==h,'owned runtime engine pin')
 sys.path.insert(0,str(rt));import symbolic_runtime as engine
 mapping={int(k):int(v)for k,v in json.loads((ROOT/'calibration/baseline/legacy_mapping.json').read_text()).items()};states={q for q,b in t};m={q:mapping.get(q,q+1000)for q in states|{254}};require(len(set(m.values()))==209,'legacy renaming');tt={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in t.items()};lemmas,blocks=engine.prove_blocks(tt);n=steps=0;rows=set()
 for site in sites:
  for positive in((False,True)if site[1]=='CD'else(False,)):
   result=engine.case(tt,lemmas,site,positive);n+=1;steps+=result['symbolic_steps'];rows.update(result['rows'])
 for block in blocks:
  for event in block['trace']:rows.add(tuple(event[1][:2]))
 require(n==5084 and rows==set(tt)and steps==expected_steps,'universal runtime coverage')
 return {'status':'PASS','contracts':n,'covered_rows':len(rows),'symbolic_steps':steps,'quantifiers':'arbitrary natural registers and gap; arbitrary nonempty finite spare list; complete tape'}

def secondary(full):
 v=ROOT/'machine/variant_plain';parent=read(ROOT/'baselines/plain/native.tm');child=read(v/'u208.native.tm');sites=json.loads((v/'u208.sites.json').read_text())
 require(sha(v/'u208.native.tm')=='8edb41dcfc693729868dd9ace2015a6da848e4152a282d4e21362dc33c551efd','secondary pin');require(sha(v/'u208.sites.json')=='cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164','secondary source pin');local_result=local(parent,child)
 m={int(k):int(n)for k,n in json.loads((v/'state_map.json').read_text())['native_to_dense'].items()};require(m==dict(zip(sorted({q for q,b in child}),range(208)))|{254:208},'secondary map');require(read(v/'u208.tm')=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in child.items()},'secondary dense');require(startup(child)==startup(parent),'secondary startup');frame(startup(child),sites);require(canon(child)[0]!=canon(read(ROOT/'machine/u208.native.tm'))[0],'two new208 classes')
 witnesses=json.loads((ROOT/'evidence/comparison_isomorphisms.json').read_text());checked=[]
 for key,name in [('U209_ConPA_Compatible_Folds_2026-10-29','folds'),('U209_ConPA_Composed_2026-10-29','composed'),('U209_ConPA_Joint_2026-10-29','joint')]:
  non={int(k):v for k,v in witnesses[key]['nonidentity_map'].items()};f=lambda q:non.get(q,q);old=read(ROOT/'baselines'/name/'native.tm');derived={(q,b):(w,d,211 if z==172 else z)for(q,b),(w,d,z)in old.items()if q!=172};derived[211,0]=(0,-1,f(214));require(derived=={(f(q),b):(w,d,f(z))for(q,b),(w,d,z)in child.items()},'new208 isomorphism');checked.append(name)
 return {'native_sha256':sha(v/'u208.native.tm'),'dense_sha256':sha(v/'u208.tm'),'source_sha256':sha(v/'u208.sites.json'),'local':local_result,'isomorphic_variants_checked':checked,'runtime':runtime(child,sites,1251865)if full else {'status':'not requested'}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--full',action='store_true');p.add_argument('--output',type=Path,default=Path('verification.json'));args=p.parse_args();started=time.time()
 pp=ROOT/'baselines/compatibility/native.tm';tp=ROOT/'machine/u208.native.tm';dp=ROOT/'machine/u208.tm';sp=ROOT/'machine/u208.sites.json'
 for key,path in [('parent',pp),('native',tp),('dense',dp),('source',sp)]:require(sha(path)==PIN[key],'identity '+key)
 dependency_script=ROOT/'calibration/dependencies/check_selection.py'
 require(dependency_script.is_file(),'dependency selection checker')
 import runpy
 runpy.run_path(str(dependency_script),run_name='__main__')
 if(ROOT/'MANIFEST.json').exists():
  for name,h in json.loads((ROOT/'MANIFEST.json').read_text())['files'].items():require(sha(ROOT/name)==h,'manifest '+name)
 parent=read(pp);child=read(tp);dense=read(dp);states=census(child,208,254);census(dense,208,208);m={int(k):int(v)for k,v in json.loads((ROOT/'machine/state_map.json').read_text())['native_to_dense'].items()};require(m==dict(zip(sorted(states),range(208)))|{254:208},'dense map');require(dense=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in child.items()},'dense exact');require(len(canon(child)[1])==209,'all literal states graph reachable')
 local_result=local(parent,child);comparison=compare();source=json.loads(sp.read_text());require(len(source)==3909 and source==json.loads((ROOT/'baselines/compatibility/sites.json').read_text()),'unchanged source');base=read(ROOT/'calibration/baseline/u212.native.tm');bc=cfg(json.loads((ROOT/'calibration/baseline/sites.json').read_text()));require(cfg(source)==bc,'calibrated source CFG');start=startup(child);require(start==startup(parent)==startup(base),'complete startup identity');frame_result=frame(start,source)
 negative=[]
 for name,mutate in [('wrong read-zero direction',lambda t:t.__setitem__((211,0),(0,1,214))),('wrong helper target',lambda t:t.__setitem__((211,0),(0,-1,217))),('unredirected target172',lambda t:t.__setitem__((116,0),(0,1,172))),('missing ordinary row',lambda t:t.pop((0,0))),('changed ordinary write',lambda t:t.__setitem__((0,0),(1-t[0,0][0],t[0,0][1],t[0,0][2])))]:
  bad=dict(child);mutate(bad)
  try:local(parent,bad)
  except (ValueError,KeyError):negative.append({'mutation':name,'rejected':True})
  else:raise ValueError('negative control accepted '+name)
 result={'status':'PASS','machine':PIN,'working_states':208,'rows':416,'local':local_result,'comparison':comparison,'startup':frame_result,'negative_controls':negative,'runtime':runtime(child,source)if args.full else {'status':'not requested','command':'python3 verify.py --full'},'secondary':secondary(args.full),'optimized_finite_checks':not __debug__,'seconds':time.time()-started,'proof_kind':'ordinary mathematical/PA-formalizable; not a proof-assistant kernel certificate'}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in('status','working_states','rows','runtime','optimized_finite_checks','seconds')},indent=2))
if __name__=='__main__':main()
