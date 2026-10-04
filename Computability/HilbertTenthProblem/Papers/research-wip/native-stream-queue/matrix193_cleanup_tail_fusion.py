"""Fresh full cleanup/state Horner fusion; all frozen sources are inert data."""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'matrix193_selector_scaled_composition.py':'b220ba4a91370af19be84ab215dab3cf844dca16d026c08d7c0a8e85c62f6639',
 'matrix193_selector_scaled_composition.json':'762692a86d5020ffe89357d875803e927750546dbd946e309a2b48b6df73ce29',
 'matrix193_selector_scaled_composition.md':'96e6bc689c02ba789de5bed95b091a7560aba3a6a43a1428c6e0f3038bd61b5a',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
}
PLANS=[('cp302','cp272','cp297','cp283'),('cp304','cp274','cp300','cp284')]
CUBICS=[[7428465,45977311,-1503457720,-9305414129],[-63328274,-391960351,838975671,5192707423]]
REMOVED=['cp'+str(i)for i in range(285,302)]+['cp303']
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def load(p):
 def pairs(ps):
  d={}
  for k,v in ps:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(v):raise ValueError('noninteger JSON '+v)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  need(type(r)is list and len(r)==4,'binary row');n,o,a,b=r
  need(type(n)is str and n not in d and o in ('+','-','*'),'unique producer')
  need(all(type(v)in(int,str)for v in(a,b)),'operand type');d[n]=r
 return d
def plus(a,b,s=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+s*v
 return {k:v for k,v in d.items()if v}
def times(a,b):
 d={}
 for k,v in a.items():
  for j,c in b.items():
   z=tuple(x+y for x,y in zip(k,j));d[z]=d.get(z,0)+v*c
 return {k:v for k,v in d.items()if v}
def local(rows,root,cuts):
 d=table(rows);z=(0,)*len(cuts);memo={n:{tuple(int(i==j)for i in range(len(cuts))):1}for j,n in enumerate(cuts)}
 def run(v):
  if type(v)is int:return {z:v}if v else{}
  if v in memo:return memo[v]
  need(v in d,'closed polynomial cone');_,o,a,b=d[v];a,b=run(a),run(b)
  memo[v]=times(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1);return memo[v]
 return run(root)
def pure(rows,Q):
 p={Q:{(1,):1}}
 for n,o,a,b in rows:
  if n==Q or any(type(v)is str and v not in p for v in(a,b)):continue
  a={(0,):a}if type(a)is int else p[a];b={(0,):b}if type(b)is int else p[b]
  p[n]=times(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1)
 return p
def schedule(rows,output):
 d=table(rows);done=set();active=set();out=[]
 def run(n):
  if type(n)is int or n not in d or n in done:return
  need(n not in active,'acyclic simultaneous graph');active.add(n)
  for v in d[n][2:]:run(v)
  active.remove(n);done.add(n);out.append(d[n])
 run(output);return out

def audit(p):
 known=set(p['free']);need(len(known)==len(p['free']),'unique ports')
 need(known=={'x'}|set(p['witnesses'])|set(p['fixed_numerals']),'unchanged port grammar')
 deg={n:0 if n in p['fixed_numerals']else 1 for n in known};counts=Counter()
 for n,o,a,b in p['source']:
  need(n not in known and all(type(v)is int or v in known for v in(a,b)),'SSA/topology')
  x,y=(0 if type(v)is int else deg[v]for v in(a,b));deg[n]=x+y if o=='*'else max(x,y)
  counts[o]+=1;known.add(n)
 d=table(p['source']);seen=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in d:todo.extend(d[n][2:])
 need(seen==known,'complete liveness')
 return dict(total=len(d),M=counts['*'],A=counts['+']+counts['-'],positive_witnesses=len(p['witnesses']),supplied_ports=len(p['free']),fixed_coefficient_ports=len(p['fixed_numerals']),integer_literals=len({v for r in d.values()for v in r[2:]if type(v)is int}),syntactic_degree_upper=deg[p['output']],all_live=True)

def mapping(base,p):
 bd=table(base['coefficient_component']);d=table(p['source']);m={}
 def run(a,b):
  if type(a)is int:need(a==b,'mapped literal');return
  if a in m:need(m[a]==b,'consistent mapped register');return
  m[a]=b
  if a in bd:
   r,s=bd[a],d[b];need(r[1]==s[1],'mapped coefficient operation');run(r[2],s[2]);run(r[3],s[3])
 for a,b in zip(base['coefficient_certificates'],p['coefficient_certificates']):run(a['wire'],b['wire'])
 need(set(bd)<=set(m),'all552 component rows mapped')
 return m

def finalizer(p,N):
 d=table(p['source']);a=d[p['output']];need(a[1]=='-'and a[3]==1,'outer minus one')
 b=d[a[2]];need(b[1:3]==['*',N],'native-times-SOS');c=d[b[3]];need(c[1]=='+'and c[3]==1,'positive SOS')
 ids={a[0],b[0],c[0]};leaves=[]
 def run(n):
  r=d[n];ids.add(n)
  if r[1]=='*':need(r[2]==r[3],'square');ids.add(r[2]);leaves.append(r[2]);return
  need(r[1]=='+','sum');run(r[2]);run(r[3])
 run(c[2]);need(leaves==p['retained_residual_wires']and len(set(leaves))==len(leaves),'exact outer comparisons')
 need(len(ids)==3*len(leaves)+2,'complete finalizer size')
 need(all(not any(v in ids for v in r[2:])for r in p['source']if r[0]not in ids),'private finalizer')
 return {n:d[n]for n in ids}

def whole(old,new,Q,plans):
 pool={}
 def token(v):
  if v not in pool:pool[v]=len(pool)
  return pool[v]
 seed={n:token(('input',n))for n in old['free']};targets={t:(s,c,i)for i,(t,s,_,c)in enumerate(plans)};env=[]
 for p in(old,new):
  e=seed.copy()
  for n,o,a,b in p['source']:
   if n in targets:
    s,c,i=targets[n];e[n]=token(('proved cleanup polynomial',i,e[Q],e[s],e[c]))
   else:e[n]=token((o,token(('literal',a))if type(a)is int else e[a],token(('literal',b))if type(b)is int else e[b]))
  env.append(e)
 need(env[0][Q]==env[1][Q],'actual computed Q unchanged')
 common=set(env[0])&set(env[1]);need(all(env[0][n]==env[1][n]for n in common),'all retained expressions/full output')
 return len(common)-len(seed)

def numeric(rows,inputs,prime):
 e=inputs.copy()
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=(a*b if o=='*'else a+b if o=='+'else a-b)%prime
 return e

def transform(old,base,chartmap,index,native,groups):
 before=enc(old);d={n:r[:]for n,r in table(old['source']).items()};m=mapping(base,old);Q=m['r108']
 for n,w in m.items():need(w==chartmap.get(n,n),'component map agrees with authenticated chart map')
 pp=pure(old['source'],Q);need(pp[m['r135']]=={(4,):1},'actual paid Q4')
 fresh=[];plans=[];proof=[]
 for i,(target,body,tail,copy)in enumerate(PLANS):
  target,body,tail,copy=[m[n]for n in(target,body,tail,copy)];plans.append((target,body,tail,copy))
  co=CUBICS[i];need(pp[tail]=={(j,):v for j,v in enumerate(co)},'actual cleanup cubic')
  v=body
  for j in range(3,-1,-1):
   a='cleanup_tail_'+str(i)+'_mul_'+str(j);b='cleanup_tail_'+str(i)+'_add_'+str(j)
   need(a not in d and b not in d,'fresh names');r=[a,'*',v,Q];s=[b,'+',a,co[j]]
   fresh.extend([r,s]);d[a]=r;d[b]=s;v=b
  d[target]=[target,'+',v,copy]
 rows=schedule(list(d.values()),old['output']);by=table(rows);removed={m[n]for n in REMOVED};targets={a[0]for a in plans};added={r[0]for r in fresh}
 oldby=table(old['source']);need(set(oldby)-set(by)==removed and set(by)-set(oldby)==added,'exact18 private removals and16 additions')
 for n,r in by.items():
  if n not in added|targets:need(r==oldby[n],'all other definitions literal')
 for n in removed:need(all(r[0]in removed|targets for r in old['source']if n in r[2:]),'private removed cone')
 for i,(t,s,tail,c)in enumerate(plans):
  cuts=[Q,s,c];a=local(old['source'],t,cuts);b=local(rows,t,cuts)
  expected={(4,1,0):1,(0,0,1):1};expected.update({(j,0,0):v for j,v in enumerate(CUBICS[i])})
  need(a==b==expected,'complete local all-value identity at actual Q/state/copy cuts')
  proof.append(dict(target=t,state=s,copy=c,Q=Q,old_definition=oldby[t],new_definition=by[t],cleanup_coefficients=CUBICS[i],local_polynomial=[[list(k),v]for k,v in sorted(a.items())]))
 new={k:old[k]for k in ['variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output','retained_residual_wires']};new['source']=rows
 after=pure(rows,Q)
 need(all(pp[n]==v for n,v in after.items()if n in pp),'all retained pureQ values')
 for cert in old['coefficient_certificates']:need(after[cert['wire']]=={(j,):v for j,v in enumerate(cert['ascending_coefficients'])if v},'full coefficient word')
 new['coefficient_certificates']=old['coefficient_certificates'];ids={r[0]for r in old['coefficient_component']};component=[r for r in rows if r[0]in ids|added]
 cc=Counter(r[1]for r in component);need((len(component),cc['*'],cc['+']+cc['-'])==(550,302,248),'full550 coefficient cone')
 new['coefficient_component']=component;new['component_ledger']=dict(total=550,M=302,A=248)
 selector=old['shared_selector_component'];need(len(selector)==242 and all(by[r[0]]==r for r in selector),'all242 selector rows literal')
 new['shared_selector_component']=[r for r in rows if r[0]in {x[0]for x in selector}];new['selector_words']=old['selector_words'];new['selector_ledger']=old['selector_ledger']
 w=lambda n:chartmap.get(n,n)
 for n in native+groups:need(by[w(n)]==oldby[w(n)],'protected native/group row')
 of,nf=finalizer(old,w('eight_units')),finalizer(new,w('eight_units'));need(of==nf,'full interleaved finalizer literal')
 checked=whole(old,new,Q,plans);ledger=audit(new);prior=audit(old)
 need((ledger['total'],ledger['M'],ledger['A'])==(prior['total']-2,prior['M']-2,prior['A']),'actual complete saving')
 ledger['exact_degree']=old['ledger']['exact_degree'];ledger['outer_residuals']=len(new['retained_residual_wires']);new['ledger']=ledger
 rng=random.Random(141500+index);common=set(oldby)&set(by)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   values={n:rng.randrange(-17,18)for n in old['free']}
   if case%2==0:values.update(old['fixture_fixed_bindings'])
   a,b=numeric(old['source'],values,prime),numeric(rows,values,prime)
   need(all(a[n]==b[n]for n in common),'signed full retained values')
 need(enc(old)==before,'immediate parent packet immutable')
 new['source_sha256']=sha(enc(rows));new['identity']=dict(actual_Q=Q,local_identities=proof,deleted=[oldby[n]for n in oldby if n in removed],introduced=fresh,retained_registers_identical=checked,whole_polynomial_identity=True)
 new['boundaries']=dict(native_literal=63,group_population_literal=97,selector_literal=242,finalizer_literal=len(nf),ordinary_residuals_literal=len(new['retained_residual_wires']))
 new['parent_reference']=dict(receipt='matrix193_selector_scaled_composition.json',packet_index=index,source_sha256=sha(enc(old['source'])),degree_transfer='exact full polynomial identity on identical supplied coordinates and fixed coefficient ports')
 return new

def build(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'frozen pin '+n)
 parent=load(root/'matrix193_selector_scaled_composition.json');need(parent['source_sha256']==PINS['matrix193_selector_scaled_composition.py'],'parent helper binding')
 maps=load(root/'matrix193_entry_controller_charts.json');need(len(parent['packets'])==4 and len(maps['packets'])==3,'four actual variants')
 old=parent['packets'];base=old[0];names=[r[0]for r in base['source']]
 native=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 groups=['r'+str(i)for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 need(len(native)==63 and len(groups)==97,'protected inventories')
 out=[transform(p,base,{}if i==0 else maps['packets'][i-1]['map'],i,native,groups)for i,p in enumerate(old)]
 need([p['ledger']['total']for p in out]==[1415,1412,1412,1409],'four source counts')
 need([p['ledger']['exact_degree']for p in out]==[35587,53345,53347,71105],'exact inherited degrees')
 need([p['ledger']['positive_witnesses']for p in out]==[141,140,140,139],'witness counts')
 return dict(schema='matrix193-cleanup-tail-fusion-v1',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,packets=out,
  evidence=dict(complete_arrays=4,complete_rows=sum(len(p['source'])for p in out),coefficient_words=16,coefficient_entries=sum(len(c['ascending_coefficients'])for p in out for c in p['coefficient_certificates']),local_symbolic_identities=8,full_ring_identities=4,full_signed_modular_pairs=32,native_history_claim=False),
  scope=dict(same_complete_polynomial_and_supplied_positive_zero_sets=True,exact_degrees_inherited=True,ordinary_input_and_fixed_recipe_unchanged=True,older_terminal_and_IDLE_maps='ordinary-input only',predecessor_code_executed=False,new_diagnostic=False,universal84_unchanged=True,no_minimality_claim=True))
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(enc(r)==enc(load(a.expect)),'type-exact receipt')
 print('PASS cleanup tail fusion:1415/1412/1412/1409;550 coefficient rows;all16 words and whole outputs identical')
if __name__=='__main__':main()
