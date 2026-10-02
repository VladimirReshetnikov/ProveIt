"""Portable pinned finite review of Exact Convergence and Total Quadratic Semantics.

verify(bellman_root, quadratic_root) reads untouched archive package roots;
all generated fixtures live in a temporary directory. No checkout paths,
network access or persistent receipt writes are required.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from itertools import product
from math import lcm,prod
from contextlib import contextmanager
import argparse,hashlib,importlib.util,json,random,subprocess,sys,copy,tempfile

PINS={
 'bellman_diophantine.py':'5a5b20f384afb64f9a408dcd7a86f1e9c27dabfb9fcf9401540d479512391397',
 'check_certificate.py':'44ed5e089bd4e42ae4bf665d816fd92c1fb067cb6778702f7b36391d61230aec',
 'quadratic_compiler.py':'a6894f6c3da3ee8c3bce24875d34bd9df4b2d77546f162bf63a5648d618cebef',
 'verify_exports.py':'0574c6082a3ac09aecd3684046e31cf80b825493f328daddd6c591798105fb14'}

@contextmanager
def modules(paths):
 missing=object();saved={};made={}
 try:
  for name,path in paths:
   saved[name]=sys.modules.get(name,missing);spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);made[name]=module
  yield made
 finally:
  for name,old in saved.items():
   if old is missing:sys.modules.pop(name,None)
   else:sys.modules[name]=old

def verify(bellman_root,quadratic_root):
 if not __debug__:raise RuntimeError('Assertions are required')
 B,Q=Path(bellman_root),Path(quadratic_root)
 paths=[('_review808_bell',B/'code/bellman_diophantine.py'),('_review808_bcheck',B/'code/check_certificate.py'),('_review808_quad',Q/'code/quadratic_compiler.py'),('_review808_qcheck',Q/'code/verify_exports.py')]
 for name,path in paths:assert hashlib.sha256(path.read_bytes()).hexdigest()==PINS[path.name]
 with tempfile.TemporaryDirectory(prefix='incoming808-convergence-') as tmp,modules(paths) as loaded:
  scratch=Path(tmp);bell,bc,quad,qc=(loaded[name] for name,path in paths);pins=dict(PINS)
  counts=Counter();rng=random.Random(80820261002);findings={}
  def check(ok,label):assert ok,label;counts[label]+=1
  def reject(fn,label):
   try:fn()
   except (ValueError,TypeError,AssertionError,KeyError,IndexError):counts[label]+=1
   else:raise AssertionError(label)
  def rational_step(game,v):
   eta=F(game['common_uniform_reset']);discount=F(game['discount']);reward=F(game.get('common_reward','0'));n=game['states'];out=[]
   for i,actions in enumerate(game['base_actions']):
    av=[sum(F(p)*v[j] for j,p in a) for a in actions]
    z=max(av) if game['owners'][i]=='max' else min(av)
    out.append(reward+discount*((1-eta)*z+eta*sum(v)/n))
   return out
  # Rebuild the entire emitted Bellman polynomial from the external game and true input.
  def reconstruct_certificate(data,game):
   meta=data['metadata'];n=game['states'];owners=game['owners'];eta=F(game['common_uniform_reset']);discount=F(game['discount']);reward=F(game.get('common_reward','0'))
   target=F(meta['target']) if meta['terminal_mode']=='point' else None
   mult=lcm(reward.denominator,1 if target is None else target.denominator);den=meta['initial_denominator'];scale=den*mult;A=[mult*x for x in meta['input_numerators']]
   assert meta['initial_numerators']==A and meta['witness_scale']==scale
   if 'initial_terminal_payoffs' in game:assert [F(x,den) for x in meta['input_numerators']]==list(map(F,game['initial_terminal_payoffs']))
   rows=[]
   for aa in game['base_actions']:
    ar=[]
    for a in aa:
     row=[eta/n]*n
     for j,p in a:row[j]+=(1-eta)*F(p)
     assert sum(row)==1 and min(row)>=0;ar.append(row)
    rows.append(ar)
   D=lcm(*(v.denominator for aa in rows for row in aa for v in row));assert D==meta['probability_denominator'];a,b=discount.numerator,discount.denominator
   rows=[[[int(D*v)*a for v in row] for row in aa] for aa in rows]
   labels=[];values=[];squares=[];products=[];previous=None;old=A;T=meta['horizon']
   def clean(d):return {j:c for j,c in d.items() if c}
   for t in range(T):
    forcing=scale*(b*D)**(t+1)*reward;assert forcing.denominator==1;forcing=int(forcing)
    avs=[[sum(c*x for c,x in zip(row,old))+forcing for row in aa] for aa in rows]
    new=[max(av) if owners[i]=='max' else min(av) for i,av in enumerate(avs)]
    cur=list(range(len(labels),len(labels)+n));labels.extend(f'X_{t+1}_{i}' for i in range(n));values.extend(new)
    for i,aa in enumerate(rows):
     gaps=[]
     for h,row in enumerate(aa):
      sign=-1 if owners[i]=='max' else 1;r=defaultdict(int);r[cur[i]]-=sign;r[-1]+=sign*forcing
      for j,c in enumerate(row):r[-1 if previous is None else previous[j]]+=sign*c*(A[j] if previous is None else 1)
      if len(aa)==2:
       gi=len(labels);labels.append(f'gap_{t}_{i}_{h}');values.append(sign*(avs[i][h]-new[i]));gaps.append(gi);r[gi]-=1
      squares.append(clean(r))
     if gaps:products.append(gaps)
    old=new;previous=cur
   endpoints=[(i,None) for i in range(n)] if target is not None else [(i,0) for i in range(1,n)] if meta['terminal_mode']=='consensus' else [meta['observed_pair']]
   for i,j in endpoints:
    r=defaultdict(int);r[-1 if previous is None else previous[i]]+=A[i] if previous is None else 1
    if j is None:r[-1]-=int(scale*(b*D)**T*target)
    else:r[-1 if previous is None else previous[j]]-=A[j] if previous is None else 1
    squares.append(clean(r))
   assert labels==data['variable_labels'];assert values==data['assignment'];assert squares==[dict(row) for row in data['squared_linear_forms']];assert products==[list(p) for p in data['nonnegative_products']]
   return {'variables':len(labels),'squares':len(squares),'products':len(products),'linear_terms':sum(map(len,squares))}
  replays=[]
  for name in ['small','countdown','fixedpoint']:
   args=[sys.executable,str(B/'code/check_certificate.py'),str(B/f'artifacts/{name}_certificate.json'),'--game',str(B/f'artifacts/{name}_game.json')]
   done=subprocess.run(args,check=True,capture_output=True,text=True);result=json.loads(done.stdout);assert result['polynomial_value']==0;replays.append(result)
   data=json.loads((B/f'artifacts/{name}_certificate.json').read_text());game=json.loads((B/f'artifacts/{name}_game.json').read_text());ledger=reconstruct_certificate(data,game);counts['complete_bellman_source_reconstructions']+=1
  for name in ['locking_counterexample','literal_four_tile_example','timed_race','huge_delay_chain']:
   check(qc.verify(Q/f'results/{name}.json')['status']=='PASS','quadratic_independent_export_replays')
  # Independent every-microstep checks against a hand-written source interpreter.
  programs=[bell.Program(1,(bell.Instruction('halt'),)),bell.Program(1,(bell.Instruction('inc',0,0),bell.Instruction('halt'))),bell.Program(1,(bell.Instruction('dec',0,0,1),bell.Instruction('halt'))),bell.Program(2,(bell.Instruction('inc',1,1),bell.Instruction('dec',0,2,3),bell.Instruction('dec',1,0,3),bell.Instruction('halt')))]
  def source_step(program,state,cs):
   cs=list(cs);ins=program.instructions[state]
   if ins.op=='inc':cs[ins.counter]+=1;state=ins.target
   elif ins.op=='dec':
    if cs[ins.counter]==0:state=ins.zero
    else:cs[ins.counter]-=1;state=ins.target
   return state,tuple(cs)
  for program in programs:
   for erase in [False,True]:
    compiled=bell.compile_program(program,reset=F(1,2),erase_halt=erase,reward=F(1,4));game=compiled.game.export();states=len(program.instructions);steps=4*compiled.macro
    for initial_state in range(states):
     counters=tuple(2+i for i in range(program.counters));configs=[];state=initial_state;cs=counters;zero=False
     for j in range(6):
      x=[F(0)]*(1+states+program.counters) if zero else [F(1)]+[F(i==state) for i in range(states)]+[F(1,2**c) for c in cs]
      configs.append(x)
      if erase and program.instructions[state].op=='halt':zero=True
      else:state,cs=source_step(program,state,cs)
     v=compiled.initialize(initial_state,counters)
     for t in range(steps+1):
      j=(t+compiled.macro-1)//compiled.macro;expected=[F(1,2)+F(1,2)*F(1,4)**t*x/compiled.scale**j for x in configs[j]]
      check([v[compiled.plus(i)] for i in range(compiled.circuit.inputs)]==expected,'independent_pipeline_microsteps')
      check(all(v[compiled.plus(i)]+v[compiled.minus(i)]==1 for i in range(len(compiled.circuit.gates))),'independent_paired_channels')
      v=rational_step(game,v)
  # Native small Bellman certificates with nonzero reward, arbitrary rational discount/reset.
  for case in range(24):
   n=1+case%3;owners=tuple(['lin','min','max'][(case+i)%3] for i in range(n));actions=[]
   for i,o in enumerate(owners):
    aa=[]
    for k in range(1 if o=='lin' else 2):
     j=(i+k)%n;aa.append(((j,F(1)),))
    actions.append(tuple(aa))
   game=bell.Game(owners,tuple(actions),F(1,3),F(2,3),F(1,7));A=[rng.randrange(4) for _ in range(n)];den=1+case%3;T=case%5
   for mode in ['pair','consensus','point']:
    q=bell.certificate(game,A,T,(0,n-1),den,target=F(3,7) if mode=='point' else None,consensus=mode=='consensus')
    path=scratch/'small_certificate.json';q.export(path);data=json.loads(path.read_text());reconstruct_certificate(data,game.export());counts['small_complete_source_reconstructions']+=1
    v=[F(a,den) for a in A]
    for _ in range(T):v=rational_step(game.export(),v)
    truth=all(x==F(3,7) for x in v) if mode=='point' else len(set(v))==1 if mode=='consensus' else v[0]==v[-1]
    check((q.evaluate()==0)==truth,'independent_rational_endpoint_equivalence')
  # Independent calendar: queue rules once prerequisites become known; compare source simulator.
  def events(net,delays):
   labels={v:a for v,a in net.seeds};times={v:0 for v,a in net.seeds};pending={};fired=set()
   while True:
    for i,r in enumerate(net.rules):
     if i not in fired and all(labels.get(u)==a for u,a in r.tail):
      pending[i]=max((times[u] for u,a in r.tail),default=0)+delays[i];fired.add(i)
    pending={i:t for i,t in pending.items() if net.rules[i].head[0] not in labels}
    if not pending:break
    now=min(pending.values());off=defaultdict(list)
    for i,t in pending.items():
     if t==now:
      v,a=net.rules[i].head;off[v].append(a)
    for v,aa in off.items():labels[v]=min(aa);times[v]=now
   return [labels.get(v,0) for v in range(net.sites)],[times.get(v) for v in range(net.sites)]
  for case in range(80):
   n=1+case%5;q=1+case%3;seeds=tuple((i,1+rng.randrange(q)) for i in range(n) if rng.randrange(4)==0);free=[i for i in range(n) if i not in dict(seeds)];lits=list(product(range(n),range(1,q+1)))
   rules=tuple(quad.Rule((rng.choice(free),1+rng.randrange(q)),tuple(sorted(rng.sample(lits,rng.randrange(min(3,len(lits))+1))))) for _ in range(rng.randrange(9))) if free else ()
   net=quad.Network(n,q,seeds,rules)
   for timed in [False,True]:
    ds=[1+rng.randrange(10) if timed else 1 for _ in rules];c=quad.Compiled(net,timed);w,labels,times=c.witness(ds)
    check((labels,times)==events(net,ds),'independent_calendar_instances')
    G=sum(len(r.tail) for r in rules)+sum(not r.tail for r in rules);D=len({p for r in rules for p in r.tail if p[0] in free});m=len(free);R=len(rules) if timed else 0
    check(len(c.c.variables)==m*(2*q+3)+3*D+3*G+R and len(c.c.residuals)==R+m*(q+2)+2*D+2*G and len(c.c.products)==2*D+G+m*(q+1),'complete_quadratic_ledgers')
    p=c.c.expanded()
    for _ in range(3):
     vals={x:rng.randrange(4) for x in c.c.parameters+c.c.variables};value=sum(a*prod(vals[x] for x in mon) for mon,a in p.items());check(value==c.c.evaluate(vals) and value>=0,'independent_offzero_quadratics')
    if q==1:
     h=quad.HornCompiled(net,timed);hw,hl,ht=h.witness(ds);check((hl,ht)==(labels,times) and len(h.c.variables)==m+3*G+R,'horn_specialization')
  # Actual input-binding defect: declared source has unequal horizon-one values.
  game=bell.Game(('lin','lin'),((((0,F(1)),),),(((1,F(1)),),)));q=bell.certificate(game,[0,0],1,(0,1));path=scratch/'false_initial_certificate.json';q.export(path)
  data=json.loads(path.read_text());data['metadata']['input_numerators']=[1,0];path.write_text(json.dumps(data));g=game.export();g['initial_terminal_payoffs']=['1','0'];gp=scratch/'false_initial_game.json';gp.write_text(json.dumps(g));accepted=bc.check(path,gp)
  assert accepted['polynomial_value']==0 and rational_step(g,[F(1),F(0)])==[F(1,2),F(0)];reject(lambda:reconstruct_certificate(data,g),'independent_checker_rejects_false_initial_binding')
  findings['bellman_unbound_scaled_initial_vector']={'checker_result':accepted,'declared_input':[1,0],'actual_endpoint':['1/2','0'],'forged_internal_scaled_input':data['metadata']['initial_numerators']}
  seeds=[(0,1)];net=quad.Network(2,2,seeds,(quad.Rule((1,1),((0,1),)),));c=quad.Compiled(net,False);w,labels,times=c.witness();seeds[0]=(0,2);actual=events(c.net,[1]);assert actual!= (labels,times) and c.c.evaluate(w)==0
  findings['quadratic_mutable_seed']={'certified':[labels,times],'current_semantics':actual,'old_zero_value':c.c.evaluate(w)}
  e=c.c.export(w);e['witnesses'].clear();findings['quadratic_export_alias']={'compiler_variable_count_after_export_edit':len(c.c.variables),'source_polynomial_still_has_terms':bool(c.c.residuals)};assert not c.c.variables
  net=quad.Network(1,2,((0,1.5),),());c=quad.Compiled(net,False);w,labels,times=c.witness();assert labels==[1.5] and c.c.evaluate(w)==0;findings['quadratic_fractional_seed_label_accepted']={'labels':labels,'times':times,'zero':w}
  # Exact bounds which actually are enforced, without overstating permissive APIs.
  for bad in [True,1.,-1]:
   reject(lambda bad=bad:bell.certificate(game,[bad,0],1,(0,1)),'bellman_natural_input_rejections')
   reject(lambda bad=bad:bell.certificate(game,[0,0],bad,(0,1)),'bellman_natural_input_rejections')
   reject(lambda bad=bad:q.evaluate([bad,0]),'bellman_natural_input_rejections')
  for bad in [0,-1,1.5]:
   reject(lambda bad=bad:quad.simulate(quad.Network(1,1,(),(quad.Rule((0,1),()),)),[bad]),'quadratic_delay_rejections')
  result={'status':'PASS_WITH_UPSTREAM_API_FINDINGS','pins':pins,'counts':dict(counts),'findings':findings,'original_bellman_cli_replays':replays,'scope':'Both full mathematical articles and all supplied compiler/checker code read. Native source transfer, every-microstep and finite-domain checks only; no instantiated universal game or fixed-size unbounded quadratic.'}

  return result

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--bellman-root',required=True);p.add_argument('--quadratic-root',required=True);p.add_argument('--output');a=p.parse_args();result=verify(a.bellman_root,a.quadratic_root);raw=json.dumps(result,indent=2)+'\n'
 if a.output:Path(a.output).write_text(raw)
 print(json.dumps({'status':result['status'],'counts':result['counts'],'findings':list(result['findings'])},indent=2))
