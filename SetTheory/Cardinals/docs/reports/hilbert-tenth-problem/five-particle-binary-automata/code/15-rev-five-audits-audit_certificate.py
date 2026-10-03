#!/usr/bin/env python3
"""Independent finite executable audit plus explicit residual-formula oracle."""
import argparse,copy,hashlib,importlib.util,itertools,json,pathlib,random,sys,time,traceback
from fractions import Fraction
ap=argparse.ArgumentParser();ap.add_argument('--module',default=str(pathlib.Path(__file__).resolve().parents[1]/'certificates'/'certificate.py'));ap.add_argument('--receipt',default='independent-receipt.json');ap.add_argument('--clean-source',default=str(pathlib.Path(__file__).resolve().parents[1]/'certificates'/'clean-target-sample-source.json'));a=ap.parse_args()
p=pathlib.Path(a.module).resolve();data=p.read_bytes();spec=importlib.util.spec_from_file_location('audited_certificate',p);M=importlib.util.module_from_spec(spec);sys.modules[spec.name]=M;spec.loader.exec_module(M)
start=time.time();counts={};tests=[];failures=[]
def check(c,msg):
 if not c:raise RuntimeError(msg)
def same(x,y,msg):check(x==y,f'{msg}: got {x!r}, want {y!r}')
def rejects(fn,msg):
 try:fn()
 except (TypeError,ValueError,AttributeError):return
 except Exception as e:raise RuntimeError(f'{msg}: unexpected {type(e).__name__}: {e}') from e
 raise RuntimeError(msg+': invalid operation accepted')
def test(name,fn):
 print('RUN',name,flush=True);t=time.time()
 try:fn();tests.append(dict(name=name,status='passed',seconds=round(time.time()-t,6)));print('PASS',name,flush=True)
 except Exception as e:
  trace=traceback.format_exc();tests.append(dict(name=name,status='failed'));failures.append(dict(name=name,error=str(e),traceback=trace));print(trace,flush=True)
T={'op':'true'}
def eq(i,k):return dict(op='eq',counter=i,value=k)
def gt(i,k):return dict(op='gt',counter=i,value=k)
def both(*gs):return dict(op='and',args=list(gs))
def either(*gs):return dict(op='or',args=list(gs))
def neg(g):return dict(op='not',arg=g)
def row(name='e',source='s',target='h',side=-1,delta=0,guard=None):return dict(name=name,source=source,target=target,side=side,delta=delta,guard=copy.deepcopy(T if guard is None else guard))
def src(rows=None,J=0,controls=None,start='s',halt='h'):return dict(schema='reversible-two-counter-v1',controls=['s','h'] if controls is None else list(controls),start=start,halt=halt,class_cut=J,branches=[row()] if rows is None else copy.deepcopy(rows))
def truth(g,c):
 op=g['op']
 if op=='true':return True
 if op=='eq':return c[g['counter']]==g['value']
 if op=='gt':return c[g['counter']]>g['value']
 if op=='not':return not truth(g['arg'],c)
 return (all if op=='and' else any)(truth(x,c) for x in g['args'])
def normalization(d):return [(i,c) for i,r in enumerate(d['branches']) for c in itertools.product(range(d['class_cut']+2),repeat=2) if truth(r['guard'],c)]
def trace(d,q,c,H):
 ans=[]
 for _ in range(H):
  choices=[(i,r) for i,r in enumerate(d['branches']) if r['source']==q and truth(r['guard'],c)]
  if not choices:return None
  check(len(choices)==1,'oracle nondeterministic fixture');i,r=choices[0];old=c;c=list(c);c[0 if r['side']==-1 else 1]+=r['delta'];c=tuple(c);q=r['target'];ans.append((i,old,c,q))
 return ans if q==d['halt'] else None
def geometry(d):
 m=len(d['controls']);p=sum(r['delta']!=0 for r in d['branches']);D=2*m+4*p
 return dict(D=D,S=2*D+2,Z=40*D+60+2*d['class_cut'])
def duration(d,r,c):
 g=geometry(d);return 1 if r['delta']==0 else 3+2*(g['Z']+c[0 if r['side']==-1 else 1])+r['delta']-4*g['S']
def independent_witness(d,f):
 tr=trace(d,f.initial_state,f.initial_counters,f.H)
 if tr is None:return None
 w=[0]*len(f.names);cells=normalization(d);J=d['class_cut'];theta=0
 for t,(i,old,new,q) in enumerate(tr):
  pos=cells.index((i,tuple(min(c,J+1) for c in old)))
  w[f.selectors[t][pos]]=1
  for k in (0,1):
   w[f.counters[t][k]]=new[k]
   if f.slacks[t][pos][k] is not None:w[f.slacks[t][pos][k]]=old[k]-J-1
  theta+=duration(d,d['branches'][i],old)
 if f.clock:w[f.theta]=theta
 return tuple(w)
# Sparse multivariate integer polynomials are independent dicts monomial -> coeff.
def add(*ps):
 ans={}
 for p in ps:
  for k,v in p.items():ans[k]=ans.get(k,0)+v
 return {k:v for k,v in ans.items() if v}
def scale(a,p):return {k:a*v for k,v in p.items() if a*v}
def mul(p,q):
 ans={}
 for k,a in p.items():
  for l,b in q.items():
   mon=tuple(sorted(k+l));ans[mon]=ans.get(mon,0)+a*b
 return {k:v for k,v in ans.items() if v}
def const(v):return {():v} if v else {}
def var(i):return {(i,):1}
def expected_rows(d,f):
 cells=normalization(d);rs=d['branches'];codes={q:i for i,q in enumerate(d['controls'])};J=d['class_cut'];out=[];allclock=[]
 if not f.H:out.append(('terminal',const(codes[f.initial_state]-codes[d['halt']])))
 for t,es in enumerate(f.selectors):
  e=[var(i) for i in es];old=[const(f.initial_counters[k]) if t==0 else var(f.counters[t-1][k]) for k in (0,1)]
  out.append((f'{t}.onehot',add(*e,const(-1))))
  if f.real:out.append((f'{t}.norm',add(*(mul(v,v) for v in e),const(-1))))
  q=add(*(scale(codes[rs[i]['source']],v) for (i,c),v in zip(cells,e)))
  prior=const(codes[f.initial_state]) if t==0 else add(*(scale(codes[rs[i]['target']],var(idx)) for (i,c),idx in zip(cells,f.selectors[t-1])))
  out.append((f'{t}.state',add(q,scale(-1,prior))))
  for k in (0,1):
   inc=add(*(scale(rs[i]['delta'],v) for (i,c),v in zip(cells,e) if (0 if rs[i]['side']==-1 else 1)==k))
   out.append((f'{t}.counter{k}',add(var(f.counters[t][k]),scale(-1,old[k]),scale(-1,inc))))
  for b,((i,c),v) in enumerate(zip(cells,e)):
   for k in (0,1):
    poly=mul(v,add(old[k],const(-c[k])))
    if c[k]==J+1:poly=add(poly,scale(-1,var(f.slacks[t][b][k])))
    out.append((f'{t}.class{b}.{k}',poly))
   r=rs[i];g=geometry(d);k=0 if r['side']==-1 else 1
   tau=const(1) if r['delta']==0 else add(const(3+2*g['Z']+r['delta']-4*g['S']),scale(2,old[k]))
   allclock.append(mul(v,tau))
 if f.H:out.append(('terminal',add(*(scale(codes[rs[i]['target']],var(idx)) for (i,c),idx in zip(cells,f.selectors[-1])),const(-codes[d['halt']]))))
 if f.clock:out.append(('clock',add(var(f.theta),scale(-1,add(*allclock)))))
 return out

def source_schema_domains():
 fixtures=[]
 for key,vals in [('class_cut',[True,False,0.,1.,-1,Fraction(1)]),('schema',[None,True,1,'bad']),('controls',[None,(),('s','h'),['s','s'],['s',True]]),('start',[None,True,'bad']),('halt',[None,True,'bad']),('branches',[None,(),{}])]:
  for v in vals:
   d=src();d[key]=v;fixtures.append(d)
 for key in src():
  d=src();del d[key];fixtures.append(d)
 d=src();d['extra']=0;fixtures.append(d)
 for field in ('side','delta'):
  for v in (True,False,0.,1.,'1',None,Fraction(1)):
   d=src();d['branches'][0][field]=v;fixtures.append(d)
 badguards=[{'op':'false'},{'op':'other'}, {'op':'true','extra':0},{1:'true'}, {'op':'true',1:0}, {'op':'and','args':()}, {'op':'not'}]
 for k in (True,False,0.,1.,-1,None,Fraction(1)):
  badguards.extend([eq(0,k),eq(k,0)])
 for g in badguards:
  d=src();d['branches'][0]['guard']=g;fixtures.append(d)
 for d in fixtures:rejects(lambda d=d:M.load_machine(d),'strict shared JSON validation')
 semantics=[src([row(delta=-1)]),src([row(delta=1,guard=eq(0,0))]),src([row('a'),row('b')]),src([row('a',source='s',delta=1),row('b',source='t',delta=0)],1,['s','t','h']),src([row(source='h')])]
 for d in semantics:rejects(lambda d=d:M.load_machine(d),'all-input source validation')
 counts['schema_rejections']=len(fixtures);counts['semantic_rejections']=len(semantics)

def constructor_and_snapshot_immutability():
 d=src();m,q=M.load_machine(d);f=M.Certificate(m,1,q,[0,0],clock=True);w=f.witness();ledger=f.ledger()
 d['controls'].append('bad');d['branches'][0]['guard']['op']='not';d['branches'][0]['delta']=1
 same(f.witness(),w,'JSON snapshot mutation');same(f.ledger(),ledger,'JSON snapshot ledger')
 b=m.branches[0];cell=m.cells[0]
 rejects(lambda:b.__init__('e','s','h',0,1,True),'Branch reinitialization mutation')
 rejects(lambda:m.__init__(['s','h'],[],'h',0),'Machine reinitialization mutation')
 rejects(lambda:cell.__init__(99,(0,0)),'CellBranch reinitialization mutation')
 rejects(lambda:f.__init__(m,0,q,(0,0)),'Certificate reinitialization mutation')
 same(f.witness(),w,'reinitialization attempts changed certificate')
 for obj,field in ((b,'guard'),(m,'J'),(cell,'classes'),(f,'H')):rejects(lambda obj=obj,field=field:setattr(obj,field,None),'frozen setattr')
 for fld in ('names','selectors','counters','slacks','residuals'):check(type(getattr(f,fld)) is tuple,'compiled container must be tuple')
 try:m.control_codes['s']=99
 except TypeError:pass
 else:raise RuntimeError('codes mutable')
 mutable_guard=['or',['eq',0,0],['eq',0,0]];b=M.Branch('a','s','h',0,0,mutable_guard);mutable_guard[1][2]=100
 m=M.Machine(['s','h'],[b],'h',0);same(m.transition('s',(0,0))[1],'h','internal guard snapshot')
 counts['reinitialization_mutation_probes']=4

def formulas_counts_clock_and_coefficients():
 ds=[src([row(target='s')]),src([row(target='s',delta=1)]),src([],0),src([],0,['h'],'h','h'),src([row()]),src([row(delta=1)],0),src([row(delta=-1,side=1,guard=gt(1,0))],0),src([row(guard=both(gt(0,0),gt(1,0)))]),src([row(guard=either(eq(0,0),eq(0,0)))]),src([row(guard=both())]),src([row(guard=either())]),src([row('a',target='t',delta=1),row('b',source='t',delta=-1,side=1,guard=gt(1,0))],1,['s','t','h'])]
 count=0;rowcount=0;expcount=0;accepts=0;mutated=0;rng=random.Random(773)
 for d in ds:
  m,q=M.load_machine(d);cells=normalization(d)
  same([(c.original,c.classes) for c in m.cells],cells,'disjoint complete normalization')
  for H in range(4):
   for initial in ((0,0),(1,2)):
    for real,clock in itertools.product((False,True),repeat=2):
     f=M.Certificate(m,H,q,initial,clock=clock,nonnegative_real=real);want=independent_witness(d,f);same(f.witness(),want,'independent source trace witness')
     B=len(cells);r=sum(a==d['class_cut']+1 for i,c in cells for a in c);P=sum(d['branches'][i]['delta']!=0 for i,c in cells)
     same(len(f.names),H*(B+2+r)+int(clock),'exact variable count')
     same(len(f.residuals),H*(4+2*B+int(real))+1+int(clock),'exact residual slots')
     expected=expected_rows(d,f)
     got=[(label,{mon:coef for coef,mon in ts}) for label,ts in f.residuals];same(got,expected,'exact coefficient residual identity')
     check(all(len(mon)<=2 for label,p in expected for mon in p),'quadratic residuals')
     expanded=add(*(mul(poly,poly) for label,poly in expected));same({mon:coef for coef,mon in f.expanded()},expanded,'exact expanded quartic coefficients')
     check(all(len(mon)<=4 for mon in expanded),'quartic degree bound')
     l=f.ledger();same(l['expanded_ordered_occurrence_bound'],sum(len(poly)**2 for label,poly in expected),'squaring term count')
     if H:
      bound=H*(7*B+P+r+5)+2+int(real)*H*(B+1)+int(clock)*(1+H*(B+P));check(sum(len(poly) for label,poly in expected)<=bound,'written slot bound')
     g=geometry(d);kap=max([1]+[3+2*g['Z']+rr['delta']-4*g['S'] for rr in d['branches'] if rr['delta']]);mx=max(initial)
     coef=max(2,len(d['controls'])-1,d['class_cut']+1,mx+d['class_cut']+1,kap+2*mx if clock else 0)
     check(all(abs(v)<=coef for label,poly in expected for v in poly.values()),'residual coefficient height')
     if 'residual_coefficient_height' in l:same(l['residual_coefficient_height'],max((abs(v) for label,poly in expected for v in poly.values()),default=0),'actual residual coefficient ledger')
     if 'total_witness_coordinate_bit_bound' in l:same(l['total_witness_coordinate_bit_bound'],l['total_witness_coordinate_height_bound'].bit_length(),'witness bit ledger')
     check(all(abs(v)<=sum(len(poly)**2 for label,poly in expected)*coef**2 for v in expanded.values()),'expanded coefficient height')
     if want is not None:
      accepts+=1;same(f.evaluate(want),0,'witness satisfies SOS')
      if clock:same(want[f.theta],sum(duration(d,d['branches'][i],old) for i,old,new,qq in trace(d,q,initial,H)),'clock source horizon distinction')
      for idx in range(len(want)):
       changed=list(want);changed[idx]+=1;check(f.evaluate(changed)>0,'inactive slack/other coordinate not forced');mutated+=1
     for _ in range(2):
      w=[rng.randrange(4) for _ in f.names]
      def ev(poly):
       result=0
       for mon,coef_ in poly.items():
        val=coef_
        for i in mon:val*=w[i]
        result+=val
       return result
      same(f.evaluate(w),sum(ev(poly)**2 for label,poly in expected),'independent numerical SOS')
     count+=1;rowcount+=len(expected);expcount+=len(expanded)
 counts.update(certificate_variants=count,accepted_variants=accepts,exact_residual_rows=rowcount,expanded_coefficients=expcount,complete_witness_single_coordinate_mutations=mutated)

def complete_small_fibers_and_real_norm():
 cases=[(both(eq(0,0),eq(1,0)),(0,0)),(both(eq(0,0),eq(1,0)),(1,0)),(both(gt(0,0),gt(1,0)),(1,1)),(either(both(eq(0,0),eq(1,0)),both(gt(0,0),gt(1,0))),(1,1))]
 tried=0;fibers=[]
 for g,c in cases:
  d=src([row(guard=g)]);m,q=M.load_machine(d)
  for real in (False,True):
   f=M.Certificate(m,1,q,c,nonnegative_real=real);domain=(0,Fraction(1,2),1,2) if real else (0,1,2);zs=[]
   for w in itertools.product(domain,repeat=len(f.names)):
    if f.evaluate(w)==0:zs.append(w)
    tried+=1
   want=f.witness();same(zs,[] if want is None else [want],'complete bounded natural/rational fiber')
   fibers.append(dict(variables=len(f.names),real=real,zeros=len(zs),enumerated=len(domain)**len(f.names)))
 # Exposes why norms are paid, with two disjoint image branches.
 d=src([row('a',source='l',delta=1,guard=both(eq(0,0),eq(1,0))),row('b',source='r',delta=0,guard=both(eq(0,0),eq(1,0)))],1,['l','mid','r','h'],start='mid')
 m,q=M.load_machine(d);f=M.Certificate(m,1,q,(0,0),nonnegative_real=True);w=[Fraction(1,2),Fraction(1,2),Fraction(1,2),0]
 vals=dict(f.residual_values(w));check(all(v==0 for k,v in vals.items() if k!='0.norm'),'unpaid real counterexample');same(vals['0.norm'],Fraction(-1,2),'norm rejects fractional mixture');check(f.evaluate(w)>0,'paid real test')
 counts.update(complete_fiber_tuples=tried,complete_fibers=fibers)

def numeric_domain_and_asts():
 m,q=M.load_machine(src());f=M.Certificate(m,1,q,(0,0));r=M.Certificate(m,1,q,(0,0),nonnegative_real=True);checks=0
 for bad in (True,False,-1,0.,1.,Fraction(0),None,'0'):
  rejects(lambda bad=bad:M.Certificate(m,bad,q,(0,0)),'exact natural horizon')
  rejects(lambda bad=bad:M.Certificate(m,1,q,(bad,0)),'exact natural initial counter')
  w=list(f.witness());w[0]=bad;rejects(lambda w=w:f.evaluate(w),'exact natural witness');checks+=3
 for bad in (True,False,-1,0.,1.,None,'0'):
  w=list(r.witness());w[0]=bad;rejects(lambda w=w:r.evaluate(w),'exact rational nonnegative witness');checks+=1
 for bad in (0,1,None,'yes'):
  rejects(lambda bad=bad:M.Certificate(m,1,q,(0,0),clock=bad),'Boolean clock flag');rejects(lambda bad=bad:M.Certificate(m,1,q,(0,0),nonnegative_real=bad),'Boolean real flag');checks+=2
 rejects(lambda:f.evaluate([]),'witness size');rejects(lambda:r.evaluate([Fraction(0)]),'real witness size')
 g=T
 for _ in range(10000):g={'op':'not','arg':g}
 d=src();d['branches'][0]['guard']=g;m,q=M.load_machine(d);check(m.transition(q,(0,0)) is not None,'deep guard JSON')
 cyc={'op':'not'};cyc['arg']=cyc;d=src();d['branches'][0]['guard']=cyc;rejects(lambda:M.load_machine(d),'cyclic guard rejected explicitly')
 internal=['not'];internal.append(internal);rejects(lambda:M.Branch('b','s','h',0,0,internal),'cyclic internal AST')
 counts.update(numeric_invalid_probes=checks+2,deep_AST_nesting=10000)

def clean_target_clock():
 wrapped=pathlib.Path(a.clean_source)
 d=json.loads(wrapped.read_text());m,q=M.load_machine(d);f=M.Certificate(m,4,q,(0,0),clock=True);w=f.witness();check(w is not None,'clean target full source witness');same(w[f.theta],2834,'full clean clock with enlarged constants');same(m.geometry()['D'],18,'enlarged geometry');same(m.duration(0,(0,0)),1416,'enlarged forward leg');same(m.duration(1,(1,0)),1416,'reverse duration symmetry')
 same(f.counters[-1] and tuple(w[i] for i in f.counters[-1]),(0,0),'clean target restored counters')
 l=f.ledger();same((l['normalized_branches'],l['tail_occurrences'],l['normalized_nonzero_branches'],l['variables'],l['residual_slots']),(33,23,15,233,282),'clean target full paid counts')
 same([(label,{mon:coef for coef,mon in ts}) for label,ts in f.residuals],expected_rows(d,f),'clean target exact coefficients')
 fr=M.Certificate(m,4,q,(0,0),clock=True,nonnegative_real=True);same(fr.ledger()['residual_slots'],286,'clean target real norm charges')
 for H in (0,1,2,3,5):same(M.Certificate(m,H,q,(0,0)).witness(),None,'clean target exact horizon')
 # Zero original steps still requires both cleanup bridges, on enlarged source.
 d=src([row('turn',source='Fh',target='Bh'),row('clean',source='Bh',target='H')],0,['Fh','Bh','H'],'Fh','H');m,q=M.load_machine(d);f=M.Certificate(m,2,q,(0,0),clock=True);same(f.witness()[f.theta],2,'h0 clean bridges')
 counts['clean_target_clock_checks']=11

for name,fn in [('schema_and_all_input_domains',source_schema_domains),('immutable_snapshots_reinitialization',constructor_and_snapshot_immutability),('independent_exact_polynomials_counts_clocks',formulas_counts_clock_and_coefficients),('complete_small_fibers_paid_real',complete_small_fibers_and_real_norm),('strict_numeric_domains_deep_AST',numeric_domain_and_asts),('clean_target_enlarged_clock',clean_target_clock)]:test(name,fn)
if p.read_bytes()!=data:failures.append(dict(name='producer_changed_during_audit',error='Emitter bytes changed during run'))
receipt=dict(status='failed' if failures else 'passed',optimized=not __debug__,python=sys.version,producer_file=p.name,producer_sha256=hashlib.sha256(data).hexdigest(),audit_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),counts=counts,tests=tests,failures=failures,seconds=round(time.time()-start,6),scope='Independent finite executable regression plus proof review; not a machine-checked all-H proof or a CA full-shift proof.')
pathlib.Path(a.receipt).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(bool(failures))
