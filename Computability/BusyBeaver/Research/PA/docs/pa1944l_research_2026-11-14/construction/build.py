#!/usr/bin/env python3
"""Reconstruct three new 194-state tables from pinned text inputs.

The 4R table preserves every resolved source instruction.  The radix5/6
machines replace only the 61 four-increment multiplication bodies; the
complete source boundary binding and generic AX formula structure are
checked below.  All physical cases are independently replayable in the
separate literal checker. No proof-assistant endpoint is claimed.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INC=('leaf','inc',1)
BASE_NODES=c.raw_nodes
EXPECTED={
 '4R':'a3c1d556d61b37d60639801accacfa595df4b2c9d2b2a0a46978425b10c459a8',
 '5':'180a0fd1f046d4cbd687b43979f0605619ad5f53054d32b9f62f33e7a3bccab8',
 '6':'725ce8474d7b83473488fc9466548ed2de3744d9a80183467894f9d719103ab2'}

def sha(raw):return hashlib.sha256(raw).hexdigest()
def write_json(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def targets(row):
 return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else()
def body_paths(grammar,ns,target='node61'):
 out=[]
 def walk(t,p):
  if isinstance(t,str):
   if t==target:out.append(p)
   return walk(grammar if t=='x67'else ns[t],p)
  if c.isnode(t):walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',())
 return out

def source_binding(grammar,oldsites,oldins,ns,sites,ins,k):
 oldpaths=body_paths(grammar,BASE_NODES());newpaths=body_paths(grammar,ns)
 assert oldpaths==newpaths and len(oldpaths)==61
 conspaths=body_paths(grammar,BASE_NODES(),'node65')
 assert conspaths==body_paths(grammar,ns,'node65')
 assert [p+(1,1,1,0)for p in conspaths]==oldpaths
 assert [name for name,t in BASE_NODES().items()if 'node61'in t]==['node62']
 blocks=[];old_removed=set();new_removed=set();oldfirst={};newfirst={}
 cons_prefix=[('dec',2,8,1),('inc',7,2),('dec',6,4,3),('jump',7),
  ('dec',7,7,5),('inc',6,6),('jump',4),('jump',0),('dec',7,11,9),
  ('inc',2,10),('jump',8),('dec',1,15,12),('inc',7,13),('inc',6,14),
  ('jump',11),('dec',6,21,16),('inc',7,17),('dec',6,20,18),
  ('inc',1,19),('jump',17),('jump',11)]
 for p,cp in zip(oldpaths,conspaths):
  oi=[i for i,(q,op,a)in enumerate(oldsites)if q[:len(p)]==p]
  ni=[i for i,(q,op,a)in enumerate(sites)if q[:len(p)]==p]
  assert oi==list(range(oi[0],oi[0]+4)) and ni==list(range(ni[0],ni[0]+k))
  for indices,code in ((oi,oldins),(ni,ins)):
   first=indices[0];end=indices[-1]+1
   base=first-22
   prefix=[]
   for row in code[base:base+21]:
    prefix.append(row[:2]+tuple(v-base for v in row[2:])if row[0]in('inc','dec')else('jump',row[1]-base))
   assert prefix==cons_prefix
   assert all(code[i]==('inc',1,i+1)for i in indices)
   assert code[first-1]==('dec',7,end+1,first)
   assert code[end]==('jump',first-1)
  old_removed.update(oi);new_removed.update(ni)
  oldfirst[oi[0]]=ni[0];newfirst[ni[0]]=oi[0]
  blocks.append({'path':''.join(map(str,p)),'old_start':oi[0],'new_start':ni[0],
                 'old_length':4,'new_length':k,'test_old':oi[0]-1,'test_new':ni[0]-1,
                 'cons_path':''.join(map(str,cp)),'cons_entry_old':oi[0]-22,'cons_entry_new':ni[0]-22,
                 'cons_exit_old':oi[0]+5,'cons_exit_new':ni[0]+k+1})
 old_kept=[i for i in range(len(oldins))if i not in old_removed]
 new_kept=[i for i in range(len(ins))if i not in new_removed]
 assert len(old_kept)==len(new_kept)==3429
 reloc=dict(zip(old_kept,new_kept));reloc.update(oldfirst)
 def projected(row):
  if row[0]in('inc','dec'):return row[:2]+tuple(reloc[t]for t in row[2:])
  if row[0]=='jump':return('jump',reloc[row[1]])
  return row
 for old,new in zip(old_kept,new_kept):assert projected(oldins[old])==ins[new]
 # No source edge enters the interior of an increment body from outside it.
 for code,removed,entries in ((oldins,old_removed,oldfirst),(ins,new_removed,newfirst)):
  for i,row in enumerate(code):
   if i not in removed:assert all(t not in removed or t in entries for t in targets(row))
 assert reloc[25]==25 and oldsites[25][0]==sites[25][0]
 assert len(sites)==3673+61*(k-4)
 return {'factor':k,'body_occurrences':61,'unchanged_primitive_sites':3429,
         'all_61_bodies_are_inside_distinct_cons_macros':True,
         'all_cons_have_exact_21_site_unpair_and_pair_prefix':True,
         'all_outside_edges_preserved_under_relocation':True,
         'all_bodies_are_k_increment_loops_on_register1':True,
         'loop_counter_register':7,'no_external_entry_to_body_interiors':True,
         'same_seed_site':25,'all_resolved_instructions_equal':ins==oldins,'bodies':blocks}

def emitter_audit(grammar,k):
 ZERO=('zero',);ONE=('succ',ZERO)
 def succ(x):return('succ',x)
 def I(a,b):return('I',k,a,b)
 def M(a,b):return succ(I(a,b))
 def U(a,B):return succ(succ(I(B,a)))
 def E(a,b):return succ(succ(succ(I(a,b))))
 def N(B):return I(B,ONE)
 def And(a,b):return N(I(a,N(b)))
 def Ex(a,B):return N(U(a,N(B)))
 names={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA',
   'node65':'cons','node72':'readH','node75':'readDCons','node142':'copyGuard',
   'node150':'compareGuard',INC:'incT',('leaf','breakTo',1):'close'}
 def word(t):
  if t=='node60':return['incT']*2
  if t=='node61':raise AssertionError('AX coefficient macro unexpectedly used as a literal tag')
  if c.isnode(t):return word(t[0])+word(t[1])
  return[names[t]]
 ww=word(grammar);assert len(ww)==190
 run=maximum_run=0
 for op in ww:
  run=run+1 if op=='incT'else 0
  maximum_run=max(maximum_run,run)
 assert maximum_run==3
 oldt,A,d,h,Y,X=(('atom',a)for a in('t','a','d','h','y','x'))
 T,D,H=oldt,d,h;stack=[];fields=[Y,X]
 for op in ww[:-3]:
  if op=='push':stack.append(T);T=ZERO
  elif op in('copyD','copyH','copyA'):stack.append(T);T={'copyD':D,'copyH':H,'copyA':A}[op]
  elif op=='cons':T=I(stack.pop(),T)
  elif op=='incT':T=succ(T)
  elif op=='readH':H=('add',H,fields.pop(0))
  elif op=='readDCons':D=('add',D,fields.pop(0));T=I(T,D)
  else:raise AssertionError(op)
 assert not fields and ww[-3:]==['copyGuard','compareGuard','close']
 heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),
   I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),
   Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
 rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
 gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)))
 point=I(A,M(A,D));S=U(D,And(I(M(H,D),point),I(M(A,D),A)))
 Q=U(A,I(S,N(point)))
 assert stack==[oldt,U(d,h),rho]+heads+[gamma]
 assert T==N(I(v,Q))
 return {'radix':k,'macro_tokens':190,'pushed_items':10,'ordinary_universal_heads':6,
   'maximum_consecutive_literal_increments':3,
   'complete_stack_and_top_match_free_constructor_algebra':True,
   'guard':'A=D or A=H returns truth; clear A,D,H afterward',
   'constructor':'I(a,b)=k*Cantor(a,b); membership/equality/universal tags1/3/2 unchanged',
   'scope':'Exact formula construction; not a semantic truth evaluator.'}

def build(which,out):
 assert __debug__,'Run without -O'
 c.raw_nodes=BASE_NODES
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 grammar=c.read_grammar(HERE/'inputs/pa194.grammar.json')
 oldsites,oldins,_=c.source(grammar);assert len(oldsites)==3673
 raw,index,shape=c.build(grammar);assert len(raw)==402 and len(shape)==67
 oldfolds=json.loads((HERE/'inputs/pa194.folds.json').read_text())
 primary,_=s.apply_folds(raw,oldfolds)
 assert sha(s.table_text(primary).encode())=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
 k=4 if which=='4R'else int(which)
 ns=BASE_NODES();triple=(INC,'node60')
 if which=='4R':
  ns['node61']=(INC,(INC,'node60'))
  raw.update({(190,0):(0,True,61),(190,1):(1,True,330)})
 else:
  ns['node61']=(triple,'node60'if k==5 else triple)
  raw.update({(190,0):(0,True,330),(190,1):(1,True,99 if k==5 else 330)})
 raw.update({(330,0):(0,True,61),(330,1):(1,True,99)})
 assert len(raw)==404
 # All eight disjoint folds are checked simultaneously in the final table.
 additional=[[41,99,[[0,False,30],[1,False,2035]]]]
 allfolds=oldfolds+additional
 child,aliases=s.apply_folds(raw,allfolds)
 local=s.check_local_folds(raw,child,aliases,allfolds);assert len(local['cases'])==32
 assert all(child[q,bit]==primary[q,bit]for q in c.BOXSTATES for bit in(0,1))
 c.raw_nodes=lambda:ns
 sites,ins,contracts=c.source(grammar)
 binding=source_binding(grammar,oldsites,oldins,ns,sites,ins,k)
 if k==4:assert ins==oldins
 free=emitter_audit(grammar,k)
 valid=c.validate(child,contracts);assert valid['ok'],valid
 blank=s.startup(child,sites[25][0]);assert blank['steps']==58320
 dense,labels=s.dense_table(child,194)
 dense_text=s.table_text(dense);assert sha(dense_text.encode())==EXPECTED[which]
 out.mkdir(parents=True,exist_ok=True)
 for name,data in [('machine.native.tm',s.table_text(child)),('machine.tm',dense_text),('unfolded202.native.tm',s.table_text(raw))]:(out/name).write_text(data)
 for name,data in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
   ('instructions.json',ins),('folds.json',allfolds),('local_fold_cases.json',local),('source_binding.json',binding),('emitter_audit.json',free),('nodes.json',ns)]:write_json(out/name,data)
 receipt={'family':which,'radix':k,'working_states':194,'rows':388,'unfolded_states':202,
  'fixed_controls':135,'AX_readers':67,'simultaneous_folds':8,'local_cases':32,
  'source_sites':len(sites),'source_contracts':len(contracts),'source_binding':{a:v for a,v in binding.items()if a!='bodies'},
  'source_instruction_counts':dict(Counter(x[0]for x in ins)),
  'emitter_audit':free,'symbolic_validation':valid,'startup':blank,
  'native_sha256':sha(s.table_text(child).encode()),'dense_sha256':sha(dense_text.encode()),
  'source_maximum_path':max(len(p)for p,op,a in sites),'arithmetic_box_rows_unchanged':True,
  'scope':'Finite construction, exact source binding, universal symbolic contracts and exact startup; logical PA calibration is a separate mathematical proof; not an end-to-end proof-assistant theorem.'}
 write_json(out/'receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
 c.raw_nodes=BASE_NODES
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--family',choices=['4R','5','6'],action='append');p.add_argument('--output',type=Path,default=HERE/'generated');a=p.parse_args()
 for family in a.family or['4R','5','6']:build(family,a.output/family)
