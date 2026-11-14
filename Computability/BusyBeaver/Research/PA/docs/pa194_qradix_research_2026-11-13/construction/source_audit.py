"""Adapted radix-family source binding and exact free-algebra emitter audit.
The Q variant exchanges the two curried premises of the sixth head.
See NOTICE.txt and licenses for upstream attribution.
"""
from pathlib import Path
import compiler as c
INC=('leaf','inc',1)
BASE_NODES=c.raw_nodes
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
   Ex(D,E(H,D)),I(U(D,I(A,H)),I(U(D,A),U(D,H)))]
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

