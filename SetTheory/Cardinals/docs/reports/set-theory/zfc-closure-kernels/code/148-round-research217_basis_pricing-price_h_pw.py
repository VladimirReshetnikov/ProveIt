"""Owned bounded H/PW source pricing, using only literal inputs and owned helpers.
No supplied program is executed. Allocator output is explicitly provisional.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import sys,json,time,hashlib,itertools
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_encoding'));import price_sources as P
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
compact=lambda x:(json.dumps(x,separators=(',',':'))+'\n').encode()
H=lambda b:hashlib.sha256(b).hexdigest()
def dump(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
ss=json.load(open(ROOT/'latest218_baseline/candidate-k218/sites218.json'));old=P.tree(ss);T=A.R.table(ROOT/'latest218_baseline/candidate-k218/k218.native.tm')
data=json.load(open(ROOT/'research218_source/ks_edit_inputs.json'));macros={k:freeze(v['tree'])for k,v in data['macros'].items()}
assert len(P.nodes(old))+len({tuple(s[1:])for s in ss})==205
@lru_cache(None)
def length(t):return 1 if P.leaf(t)else length(t[0])+length(t[1])
def serial(xs):
 t=xs[-1]
 for x in reversed(xs[:-1]):t=(x,t)
 return t
U=A.at(old,'11010010011001100');assert length(U)==11 and A.boundary(U)==(0,0,False)
assert [s[1:]for s in A.flatten(U)]==[s[1:]for s in ss[180:191]]
clear6=(('CD',6),('CC',1));discard=(U,clear6);assert A.boundary(discard)==(0,0,False)

def cfg_exit(t):
 out=[];N=length(t)
 def walk(n,start,breaks,continues):
  if P.leaf(n):
   op,k=n;after=start+1
   target=lambda stack,k:stack[-k]if len(stack)>=k else(N if stack is breaks else 0)
   edges=[]if op=='CH'else[target(continues,k)]if op=='CC'else[target(breaks,k)]if op=='CB'else[target(breaks,1),after]if op=='CD'else[after]
   assert len(out)==start;out.append((op,k,edges));return
  end=start+length(n);mid=start+length(n[0]);walk(n[0],start,breaks+[end],continues);walk(n[1],mid,breaks,continues+[start])
 walk(t,0,[],[]);return out

def parser_contract():
 G=cfg_exit(discard);samples=[]
 for a in range(17):
  for b in range(17):
   v=(a+b)*(a+b+1)//2+b;reg=[31,37,41,43,47,53,0,0,v];before=reg.copy();pc=0;steps=0
   while pc<len(G):
    op,k,edges=G[pc]
    if op=='CI':reg[k]+=1;pc=edges[0]
    elif op=='CD':positive=reg[k]>0;reg[k]-=positive;pc=edges[int(positive)]
    else:assert op in('CB','CC');pc=edges[0]
    steps+=1;assert steps<100000
   expected=before.copy();expected[8]=b;assert reg==expected
   samples.append(dict(u=a,tail=b,steps=steps))
 proof=dict(status='EXACT_DISCARD_READER_CONTRACT_WITH_ALL_NATURAL_INVARIANT',input='R8=P(u,tail), R6=R7=0; arbitrary R0..R5 including prior topR1 and stackR2',output='R8=tail; R6=R7=0; every R0..R5 unchanged',literal_unpair_interval=[180,191],literal_unpair_leaves=11,discard_total_leaves=13,discard_ast=discard,loop_invariant='After i decrement iterations: R8=N-i and P(R6,R7)=i. A step sends (a,b) to (a-1,b+1) when a>0, or (0,b) to (b+1,0) when a=0; both increase Cantor P by1. R8 decreases to0. The final transfer moves R7 toR8 and clearsR7; Clear6 then clears the unused first component. Only R6,R7,R8 are accessed.',termination='Exactly N main-loop iterations; each transfer or clear decreases its tested register. Therefore all natural inputs terminate.',checked_cases=len(samples),samples=samples,scope='Ordinary loop-invariant proof plus finite corroboration, not binary TM primitive certification.')
 dump('DISCARD_READER_CONTRACT.json',proof)
parser_contract()

I=lambda a,b:('I',a,b)
def postfix(f):return[f]if isinstance(f,str)else postfix(f[1])+postfix(f[2])+['I']
def decode(word):
 stack=[]
 for x in word:
  if x!='I':stack.append(x)
  else:b,a=stack.pop(),stack.pop();stack.append(I(a,b))
 assert len(stack)==1;return stack[0]
def constructors(f):return set()if isinstance(f,str)else{f}|constructors(f[1])|constructors(f[2])
def metrics(t):
 s=A.flatten(t);return dict(source_dag_nodes=len(P.nodes(t))+len({tuple(x[1:])for x in s}),internal_subtrees=len(P.nodes(t)),primitive_leaves=len(s),maximum_depth=max(len(x[0])for x in s),maximum_zero_run=max(len(z)for p,o,k in s for z in p.split('1')))

def splice(new):
 lo,hi=135,486;removed=[];inserted=[]
 def walk(n,i=0):
  j=i+length(n)
  if j<=lo or hi<=i:return n
  if lo<=i and j<=hi:
   assert A.boundary(n)==(0,0,False),(i,j,A.boundary(n));removed.append([i,j])
   if i==lo:inserted.append(i);return new
   return None
  assert not P.leaf(n);a=walk(n[0],i);b=walk(n[1],i+length(n[0]));return b if a is None else a if b is None else(a,b)
 result=walk(old);assert inserted==[135]and sum(b-a for a,b in removed)==351;return result,removed
oldG=A.continuation_cfg(old);assert oldG==A.address_cfg(ss)
def verify_source(t,inserted):
 ns=A.flatten(t);assert [x[1:]for x in ns]==[x[1:]for x in ss[:135]]+[x[1:]for x in A.flatten(inserted)]+[x[1:]for x in ss[486:]]
 G=A.continuation_cfg(t);assert G==A.address_cfg(ns)
 delta=len(ns)-len(ss)
 def transport(j):
  assert not 135<j<486,('outside edge enters obsolete interior',j)
  return j if j<=135 else j+delta
 for i,row in enumerate(oldG):
  if 135<=i<486:continue
  j=i if i<135 else i+delta
  assert G[j]==[row[0],row[1],[transport(k)for k in row[2]]],(i,j,row,G[j])
 return ns

def main():
 inventory=json.load(open(OUT/'INVENTORY.json'));original_allocation=P.allocation;cached=original_allocation(T,old)
 P.allocation=lambda table,tree:cached if table is T and tree is old else original_allocation(table,tree)
 results=[];started=time.monotonic();status='COMPLETE';interior=json.load(open(ROOT/'research217_source_plateaus/INTERIOR_HELPER_ROWS.json'))['rows'];helper={(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)}
 try:
  for idx,item in enumerate(inventory['variants']):
   if time.monotonic()-started>=10:status='CAP_UNKNOWN';break
   p,q,r=item['H_roles'];h=I(I(p,q),I(I(q,r),I(p,r)));pw=I(I(I(q,r),q),I(p,q));forms=[h,pw]if item['order']=='H_PW'else[pw,h]
   assert len(constructors(h)|constructors(pw))==7
   words=[postfix(f)for f in forms];assert[decode(w)for w in words]==forms
   blocks=[discard]+[macros[x]for w in words for x in w];assert all(A.boundary(x)==(0,0,False)for x in blocks)
   inserted=serial(blocks);new,removed=splice(inserted);ns=verify_source(new,inserted);source=compact(ns);stem=f'h_pw_{idx:02d}'
   (OUT/(stem+'.sites.json')).write_bytes(source)
   result=dict(index=idx,**item,formula_constructor_dag_nodes=7,postfix=words,source_sha256=H(source),source_file=stem+'.sites.json',metrics=metrics(new),inserted_primitive_leaves=length(inserted),removed_closed_intervals=removed,unchanged_outer_cfg=True,stack_contract='For prior topT and older stackS, H thenPW ends with topPW and stackS,T,H; reverse order ends with topH and stackS,T,PW. Fourth field is consumed and discarded before either row; a,b,c and all prior items preserved.',physical_status='NOT_CERTIFIED')
   try:
    out,receipt=P.compile(T,old,new);raw=P.M.enc(out);(OUT/(stem+'.provisional.native.tm')).write_bytes(raw)
    changed={(x['state'],x['read'])for x in receipt['changes']}
    result['allocator']=dict(**receipt,native_sha256=H(raw),file=stem+'.provisional.native.tm',changed_protected_helper_rows=[list(x)for x in sorted(changed&helper)],changed_interior_decoder_helper_rows=[list(x)for x in sorted(changed)if f'{x[0]}/{x[1]}'in interior],warning='Actual output of owned provisional allocator, not a certified physical construction. Extinct-state reuse may overwrite primitive, bootstrap or selector obligations; source-prefix binding alone is insufficient.')
   except Exception as e:result['allocator']=dict(status='ALLOCATION_OR_PREFIX_BINDING_FAILED',error=repr(e))
   results.append(result);print(json.dumps(dict(index=idx,metrics=result['metrics'],allocator_states=result['allocator'].get('states'),allocator_error=result['allocator'].get('error'))),flush=True)
 finally:P.allocation=original_allocation
 report=dict(status=status,variants_attempted=len(results),inventoried_variants=len(inventory['variants']),baseline_metrics=metrics(old),baseline_physical_states=len(T)//2,source_histogram=dict(Counter(r['metrics']['source_dag_nodes']for r in results)),allocator_histogram=dict(Counter(str(r['allocator'].get('states','FAILED'))for r in results)),seconds=time.monotonic()-started,scope='Parser-consumption-preserving H/PW source pricing and actual provisional allocator outputs. No runtime, startup, physical count certificate or completed proof-enumerator equivalence.',results=results)
 dump('PARSER_PRESERVING_PRICES.json',report);print(json.dumps({k:v for k,v in report.items()if k!='results'},indent=2))
if __name__=='__main__':main()
