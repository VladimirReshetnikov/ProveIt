#!/usr/bin/env python3
"""Bounded independent interpreter evidence plus authenticated primary provenance."""
import argparse,hashlib,json,types
from collections import Counter,defaultdict
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'source':'836c86ce4aff428750aab5af9372f1ba9c85e0c10618293ddb74394f0b348170','receipt':'fdc5945dab4f42164694c01afc85ce670a99089e61f146504c315e0107ba9551','note':'0082453baf2b43e7a8fdc48f6a380aefbd12a78bba015c2839d867ac77071a5e','paper':'81677dd609d5b2c111c83fc5768382dbc14b54b1bf212a0b3fe828aca1b6c999'}
PRIMES=(2,3,5,7,11,13,17)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def syntax(rows,k,entry,exits,reverse=False):
 assert len(rows)==len({tuple(r) for r in rows})
 for s,i,op,t in rows:
  assert type(s)is str and type(t)is str and type(i)is int and 0<=i<k
  assert op in ('+','-','Z','P','0')
 for col in (0,3) if reverse else (0,):
  groups=defaultdict(list)
  for r in rows:groups[r[col]].append(r)
  for rs in groups.values():
   assert len(rs)==1 or len(rs)==2 and rs[0][1]==rs[1][1] and {r[2] for r in rs}=={'Z','P'}
 assert all(r[3]!=entry and r[0] not in exits for r in rows)
 return len({r[col] for r in rows for col in (0,3)})

def execute(rows,entry,values,exits,boundaries=()):
 table=defaultdict(list)
 for r in rows:table[r[0]].append(r[1:])
 c=list(values);q=entry;trace=[];steps=0
 while True:
  assert all(type(n)is int and n>=0 for n in c)
  if q in boundaries:trace.append((q,tuple(c)))
  if q in exits:return True,q,c,steps,trace
  enabled=[]
  for i,op,t in table[q]:
   if op in ('+','0') or op in ('-','P') and c[i]>0 or op=='Z' and c[i]==0:enabled.append((i,op,t))
  assert len(enabled)<=1
  if not enabled:return False,q,c,steps,trace
  i,op,q=enabled[0]
  if op=='+':c[i]+=1
  if op=='-':c[i]-=1
  steps+=1
  assert steps<1000000

def invert(rows):
 ops={'+':'-','-':'+','0':'0','Z':'Z','P':'P'}
 return [[t,i,ops[op],s] for s,i,op,t in rows]

def primecode(c):
 n=1
 for p,k in zip(PRIMES,c):n*=p**k
 return n

def run(source,receipt,note,paper):
 for key,path in [('source',source),('receipt',receipt),('note',note),('paper',paper)]:assert sha(path.read_bytes())==PINS[key]
 saved=json.loads(receipt.read_text());assert saved['source_sha256']==PINS['source']
 m=types.ModuleType('_authenticated_prime_macro_emitter');m.__file__=str(source)
 exec(compile(source.read_bytes(),str(source),'exec'),m.__dict__)
 count=Counter();macros=[]
 # Emit actual source macros; neither author interpreter nor verify is used.
 for i,p in enumerate(PRIMES[:5]):
  for kind in ('+','-','Z','P','both','0'):
   raw=[['in',i,'Z','zero'],['in',i,'P','positive']] if kind=='both' else [['in',i,kind,'done']]
   ends={'zero','positive'} if kind=='both' else {'done'}
   rows=m.prime_compile(i+1,raw,'in',ends)
   states=syntax(rows,2,'in',ends,True);count['separated_primitive_tables']+=1
   if kind in ('+','-'):assert len(rows)==p+10
   for n in (1,p,p*p,p*p+1,65,67,71,79,83):
    got,q,v,steps,_=execute(rows,'in',[n,0],ends)
    ok=kind not in ('-','Z','P') or (n%p!=0 if kind=='Z' else n%p==0)
    assert got==ok
    if got:
     want=n*p if kind=='+' else n//p if kind=='-' else n
     assert v==[want,0]
     if kind=='both':assert q==('positive' if n%p==0 else 'zero')
     back=execute(invert(rows),q,v,{'in'})
     assert back[:4]==(True,'in',[n,0],steps)
     count['primitive_inverse_runs']+=1
    count['primitive_forward_cases']+=1
   macros.append({'prime':p,'kind':kind,'states':states,'rows':len(rows),'rows_sha256':sha(json.dumps(rows,separators=(',',':')).encode())})
 assert macros==[{'prime':d['prime'],'kind':d['kind'],'states':d['states'],'rows':d['instructions'],'rows_sha256':d['rows_sha256']} for d in saved['prime_macros']]
 # Independent literal seven-instruction primary example, not receipt's copy.
 source_rows=[['q0',1,'Z','q1'],['q1',0,'Z','halt'],['q1',0,'P','q2'],['q2',0,'-','q3'],['q3',1,'+','q4'],['q4',2,'+','q5'],['q5',1,'P','q1']]
 compiled=m.prime_compile(3,source_rows,'q0',{'halt'})
 assert len(compiled)==93;syntax(compiled,2,'q0',{'halt'},True)
 labels={r[j] for r in source_rows for j in (0,3)};boundary_examples=[]
 for n in range(4):
  original=execute(source_rows,'q0',[n,0,0],{'halt'},labels)
  encoded=execute(compiled,'q0',[2**n,0],{'halt'},labels)
  assert original[0] and encoded[0] and original[2]==[0,n,n] and encoded[2]==[15**n,0]
  wanted=[(q,(primecode(c),0)) for q,c in original[4]]
  assert encoded[4]==wanted
  count['complete_encoded_examples']+=1;count['exact_original_state_boundaries']+=len(wanted)
  boundary_examples.append({'n':n,'boundaries':len(wanted),'microsteps':encoded[3]})
 # Verify the actual divide prefix, with unrelated nonzero program input.
 div=m.divider(96,0,2);assert len(div)==202 and syntax(div,5,'entry',{'done'},True)==201
 for n in (0,1,95,96,97,191,192,193,479,480,481):
  got,q,v,steps,_=execute(div,'entry',[n,23,0,0,0],{'done'})
  assert got==(n%96==0)
  if got:
   assert v==[n//96,23,0,0,0] and steps==198*(n//96)+4
   assert execute(invert(div),'done',v,{'entry'})[:3]==(True,'entry',[n,23,0,0,0])
   count['divider_inverse_cases']+=1
  count['divider_boundary_cases']+=1
 for base in (3,5):
  unary=m.unary_loader(base);syntax(unary,3,'entry',{'done'})
  paired=m.paired_unary_loader(base);syntax(paired,5,'entry',{'done'})
  for x in range(4):
   a=execute(unary,'entry',[x,0,0],{'done'});assert a[0] and a[2]==[0,sum(base**j for j in range(x)),0]
   count['unary_input_cases']+=1
   for e in range(4):
    first=execute(div,'entry',[96*x,e,0,0,0],{'done'})
    assert first[0] and first[2]==[x,e,0,0,0]
    last=execute(paired,'entry',first[2],{'done'})
    assert last[0] and last[2][:3]==[0,0,0] and last[2][4]==0
    actual=[];z=last[2][3]
    while z:z,d=divmod(z,base);actual.append(d)
    assert actual==[1]*x+[2]+[1]*e
    count['composed_paired_loader_cases']+=1
  # Boundary checks for actual stack macros, including blank push and zero pop.
  for digit in range(base):
   rows=[['entry',0,'0','push']]+m.push_rows(base,digit,0,1,'push','done','audit')
   syntax(rows,2,'entry',{'done'})
   for n in (0,1,base-1,base,base+1):
    got=execute(rows,'entry',[n,0],{'done'});assert got[0] and got[2]==[base*n+digit,0]
    count['stack_push_boundary_cases']+=1
  rows,exits=m.pop_rows(base,0,1,'entry','audit');syntax(rows,2,'entry',set(exits))
  for n in (0,1,base-1,base,base+1,base**2-1,base**2):
   got=execute(rows,'entry',[n,0],set(exits));assert got[0] and got[1]==exits[n%base] and got[2]==[n//base,0]
   count['stack_pop_boundary_cases']+=1
 # Exact prime-code interface, without constructing doubly exponential mass.
 for x in (1,2,5):
  for e in (0,1,7):
   inner=2**(96*x);C=3**e;valuation=96*C*inner
   assert valuation//96==primecode([96*x,e,0,0,0,0,0])
   count['nested_input_recipe_cases']+=1
 return {'status':'PASS_INDEPENDENT_PRIME_POWER_INPUT_REVIEW','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'counts':dict(count),'prime_macro_tables':macros,'encoded_examples':boundary_examples,'primary_scope':{'theorem3_1_printed_page':308,'theorem4_1_printed_page':313,'primitive_macro_pages':[314,315,316],'source_of_general_theorem':'Independent written proof read plus primary theorem and source-boundary invariants, not finite execution.'},'execution_scope':'Actual authenticated author macro emitters only; all interpretation, syntax, inverse, prime encodings and input-word expectations are independent. No author verify/run, universal table, outer huge mass or native Pell witnesses.'}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('source','receipt','note','paper'):p.add_argument('--'+key,type=Path,required=True)
 p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 r=run(a.source,a.receipt,a.note,a.paper)
 if a.expect:assert exact(r,json.loads(a.expect.read_text()))
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']}))
if __name__=='__main__':main()
