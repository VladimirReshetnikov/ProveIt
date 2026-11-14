#!/usr/bin/env python3
"""Build the 196-state immediate-MP-halt prototype; not a sub-194 result.

Inherited compiler/runtime are attributed in licenses/ and PROVENANCE.json.
Run Python without -O. Standard library only. The executable certificates
are not a new end-to-end proof-assistant theorem.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'construction'))
import compiler as c
PHYSICAL=[6,2,0,4,3,7,8,5,1]
START,HALT=74,254
def sha(b):return hashlib.sha256(b).hexdigest()
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def read(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip():continue
  q,b,w,m,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert b in(0,1) and w in(0,1) and m in('L','R') and(q,b)not in rows
  rows[q,b]=(w,m=='R',n)
 return rows
def table(rows):return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
def dump(path,x):path.write_text(json.dumps(x,indent=2)+'\n')
def dense(rows):
 states={q for q,b in rows};assert len(states)==196 and len(rows)==392
 assert HALT not in states and {n for w,d,n in rows.values()}-states=={HALT}
 order=[START];index={START:0}
 for q in order:
  for b in(0,1):
   n=rows[q,b][2]
   if n!=HALT and n not in index:index[n]=len(order);order.append(n)
 assert set(order)==states
 return {(index[q],b):(w,d,196 if n==HALT else index[n])for(q,b),(w,d,n)in rows.items()},order+[HALT]
def startup(rows,path):
 # The measured startup frame is checked by literal equality of the entire tape.
 head=-2;gap=48;file=[0,0,0,0,0,0,2,0,0]+[1]*26
 expected={head-1,head+gap}
 expected.update(head+i for i,b in enumerate(path)if b)
 p=head+gap+1
 for v in file:
  p+=1;expected.update(range(p,p+v+1));p+=v+1
 q,h,ones=START,0,set()
 for step in range(58154):
  assert q!=HALT,('halt during startup',step)
  w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else-1
 assert(q,h,ones)==(84,head,expected)
 return {'steps':58154,'state':q,'head':h,'gap':gap,'source_site':25,
 'physical_file':file,'complete_tape_equality':True,'one_cells':sorted(ones)}
def run_source(code,pc,rs,stop=25,limit=2000000):
 rs=list(rs)
 for steps in range(limit):
  if steps and pc==stop:return pc,rs,steps
  row=code[pc]
  if row[0]=='halt':return 'halt',rs,steps
  if row[0]=='inc':r,n=row[1:];rs[r]+=1;pc=n
  elif row[0]=='dec':r,z,p=row[1:];pc=p if rs[r] else z;rs[r]=max(0,rs[r]-1)
  else:pc=row[1]
 raise AssertionError(('source fuel',pc,rs))
def command_checks(sites,code):
 def pair(a,b):return(a+b)*(a+b+1)//2+b
 def unpair(n):
  a=b=0
  for _ in range(n):a,b=(a-1,b+1) if a else(b+1,0)
  return a,b
 def entry(prefix):return next(i for i,(p,o,a)in enumerate(sites)if p[:len(prefix)]==prefix)
 mp=entry((1,0,1,0,1,0,1,0));shift=entry((1,0,1,1))
 assert (mp,shift)==(3554,3651)
 checks=0
 for t in range(3):
  for d in range(3):
   for x in range(3):
    b=d+x;match=4*pair(t,b)
    for h in sorted({0,1,match,match+1}):
     for w in range(3):
      rs=[17,t,w,0,d,h,0,0,pair(x,2)]
      pc,after,steps=run_source(code,mp,rs)
      expected='halt' if h==match and b==1 else 25
      assert pc==expected,(t,d,x,h,w,pc,expected)
      if pc!='halt':
       want=[17,b if h==match else 0,w,0,0 if h==match else d+x,0,0,0,2]
       assert after==want,(rs,after,want)
      checks+=1
 for t in range(4):
  for h in range(4):
   for w in range(10):
    rs=[17,t,w,0,3,h,0,0,2]
    pc,after,steps=run_source(code,shift,rs)
    hd,tl=unpair(w)
    expected='halt' if t+h==1 else 25
    assert pc==expected,(rs,pc,expected)
    if pc!='halt':
     want=[17,h,tl,0,3,hd,0,0,2]
     assert after==want,(rs,pc,after,want)
    checks+=1
 return {'bounded_command_cases':checks,'mp_source_entry':mp,'shift_source_entry':shift,
 'scope':'Finite cross-check of exact source semantics; universal argument in source_proof.tex.'}

def build(output):
 assert __debug__ and not sys.flags.optimize,'Run without -O.'
 base=read(HERE/'inputs/base.native.tm');assert len(base)==388
 assert sha(table(base).encode())=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
 nodes={k:tup(v)for k,v in json.loads((HERE/'inputs/base_nodes.json').read_text()).items()}
 success=('node51',(('leaf','inc',5),'node7'))
 nodes['node163']=('node6',success)
 c.raw_nodes=lambda:nodes
 grammar=c.read_grammar(HERE/'inputs/grammar.json')
 sites,code,contracts=c.source(grammar)
 edits={(164,1):(1,True,400),
  (400,0):(0,True,130),(400,1):(1,True,401),
  (401,0):(0,True,63),(401,1):(1,True,68)}
 rows=dict(base);rows.update(edits)
 assert all(rows[q,b]==base[q,b]for q in c.BOXSTATES for b in(0,1))
 assert len(sites)==3663 and len(contracts)==4768
 assert code[3634:3651]==[
  ('dec',4,3638,3635),('inc',1,3636),('inc',6,3637),('jump',3634),
  ('inc',5,3639),('dec',5,3643,3640),('dec',6,3642,3641),('jump',3639),
  ('jump',3644),('dec',6,3649,3644),('dec',5,3646,3645),('jump',3644),
  ('dec',6,3648,3647),('jump',3644),('jump',3650),('halt',),('jump',25)]
 assert sites[10]==((0,0,1),'halt',None) and code[10]==('halt',)
 valid=c.validate(rows,contracts);assert valid['ok'],valid
 blank=startup(rows,sites[25][0]);checks=command_checks(sites,code)
 dt,labels=dense(rows)
 output.mkdir(parents=True,exist_ok=True)
 for name,data in [('nodes.json',nodes),('sites.json',[[''.join(map(str,p)),o,a]for p,o,a in sites]),('instructions.json',code),('labels.json',labels)]:dump(output/name,data)
 (output/'machine.native.tm').write_text(table(rows));(output/'machine.tm').write_text(table(dt))
 receipt={'status':'196-state protocol prototype; not a sub-194 construction','working_states':196,
 'rows':392,'source_sites':len(sites),'primitive_outcomes':len(contracts),
 'symbolic_runtime':valid,'startup':blank,'command_checks':checks,
 'native_sha256':sha(table(rows).encode()),'dense_sha256':sha(table(dt).encode()),
 'new_end_to_end_kernel_theorem':False,
 'proof_boundary':'Inherits unchanged arithmetic-block lemmas and PA numerical-calculus calibration; new source controller proof is ordinary mathematics.'}
 dump(output/'receipt.json',receipt);print(json.dumps(receipt,indent=2))
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=HERE/'generated')
 build(p.parse_args().output)
