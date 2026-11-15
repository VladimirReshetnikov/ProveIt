#!/usr/bin/env python3
"""Apply and certify the inherited two guarded 3-to-1 shortcuts.

The acceleration method is credited to the supplied AX11GH/GHS packet.
This applies it to the newly constructed AX11GDH table. Standard library only.
The global iPRA simulation proof is in proof/acceleration.tex.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,shutil,sys
START,HALT=74,254
PARENT_SHA='2eb51a94fd0c47d5eae802b5d9add156f23f05fa243f6157432cc6c03ffc6221'
EXPECTED_SHA='495be0f21e9aff11e35002a8909d94da1c0eaee92be37263db79f22f6c5567df'
PATCH={(26,1):(1,'R',91),(101,0):(0,'R',17)}
def require(x,msg):
 if not x:raise AssertionError(msg)
def read(path):
 r={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  require((q,b)not in r,'duplicate transition');require(b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
  r[q,b]=(w,d,n)
 return r
def text(r):return ''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(r.items()))
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def step(rows,state,head,ones):
 if state==HALT:return state,head,ones
 w,d,n=rows[state,int(head in ones)]
 (ones.add if w else ones.discard)(head)
 return n,head+(1 if d=='R'else-1),ones
def dense(rows):
 controls={q for q,b in rows};require(len(controls)==194 and len(rows)==388,'state count')
 require(all((q,b)in rows for q in controls for b in(0,1)),'total table')
 require({n for w,d,n in rows.values()}-controls=={HALT},'halt labels')
 labels=[START];idx={START:0}
 for q in labels:
  for b in(0,1):
   n=rows[q,b][2]
   if n!=HALT and n not in idx:idx[n]=len(labels);labels.append(n)
 require(len(labels)==194,'not all controls graph reachable')
 return {(idx[q],b):(w,d,194 if n==HALT else idx[n])for(q,b),(w,d,n)in rows.items()},labels+[HALT]
def build(parent,out):
 require(not sys.flags.optimize,'Run without -O')
 require(hashlib.sha256((parent/'machine.native.tm').read_bytes()).hexdigest()==PARENT_SHA,'exact parent binding')
 old=read(parent/'machine.native.tm');new=dict(old)
 require(old[26,1]==(1,'R',42)and old[101,0]==(0,'L',26),'parent shortcut rows')
 require(old[42,0]==(0,'R',13)and old[13,0]==(0,'L',91),'first path')
 require(old[26,0]==(0,'R',194)and old[194,0]==(0,'R',17),'second path')
 incoming={q:[(s,b,*v)for(s,b),v in sorted(old.items())if v[2]==q]for q in(11,26,101)}
 require(incoming[101]==[(96,0,0,'R',101)],'I101 predecessor')
 require(incoming[26]==[(11,0,0,'L',26),(101,0,0,'L',26)],'I26 predecessors')
 require(all(w==0 for s,b,w,d,n in incoming[11]),'I11 predecessors write zero')
 require(START not in(11,26,101),'initial invariant')
 new.update(PATCH);cases=[]
 for q,b in PATCH:
  for bits in itertools.product(range(2),repeat=5):
   t={i-2 for i,v in enumerate(bits)if v}
   if (0 in t)!=bool(b):continue
   if q==26 and (1 in t or 2 in t):continue
   if q==101 and -1 in t:continue
   a=(q,0,set(t));f=step(new,q,0,set(t));trace=[]
   for _ in range(3):
    a=step(old,*a);require(a[0]!=HALT,'shortcut hides halt');trace.append([a[0],a[1],sorted(a[2])])
   require(a==f,'local whole-tape identity')
   cases.append(dict(state=q,window=bits,parent_trace=trace,child=[f[0],f[1],sorted(f[2])]))
 require(len(cases)==12,'case count')
 seed=(json.loads((parent/'startup.json').read_text()) if (parent/'startup.json').exists()
       else json.loads((parent/'receipt.json').read_text())['startup'])
 expected=(seed['state'],seed['head'],set(seed['one_cells']))
 a=(START,0,set());f=(START,0,set());sigma=0;uses={str(k):0 for k in PATCH}
 for k in range(1,100001):
  edge=(f[0],int(f[1]in f[2]));duration=3 if edge in PATCH else 1
  if duration==3:uses[str(edge)]+=1
  f=step(new,*f)
  for _ in range(duration):a=step(old,*a)
  sigma+=duration
  require(a==f,'expanded-clock identity during startup')
  require(f[0]!=HALT,'unexpected blank startup halt')
  if f==expected:break
 else:raise AssertionError('seed frame not reached')
 require(sigma==seed['steps'],'parent startup clock')
 den,labels=dense(new);require(hashlib.sha256(text(den).encode()).hexdigest()==EXPECTED_SHA,'exact output binding')
 out.mkdir(parents=True,exist_ok=True)
 for name,rows in [('machine.native.tm',new),('machine.tm',den)]: (out/name).write_text(text(rows))
 dump(out/'labels.json',labels)
 for name in ['nodes.json','grammar.json','folds.json','instructions.json','sites.json']:
  shutil.copyfile(parent/name,out/name)
 startup={**seed,'steps':k};dump(out/'startup.json',startup)
 receipt=dict(status='PASS',name='PA194AX11GDHF',states=194,transitions=388,source_graph_unchanged=True,
  parent_dense_sha256=hashlib.sha256((parent/'machine.tm').read_bytes()).hexdigest(),
  dense_sha256=hashlib.sha256(text(den).encode()).hexdigest(),native_sha256=hashlib.sha256(text(new).encode()).hexdigest(),
  native_edits=[[q,b,list(old[q,b]),list(new[q,b])]for q,b in PATCH],
  incoming_invariant_rows=incoming,local_cases=len(cases),startup_steps=k,parent_startup_steps=sigma,
  startup_shortcut_uses=uses,relative_clock='H_parent(t) -> H_child(t); H_child(t) -> H_parent(3*t)',
  proof_scope='Exact local certificates plus the written quantifier-free induction in proof/acceleration.tex; no proof-assistant build.')
 dump(out/'acceleration_receipt.json',receipt);dump(out/'acceleration_cases.json',cases)
 dump(out/'receipt.json',dict(name='PA194AX11GDHF',states=194,startup=startup,sha256=EXPECTED_SHA))
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 print(json.dumps(build(a.parent,a.output),indent=2))
