#!/usr/bin/env python3
"""Rebuild two 194-state marker-separated compositions and exact finite certificates.

Python 3.10+, standard library, no network. The four local checks cover arbitrary
complete binary tapes, using incoming-edge history. They are not bounded samples
of register values and do not purport to be a Lean kernel proof.
The marker/selector separation is the existing PA194B construction; this package
newly composes it with the pinned LCG and LCGS parents, with credited dependencies.
"""
from pathlib import Path
import argparse, hashlib, json
HERE=Path(__file__).resolve().parent
START,HALT,MARKER,SELECTOR,OLD_READER,KEEP=74,254,400,51,301,88

def sha(b):return hashlib.sha256(b).hexdigest()
def table(rows):return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for(q,b),(w,d,n) in sorted(rows.items()))
def read(path):
 rows={}
 for ln in path.read_text().splitlines():
  if not ln.strip() or ln.lstrip().startswith('#'):continue
  q,b,w,d,n=ln.split();q,b,w,n=map(int,(q,b,w,n))
  assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('R','L')
  rows[q,b]=w,d=='R',n
 states={q for q,b in rows}
 assert len(states)==194 and len(rows)==388
 assert all((q,b)in rows for q in states for b in(0,1))
 assert {n for w,d,n in rows.values()}-states=={HALT}
 return rows

def rename(q):return MARKER if q==SELECTOR else KEEP if q==OLD_READER else q

def construct(old):
 assert MARKER not in {q for q,b in old}
 assert old[SELECTOR,0]==(0,True,16) and old[SELECTOR,1]==(1,True,SELECTOR)
 assert old[OLD_READER,0]==(0,True,45) and old[OLD_READER,1]==(1,True,103)
 assert old[KEEP,0]==(0,True,122) and old[KEEP,1]==(1,True,103)
 rows={(rename(q),b):(w,d,rename(n))for(q,b),(w,d,n)in old.items()if q!=OLD_READER}
 rows[KEEP,0]=0,False,SELECTOR
 rows[SELECTOR,0]=0,True,122
 rows[SELECTOR,1]=1,True,SELECTOR
 assert len(rows)==388
 incoming={q:[list((s,b,w,d))for(s,b),(w,d,n)in old.items()if n==q]for q in(OLD_READER,KEEP)}
 assert incoming[OLD_READER] and incoming[KEEP]
 assert {(w,d)for s,b,w,d in incoming[OLD_READER]}=={(0,True)}
 assert {(w,d)for s,b,w,d in incoming[KEEP]}=={(1,True)}
 assert START not in (OLD_READER,KEEP,SELECTOR,MARKER)
 # All unaffected old rows simulate in one step under the exact renaming.
 unaffected=[(q,b)for(q,b)in old if q not in(OLD_READER,KEEP)]
 assert all(rows[rename(q),b]==(w,d,rename(n))for(q,b)in unaffected for w,d,n in [old[q,b]])
 cases=[]
 for src,history in [(OLD_READER,0),(KEEP,1)]:
  for bit in(0,1):
   q,p,t=KEEP,0,{-1:history,0:bit}
   w,d,n=old[src,bit];goal=(rename(n),1 if d else-1,{-1:history,0:w})
   trace=[]
   for k in range(1,6):
    assert p in(-1,0)
    act=rows[q,t[p]];trace.append([q,p,t[-1],t[0],list(act)])
    w,d,q=act;t[p]=w;p+=1 if d else-1
    assert q!=HALT
    if(q,p,t)==goal:break
   else:raise AssertionError(('local certificate',src,bit))
   cases.append(dict(parent_state=src,left_bit=history,read=bit,duration=k,trace=trace,exit=[q,p,t[-1],t[0]]))
 assert [c['duration']for c in cases]==[5,1,3,1]
 return rows,dict(incoming=incoming,cases=cases,unchanged_old_rows=len(unaffected),all_unchanged_rows_checked=True)

def dense(rows):
 states={q for q,b in rows};assert len(states)==194 and HALT not in states
 order=[START];index={START:0}
 for q in order:
  for b in(0,1):
   n=rows[q,b][2]
   if n!=HALT and n not in index:index[n]=len(order);order.append(n)
 assert len(order)==194 and set(order)==states
 return {(index[q],b):(w,d,194 if n==HALT else index[n])for(q,b),(w,d,n)in rows.items()},order+[HALT]

def exact_startup(old,rows,metadata):
 q,p,t=START,0,set();oq,op,ot=START,0,set();micro=0;fold_counts={f'{s}/{b}':0 for s in(OLD_READER,KEEP)for b in(0,1)}
 for oldtime in range(metadata['parent_startup_steps']):
  key=f'{oq}/{int(op in ot)}'
  if key in fold_counts:fold_counts[key]+=1
  w,d,oq=old[oq,int(op in ot)];(ot.add if w else ot.discard)(op);op+=1 if d else-1
  assert oq!=HALT
  for j in range(1,6):
   w,d,q=rows[q,int(p in t)];(t.add if w else t.discard)(p);p+=1 if d else-1;micro+=1
   if(q,p,t)==(rename(oq),op,ot):break
  else:raise AssertionError(('startup simulation',oldtime))
 # The full canonical frame, including all blank exterior, is checked.
 want_head=-2;gap=48
 want={want_head-1,want_head+gap}
 want.update(want_head+i for i,b in enumerate(metadata['site25_path'])if b=='1')
 pos=want_head+gap+1;physical=[0,0,0,0,0,0,2,0,0]+[1]*26
 for v in physical:
  pos+=1;want.update(range(pos,pos+v+1));pos+=v+1
 assert(oq,op,ot)==(84,want_head,want)
 assert micro==metadata['child_startup_steps']
 return dict(parent_steps=metadata['parent_startup_steps'],child_steps=micro,state=q,head=p,
             source_site=25,path=metadata['site25_path'],gap=gap,physical_register_file=physical,
             ones=sorted(t),complete_tape_equality=True,fold_counts=fold_counts,
             every_parent_step_relationally_checked=True)

def build(out):
 assert __debug__,'Run without Python -O.'
 manifests=json.loads((HERE/'inputs/metadata.json').read_text())
 receipts=[]
 for meta in manifests:
  oldfile=HERE/'inputs'/f"{meta['parent']}.native.tm"
  assert sha(oldfile.read_bytes())==meta['parent_native_sha256']
  old=read(oldfile);rows,local=construct(old);dt,labels=dense(rows)
  assert sha(table(dt).encode())==meta['expected_dense_sha256']
  startup=exact_startup(old,rows,meta)
  dest=out/meta['child'];dest.mkdir(parents=True,exist_ok=True)
  receipt=dict(name=meta['child'],parent=meta['parent'],working_states=194,rows=388,
               start=0,halt=194,native_start=START,native_halt=HALT,
               parent_native_sha256=meta['parent_native_sha256'],
               native_sha256=sha(table(rows).encode()),dense_sha256=sha(table(dt).encode()),
               local=local,startup=startup,
               theorem='H_parent(t) implies H_child(5*t); H_child(t) implies H_parent(t).',
               status='ordinary mathematical relative proof with exact executable local certificate; no new Lean kernel theorem')
  for name,data in [('machine.native.tm',table(rows)),('machine.tm',table(dt)),('labels.json',json.dumps(labels,indent=2)+'\n'),('receipt.json',json.dumps(receipt,indent=2)+'\n')]:
   (dest/name).write_text(data)
  receipts.append(receipt)
  print(meta['child'],receipt['dense_sha256'],startup['child_steps'],flush=True)
 (out/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
 return receipts

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'machines');args=ap.parse_args();build(args.output)
