#!/usr/bin/env python3
"""Independent finite-premise audit for LCG/LCGS split-marker compositions.

Reads only literal tables and label arrays, not the construction's Python code.
The accompanying proof establishes the uniform arithmetic induction from these
finite premises. Startup replay is a separate exact whole-tape check.
"""
import argparse,collections,hashlib,json,pathlib

def sha(raw):return hashlib.sha256(raw).hexdigest()
def parse_table(raw):
 rows={}
 for line in raw.decode('ascii').splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows
  rows[q,b]=(w,d,t)
 states={q for q,b in rows};assert states and len(rows)==2*len(states)
 assert all((q,b) in rows for q in states for b in (0,1))
 halts={t for w,d,t in rows.values()}-states;assert len(halts)==1
 return rows,states,next(iter(halts))
def reachable_count(rows,start):
 states={q for q,b in rows};seen={start};todo=[start]
 for q in todo:
  for b in (0,1):
   t=rows[q,b][2]
   if t in states and t not in seen:seen.add(t);todo.append(t)
 return len(seen)

PARENT_HASHES={
 'PA194LCG':'bdbfb392b408dd729899f07ad38de92b86f5d76bbdb87e7a12e5f1137f3d8047',
 'PA194LCGS':'137359a2ee40b81c994903589b68f34c4d47cb97f8600c86016094f637a4f25a'}
DENSE_HASHES={
 'PA194LCGMS':'a168e6264a3963dec96a5f6f5dffd75d9f45cc4ed4cb31c80f3d2e8f23bcc312',
 'PA194LCGSMS':'cdaa8211a08619263a0dc3cd5a6a3a62a02f506b360d738d20b25975246badf6'}

def step(rows,c):
 q,p,ones=c;w,d,n=rows[q,int(p in ones)];ones=set(ones)
 if w:ones.add(p)
 else:ones.discard(p)
 return n,p+(1 if d=='R' else -1),ones

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--package',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[1]);ap.add_argument('--output',type=pathlib.Path,required=True);a=ap.parse_args();results=[]
 assert __debug__, 'Assertions must be enabled; do not run Python -O.'
 for parent,seed in [('PA194LCG',57870),('PA194LCGS',57712)]:
  src=a.package/'inputs'/(parent+'.native.tm');dst=a.package/'machines'/(parent+'MS');pr=src.read_bytes();nr=(dst/'machine.native.tm').read_bytes();dr=(dst/'machine.tm').read_bytes()
  assert sha(pr)==PARENT_HASHES[parent] and sha(dr)==DENSE_HASHES[parent+'MS']
  old,states,halt=parse_table(pr);new,newstates,newhalt=parse_table(nr);dense,denstates,denhalt=parse_table(dr)
  assert len(states)==len(newstates)==len(denstates)==194 and len(old)==len(new)==len(dense)==388
  assert 400 not in states and {51,88,301}<=states and halt==newhalt==254 and denhalt==194
  assert denstates==set(range(194))
  rename=lambda q:400 if q==51 else 88 if q==301 else q
  assert newstates=={rename(q) for q in states}|{51}
  expected={(rename(q),b):(w,d,rename(t)) for (q,b),(w,d,t) in old.items() if q!=301}
  expected[88,0]=(0,'L',51);expected[51,0]=(0,'R',122);expected[51,1]=(1,'R',51)
  assert new==expected
  incoming={q:sorted((s,b,w,d) for (s,b),(w,d,t) in old.items() if t==q) for q in (301,88)}
  assert incoming[301] and incoming[88]
  assert all(w==0 and d=='R' for s,b,w,d in incoming[301])
  assert all(w==1 and d=='R' for s,b,w,d in incoming[88])
  assert 74 not in (301,88) and halt not in (301,88)
  labels=json.loads((dst/'labels.json').read_text());assert len(labels)==195 and labels[0]==74 and labels[-1]==halt and set(labels[:-1])==newstates and len(set(labels))==195
  for (q,b),(w,d,t) in dense.items():assert new[labels[q],b]==(w,d,labels[t])
  assert reachable_count(dense,0)==194
  cases=[]
  for source,history in ((301,0),(88,1)):
   for bit in (0,1):
    initial={-1:history,0:bit};tape=dict(initial);q=88;p=0;oldw,oldd,oldt=old[source,bit];target=(rename(oldt),1 if oldd=='R' else -1,{-1:history,0:oldw});trace=[]
    for k in range(1,6):
     assert p in (-1,0) and q!=halt
     w,d,n=new[q,tape[p]];trace.append([q,p,tape[p],w,d,n]);tape[p]=w;p+=1 if d=='R' else -1;q=n
     if (q,p,tape)==target:break
    else:raise AssertionError(('local mismatch',source,bit))
    assert k==({(301,0):5,(301,1):1,(88,0):3,(88,1):1}[source,bit])
    cases.append({'parent_state':source,'left_history_bit':history,'scanned_bit':bit,'duration':k,'trace':trace,'endpoint_state':q,'endpoint_relative_head':p})
  # Every non-special transition commutes with the control map, including halt edges.
  for (q,b),(w,d,t) in old.items():
   if q not in (301,88):assert new[rename(q),b]==(w,d,rename(t))
  oldc=(74,0,set());newc=(74,0,set());micro=0;counts=collections.Counter();after=collections.Counter();saved_seed=None
  for t in range(seed+10000):
   oq,op,ot=oldc;ob=int(op in ot)
   counts[oq,ob]+=1
   if t>=seed:after[oq,ob]+=1
   duration={(301,0):5,(301,1):1,(88,0):3,(88,1):1}.get((oq,ob),1)
   oldc=step(old,oldc)
   for _ in range(duration):newc=step(new,newc);micro+=1
   assert newc==(rename(oldc[0]),oldc[1],oldc[2]),(t,oldc,newc)
   assert oldc[0]!=halt
   if t+1==seed:
    assert oldc[0]==84 and oldc[1]==-2
    saved_seed={'parent_steps':seed,'child_steps':micro,'state':newc[0],'head':newc[1],'ones':sorted(newc[2]),'whole_tape_equal':True}
  def relevant(c):return {f'{q},{b}':c[q,b] for q in (51,88,301) for b in (0,1)}
  results.append({'name':parent+'MS','parent':parent,'parent_sha256':sha(pr),'native_sha256':sha(nr),'dense_sha256':sha(dr),'working_states':194,'rows':388,'all_states_graph_reachable':True,'dense_native_conjugacy':'PASS','complete_changed_row_premises':'PASS','incoming_history_rows':{str(q):v for q,v in incoming.items()},'two_cell_cases':cases,'startup':saved_seed,'prefix_materiality':{'parent_steps':seed+10000,'child_steps':micro,'special_rows_total':relevant(counts),'special_rows_after_clean_seed':relevant(after)},'arithmetic_conclusion_from_finite_premises':'With totalized halting, iPRA proves H_parent(t) -> H_child(5t) and H_child(t) -> H_parent(t). See standalone proof; this checker itself is not a proof-assistant kernel.'})
 out={'status':'PASS','scope':__doc__,'results':results};a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','results':[{k:r[k] for k in ('name','dense_sha256','startup','prefix_materiality')} for r in results]},indent=2))
if __name__=='__main__':main()
