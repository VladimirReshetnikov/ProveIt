from core import *
import itertools,time
options=[(n,b.tup(t)) for score,n,t in json.loads((ROOT/'recorded/singles.json').read_text())]
def synth_joint(edits):
 qs={name_q[n] for n in edits};rows=dict(raw);sigs={(rows[q,0],rows[q,1]):q for q,_ in rows if q not in qs};qq=4000
 def action(t,bit):
  nonlocal qq
  if isinstance(t,str):
   if t in name_q:return bit,True,name_q[t]
   t=nodes[t]
  if t[0]=='leaf':
   if t[1] in leaf_targets:return bit,True,leaf_targets[t[1]][t[2]]
   if t[1]=='continueTo':return (0,False,1) if t[2]==1 else (0,False,16) if t[2]==2 else (1,False,73)
   if t[1]=='breakTo' and t[2]==1:return 0,False,302
   if t[1]=='halt':return bit,True,b.HALT
   raise ValueError(t)
  acts=action(t[0],0),action(t[1],1)
  if acts in sigs:return bit,True,sigs[acts]
  q=qq;qq+=1;rows[q,0],rows[q,1]=acts;sigs[acts]=q
  return bit,True,q
 for name,t in edits.items():
  q=name_q[name];rows[q,0],rows[q,1]=action(t[0],0),action(t[1],1)
 return b.reachable(rows)
seenrows=set();results=[];hist=collections.Counter();hit=0;begin=time.time()
for depth in (2,3,4) if '--full' in sys.argv else (2,):
 count=0
 for combo in itertools.combinations(options,depth):
  edits=dict(combo)
  if len(edits)!=depth:continue
  rr=synth_joint(edits);key=tuple(sorted(rr.items()))
  if key in seenrows:continue
  seenrows.add(key);count+=1
  folds=proposed_folds(rr);score=len(rr)//2-len(folds);hist[score]+=1
  if score<194:
   nn=dict(nodes);nn.update(edits);ss,ii=b.source(nn,ax)
   out=ROOT/'generated'/('joint_hit_'+str(hit));out.mkdir(parents=True,exist_ok=True);hit+=1
   b.dump(out/'edits.json',edits);b.dump(out/'nodes.json',nn);b.dump(out/'sites.json',ss);b.dump(out/'folds.json',folds)
   (out/'raw.tm').write_text(b.table_text(rr))
   ok=ii==ins
   try:
    folded,al=b.apply_folds(rr,folds);lc=b.check_folds(rr,folded,al,folds)
    (out/'machine.native.tm').write_text(b.table_text(folded));b.dump(out/'local.json',lc)
    foldok=True
   except (AssertionError,KeyError) as e:foldok=False
   rec=dict(names=list(edits),states=score,source_identical=ok,folds_pass=foldok,path=str(out));results.append(rec);print('HIT',rec,flush=True)
 print('depth',depth,'unique',count,'hist',dict(sorted(hist.items())),'seconds',time.time()-begin,flush=True)
(ROOT/'replay.json').write_text(json.dumps(dict(options=options,histogram=dict(hist),hits=results,unique=len(seenrows)),indent=2))
