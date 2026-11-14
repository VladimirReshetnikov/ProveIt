#!/usr/bin/env python3
"""Enumerate small neighborhoods of the exact AX parse, with local-fold cost."""
import compile_ax as c
import collections,json,pathlib,hashlib,time,sys
g=c.g; OUT=c.HERE/('safe_layout_catalog' if '--safe' in sys.argv else 'layout_catalog');OUT.mkdir(exist_ok=True)
def digest(t):return hashlib.sha256(json.dumps(t,separators=(',',':')).encode()).hexdigest()[:16]
def emit(tree,T,internal,root,selection,level):
 new,proj=c.make_fold(T,selection)
 working=c.states(new);mapping={74:0}
 for q in sorted(working):
  if q not in mapping:mapping[q]=len(mapping)
 mapping[254]=len(working)
 raw=''.join(f'{mapping[q]} {b} {w} {d} {mapping[r]}\n' for (q,b),(w,d,r) in sorted(new.items(),key=lambda z:(mapping[z[0][0]],z[0][1])))
 name=f'{len(working)}_{digest(tree)}'
 (OUT/(name+'.tm')).write_text(raw)
 (OUT/(name+'.json')).write_text(json.dumps({'tree':tree,'source_word':g.word(tree),'folds':selection,'native_to_dense':mapping,'level':level,'working_states':len(working),'raw_sha256':hashlib.sha256(raw.encode()).hexdigest(),'decoder_three_step_folds_verified':True,'source_metrics':c.source_metrics(tree),'source_and_full_runtime_proof':'not yet rederived'},indent=2)+'\n')
 return name
def rotations(cur):
 for q in g.nodes(cur):
  l,r=q
  if isinstance(l,tuple):yield g.replace(cur,q,(l[0],(l[1],r)))
  if isinstance(r,tuple):yield g.replace(cur,q,((l,r[0]),r[1]))
def main():
 begin=time.time();base=g.get_macro_tree()[2];q=collections.deque([(base,0)]);seen={base};counts=collections.Counter();limit=int(sys.argv[1]) if len(sys.argv)>1 else 240;priced=0;best=999
 while q and time.time()-begin<limit:
  cur,level=q.popleft();T,internal,root=c.compile_tree(cur);selection=c.best_selection(T,internal);n=len(c.states(T))-len(selection);priced+=1;counts[n]+=1
  if n<=198 and ('--safe' not in sys.argv or c.source_metrics(cur)['max_consecutive_zeros']<=6):
   name=emit(cur,T,internal,root,selection,level)
   if n<best:best=n;print('BEST',name,'level',level,'priced',priced,flush=True)
   if n<196:print('FOUND',name,flush=True);break
   if level<4:
    for t in rotations(cur):
     if len(g.nodes(t))>71 or t in seen:continue
     seen.add(t);q.append((t,level+1))
  if priced%1000==0:print('PROGRESS',priced,'queue',len(q),'counts',dict(counts),'seconds',time.time()-begin,flush=True)
 print('DONE',priced,'queue',len(q),'counts',dict(counts),'seconds',time.time()-begin,flush=True)
 (OUT/'receipt.json').write_text(json.dumps({'priced':priced,'unfinished_queue':len(q),'counts':dict(counts),'seconds':time.time()-begin},indent=2))
if __name__=='__main__':main()
