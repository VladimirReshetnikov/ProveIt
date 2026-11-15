#!/usr/bin/env python3
"""Exact full-tuple all-root action-graph comparisons, with enlarged symmetries."""
from pathlib import Path
import json,hashlib,time,collections,argparse,tempfile,sys
if not __debug__ or sys.flags.optimize:
 raise SystemExit('Run without -O or PYTHONOPTIMIZE.')
OUT=Path(__file__).resolve().parent

def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,t=line.split();key=(int(q),int(b));assert key not in rows
  rows[key]=(int(w),-1 if d=='L' else 1,int(t));assert d in ('L','R')
 states={q for q,b in rows};assert set(rows)=={(q,b) for q in states for b in(0,1)}
 halts={t for w,d,t in rows.values()}-states;assert len(halts)==1
 assert all(w in (0,1) for w,d,t in rows.values())
 return rows,states,next(iter(halts))

def rooted(data,start,reflection,complement,ignore_terminal=True):
 rows,states,halt=data;index={start:0};order=[start];seq=[]
 for q in order:
  for bit in (0,1):
   w,d,t=rows[q,bit^complement]
   if t==halt:
    seq.append((0,1,-1) if ignore_terminal else (w^complement,-d if reflection else d,-1))
   else:
    if t not in index:index[t]=len(order);order.append(t)
    seq.append((w^complement,-d if reflection else d,index[t]))
 if len(order)!=len(states):return None
 return tuple(seq)

def canonical(data):
 best=None;best_params=None;roots=[]
 for q in sorted(data[1]):
  base=rooted(data,q,False,False)
  if base is None:continue
  roots.append(q)
  for r,c in ((False,False),(True,False),(False,True),(True,True)):
   f=base if not r and not c else rooted(data,q,r,c)
   if best is None or f<best:best,best_params=f,(q,r,c)
 return best,dict(spanning_roots=roots,canonical_parameters=best_params)

def h(value):return hashlib.sha256(json.dumps(value,separators=(',',':')).encode()).hexdigest()

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('candidates',nargs='*',type=Path);parser.add_argument('--receipt',type=Path);args=parser.parse_args()
 if not args.candidates:args.candidates=[OUT.parent/'machines'/name/'machine.tm' for name in ('PA194AX11GH','PA194AX11GHS')]
 if args.receipt is None:args.receipt=Path(tempfile.mkdtemp(prefix='pa194-novelty-'))/'receipt.json'
 started=time.time();old=json.loads((OUT/'comparison194_complete.json').read_text());canon={};records=[]
 for i,r in enumerate(old):
  p=OUT/'representatives194'/(r['table_class']+'.tm');data=parse(p);c,meta=canonical(data)
  canon[r['table_class']]=c
  records.append({'table_class':r['table_class'],'name':r['historical_name'],'path':r['representative'],'spanning':c is not None,'broad_canonical_sha256':h(c) if c is not None else None,**meta})
  if (i+1)%25==0:print('classified',i+1,flush=True)
 results=[];new_forms=[]
 for p in args.candidates:
  name=p.parent.name if p.name=='machine.tm' else p.stem
  data=parse(p);c,meta=canonical(data);assert c is not None
  matches=[x for x in records if canon[x['table_class']]==c]
  result={'name':name,'table_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'states':len(data[1]),'rows':len(data[0]),'terminal':data[2],'canonical_sha256':h(c),'historical_match_count':len(matches),'historical_matches':matches,'self_loops':sum(q==t for (q,b),(w,d,t) in data[0].items()),'indegree_histogram':dict(sorted(collections.Counter(collections.Counter(t for w,d,t in data[0].values() if t in data[1]).get(q,0) for q in data[1]).items())),**meta}
  results.append(result);new_forms.append(c)
 receipt={'source_revision':'1e1a41f799d4658b829cdd0eabae3775a0c8c4a0','comparison_method':'Full canonical tuple equality,all spanning roots,arbitrary state renaming,reflection,global bit exchange,terminal write/move ignored. Structural novelty only;global bit exchange does not preserve the zero blank.','historical_classes':len(old),'historical_spanning':sum(c is not None for c in canon.values()),'historical_nonspanning':sum(c is None for c in canon.values()),'nonspanning_exclusion':'Candidates admit spanning roots;the sole disconnected diagnostic does not.','candidates':results,'candidate_pair_equalities':[{ 'left':results[i]['name'],'right':results[j]['name'],'equal':new_forms[i]==new_forms[j]} for i in range(len(results)) for j in range(i)],'elapsed_seconds':time.time()-started}
 args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'historical_classes':receipt['historical_classes'],'historical_spanning':receipt['historical_spanning'],'candidates':[{'name':r['name'],'sha256':r['table_sha256'],'matches':r['historical_match_count']} for r in results],'pair_equalities':receipt['candidate_pair_equalities'],'receipt':str(args.receipt)},indent=2))
if __name__=='__main__':main()
