#!/usr/bin/env python3
"""Bounded two-row reader folds checked against every actual source prefix.

The entire known prefix (including its left1 sentinel) is available; unknown
cells are never guessed. A successful prefix screen is not a physical theorem.
"""
from pathlib import Path
import argparse,json,time,hashlib
from collections import defaultdict

def need(v,msg):
 if not v:raise ValueError(msg)
def parse(path):
 t={}
 for line in path.read_text().splitlines():
  if not line.strip()or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));need((q,b)not in t,'duplicate row');t[q,b]=(w,1 if d=='R'else-1,n)
 need(len(t)%2==0 and set(t)=={(q,b)for q,z in t for b in(0,1)},'partial table')
 return t

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--machine',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--cap',type=int,default=100);ap.add_argument('--pair',type=int,nargs=2);args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
 T=parse(args.machine);sites=json.loads(args.sites.read_text());paths=[s['path']if isinstance(s,dict)else s[0]for s in sites]
 internal={p[:j]for p in paths for j in range(len(p))};need(''in internal,'source root')
 def decoder_paths():
  prefixes=defaultdict(list)
  def visit(prefix,q):
   prefixes[q].append(prefix)
   for bit in (0,1):
    child=prefix+str(bit)
    if child not in internal:continue
    tape=[1]+list(map(int,child));old=tape.copy();pos=len(prefix)+1;end=pos+1;now=q
    for tick in range(args.cap):
     if pos==end:break
     need(0<=pos<end,'decoder reads unknown cell')
     w,d,now=T[now,tape[pos]];tape[pos]=w;pos+=d
    need(pos==end and tape==old,'decoder does not preserve the prefix')
    visit(child,now)
  visit('',84);return prefixes
 ps=decoder_paths();pure={q for q in ps if all(T[q,b][:2]==(b,1)for b in(0,1))};states=sorted({q for q,b in T});print('PURE',len(pure),'DECODER',len(ps),'PREFIXES',sum(map(len,ps.values())),flush=True)
 def proj(q,drop,keep):return keep if q==drop else q
 def check(path,bit,expected,drop,keep,patches):
  data=[1]+list(map(int,path))+[bit];old=data.copy();pos=len(data)-1;end=pos+1;now=keep
  for step in range(args.cap):
   if pos==end:return now==proj(expected,drop,keep)and data==old
   if not 0<=pos<end:return False
   b=data[pos]
   if now==keep:
    if b not in patches:return None
    w,d,now=patches[b]
   else:
    if (now,b)not in T:return False
    w,d,now=T[now,b]
   data[pos]=w;pos+=d;now=proj(now,drop,keep)
  return False
 begin=time.monotonic();count=0;pairs=0;joint=0;survivors=[];allpairs=0
 for ix,drop in enumerate(sorted(pure)):
  for keep in sorted(pure):
   if keep>=drop:continue
   if args.pair and {drop,keep}!=set(args.pair):continue
   allpairs+=1
   cases={bit:sorted([(p,bit,T[q,bit][2])for q in(drop,keep)for p in ps[q]],key=lambda x:len(x[0]))for bit in(0,1)}
   opts={}
   for bit in(0,1):
    opts[bit]=[]
    acts={(bit,1,proj(T[q,bit][2],drop,keep))for q in(drop,keep)}|{(w,-1,h)for w in(0,1)for h in states if h!=drop}
    for action in sorted(acts):
     count+=1
     if all(check(p,bit,e,drop,keep,{bit:action})is not False for p,bit,e in cases[bit]):opts[bit].append(action)
    if not opts[bit]:break
   if not all(opts.get(b)for b in(0,1)):continue
   pairs+=1
   for a in opts[0]:
    for z in opts[1]:
     joint+=1
     if all(check(p,bit,e,drop,keep,{0:a,1:z})for bit in(0,1)for p,bit,e in cases[bit]):
      cand={(q,b):(w,d,proj(n,drop,keep))for(q,b),(w,d,n)in T.items()if q!=drop};cand[keep,0]=a;cand[keep,1]=z
      name=f'fold_{drop}_{keep}_{len(survivors):04d}.tm';dest=args.out/name
      dest.write_text('#! start 74\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(cand.items())))
      row={'drop':drop,'keep':keep,'patch0':a,'patch1':z,'table':name};survivors.append(row);print('SURVIVOR',row,flush=True)
  if ix%20==0:print('PROGRESS',ix,'branches',count,'joint',joint,'seconds',time.monotonic()-begin,flush=True)
 result={'machine_sha256':hashlib.sha256(args.machine.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(args.sites.read_bytes()).hexdigest(),'pure_decoder_states':len(pure),'decoder_states':len(ps),'known_prefixes':sum(map(len,ps.values())),'maximum_prefix_length':max(len(p)for pp in ps.values()for p in pp),'state_pairs':allpairs,'pairs_with_branch_candidates':pairs,'branch_action_trials':count,'joint_action_trials':joint,'survivors':survivors,'step_bound':args.cap,'restricted_pair':args.pair,'seconds':time.monotonic()-begin,'scope':'All known source prefixes, including the left1 sentinel, with inherited right actions or arbitrary bit-writing left-helper actions in two synthesized keeper rows. Does not cover larger row sets, unknown cells, longer blocks, altered source semantics, or general machine minimality. Any survivor requires full source/runtime/startup proofs.'}
 (args.out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
