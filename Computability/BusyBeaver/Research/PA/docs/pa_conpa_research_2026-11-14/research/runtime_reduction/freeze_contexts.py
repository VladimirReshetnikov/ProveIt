#!/usr/bin/env python3
"""Freeze baseline radius-four abstract windows, replacing non-box windows by source envelopes."""
import pathlib,collections,json,argparse
root=pathlib.Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--candidate-root',type=pathlib.Path);args=parser.parse_args()
candidate_root=args.candidate_root or root.parents[1]/'machines'
for name in ['PA194AX11GH','PA194AX11GHS']:
 rows={}
 for line in (candidate_root/name/'machine.native.tm').read_text().splitlines():
  if not line.strip():continue
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 k=4;mask=(1<<(2*k+1))-1;seen=collections.defaultdict(set);queue=collections.deque([(74,0)]);seen[74].add(0)
 def add(q,p):
  if (q,0) in rows and p not in seen[q]:seen[q].add(p);queue.append((q,p))
 while queue:
  q,p=queue.popleft();w,d,n=rows[q,p>>k&1];p=(p&~(1<<k))|w<<k
  if d==1:add(n,p>>1);add(n,(p>>1)|(1<<2*k))
  else:add(n,(p<<1)&mask);add(n,((p<<1)&mask)|1)
 custom=collections.defaultdict(set)
 for line in (root/(name+'_contexts4.txt')).read_text().splitlines():
  q,p=map(int,line.split());custom[q].add(p)
 seen.update(custom)
 (root/(name+'_frozen_contexts4.txt')).write_text(''.join(f'{q} {p}\n' for q in sorted(seen) for p in sorted(seen[q])))
 print(name, len(seen),sum(map(len,seen.values())))
