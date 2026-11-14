#!/usr/bin/env python3
"""Certify that five fixed near misses need at least two *additional* changed rows.

Scope: 13-cell exact one-parent-step positive simulations of at most 128 child
steps, using the radius-six blank-start abstract window closure. This is not a
lower bound on 195-state machines, nor a claim of differing halting behavior.
Python 3.10+, standard library only.
"""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,json

DIGEST='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
NEAR_MISSES=[(45,160,(184,1),(1,-1,75)),(56,96,(96,1),(1,1,67)),
 (96,56,(56,1),(1,1,67)),(96,103,(103,1),(1,1,110)),(103,96,(96,1),(1,1,110))]
RADIUS=6
FUEL=128

def load(path):
 data=path.read_bytes();assert sha256(data).hexdigest()==DIGEST
 table={}
 for line in data.decode('ascii').splitlines():
  q,b,w,d,n=line.split();key=int(q),int(b);assert key not in table
  table[key]=int(w),1 if d=='R' else -1,int(n)
 assert set(table)=={(q,b) for q in range(196) for b in (0,1)}
 assert all(w in (0,1) and d in (-1,1) and 0<=n<=196 for w,d,n in table.values())
 return table

def closure(table):
 width=2*RADIUS+1;mask=(1<<width)-1;mid=1<<RADIUS
 seen={(0,0)};queue=deque(seen);halt=False
 while queue:
  q,bits=queue.popleft();w,d,n=table[q,(bits>>RADIUS)&1]
  bits=(bits|mid) if w else bits&~mid
  if n==196:halt=True;continue
  for fresh in (0,1):
   shifted=((bits>>1)|(fresh<<(width-1))) if d==1 else ((bits<<1)&mask)|fresh
   pair=n,shifted
   if pair not in seen:seen.add(pair);queue.append(pair)
 return seen,halt

def block(table,drop,keep,key,row,parent,mask):
 project=lambda q:keep if q==drop else q
 t={i:(mask>>(i+RADIUS))&1 for i in range(-RADIUS,RADIUS+1)}
 w,gh,gs=table[parent,t[0]];goal=t.copy();goal[0]=w;gs=project(gs)
 q=project(parent);h=0;trace=[]
 for k in range(FUEL):
  if q==196 or h not in t:
   return {'matched':False,'reason':'halt' if q==196 else 'outside-window','steps':k,'trace':trace}
  b=t[h];w,d,n=row if (q,b)==key else table[q,b]
  trace.append([q,h,b,w,d,project(n)])
  t[h]=w;h+=d;q=project(n)
  if q==gs and h==gh and t==goal:
   return {'matched':True,'steps':k+1,'trace':trace}
 return {'matched':False,'reason':'fuel','steps':FUEL,'trace':trace}

def rowset(result):return {(x[0],x[2]) for x in result['trace']}

def find_certificate(table,seen,near):
 drop,keep,key,row=near
 affected={drop,keep,key[0]};failures=[];attempts=0
 for q,mask in sorted(seen):
  if q not in affected:continue
  attempts+=1;r=block(table,drop,keep,key,row,q,mask)
  if not r['matched']:failures.append((q,mask,r))
 # Seek two independent obstruction traces. Their sets of queried transition
 # addresses intersect only at the row required to stay fixed.
 for i,(q,a,x) in enumerate(failures):
  for p,b,y in failures[i+1:]:
   common=rowset(x)&rowset(y)
   if common<={key}:
    return {'drop':drop,'keep':keep,'fixed_patch':{'address':list(key),'row':list(row)},
     'affected_windows':attempts,'failed_windows':len(failures),
     'witnesses':[{'parent_state':q,'window_mask':a,**x},{'parent_state':p,'window_mask':b,**y}],
     'common_transition_addresses':[list(z) for z in sorted(common)],
     'possible_additional_transition_addresses':[]}
 raise ValueError(('no two-window certificate',near))

def replay_trace(table,drop,keep,key,row,parent,initial,trace,reason):
 # Independent fixed-width bit-vector replay of the generated dictionary trace.
 proj=lambda x:keep if x==drop else x
 w,goal_head,n=table[parent,(initial>>RADIUS)&1]
 goal_bits=(initial|(1<<RADIUS)) if w else initial&~(1<<RADIUS)
 goal_state=proj(n);bits=initial;state=proj(parent);head=0
 for record in trace:
  assert -RADIUS<=head<=RADIUS and state!=196
  read=(bits>>(head+RADIUS))&1
  wr,move,dest=row if (state,read)==key else table[state,read]
  assert record==[state,head,read,wr,move,proj(dest)]
  bit=1<<(head+RADIUS)
  bits=(bits|bit) if wr else bits&~bit
  head+=move;state=proj(dest)
  assert (state,head,bits)!=(goal_state,goal_head,goal_bits)
 assert len(trace)<=FUEL
 assert (reason=='outside-window' and not -RADIUS<=head<=RADIUS or
         reason=='halt' and state==196 or reason=='fuel' and len(trace)==FUEL)
 return {(r[0],r[2]) for r in trace}

def verify_certificate(table,seen,c):
 drop,keep=c['drop'],c['keep'];key=tuple(c['fixed_patch']['address']);row=tuple(c['fixed_patch']['row'])
 addresses=[]
 for w in c['witnesses']:
  q,mask=w['parent_state'],w['window_mask'];assert (q,mask) in seen
  assert not w['matched'] and w['steps']==len(w['trace'])
  addresses.append(replay_trace(table,drop,keep,key,row,q,mask,w['trace'],w['reason']))
 common=set.intersection(*addresses)
 assert common<={key}
 assert [list(z) for z in sorted(common)]==c['common_transition_addresses']
 return True

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--table',type=Path,default=Path(__file__).with_name('pa196.tm'))
 ap.add_argument('--output',type=Path,default=Path(__file__).with_name('repair-obstructions.json'))
 args=ap.parse_args();table=load(args.table);seen,halt=closure(table)
 assert len(seen)==270067 and halt
 certificates=[find_certificate(table,seen,n) for n in NEAR_MISSES]
 assert all(verify_certificate(table,seen,c) for c in certificates)
 out={'pa196_sha256':DIGEST,'closure_radius':RADIUS,'closure_windows':len(seen),
      'abstract_halt_reachable':halt,'active_offsets':list(range(-RADIUS,RADIUS+1)),
      'maximum_child_steps':FUEL,'certificates':certificates}
 args.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'certificates':len(certificates),'failed_windows':[c['failed_windows'] for c in certificates],
  'witness_masks':[[w['window_mask'] for w in c['witnesses']] for c in certificates],
  'conclusion':'No one additional transition repair within the specified simulation template.'},indent=2))
if __name__=='__main__':
 if not __debug__: raise RuntimeError('Run without Python -O: assertion checks are required')
 main()
