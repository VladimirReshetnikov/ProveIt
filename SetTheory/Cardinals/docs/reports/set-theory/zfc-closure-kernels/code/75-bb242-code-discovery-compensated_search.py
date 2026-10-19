"""Search grafted controls with certified repairs at incoming rows.

Pair relation excludes dead and keep. Copy one dead row into keep, redirect
dead entries to keep, and repair incoming keep edges as needed. Match exact
whole windows at positive old/new clocks; unknown exterior is untouched.
"""
import sys,json,pathlib,time,argparse,itertools,hashlib
from collections import defaultdict
from audit_tm import parse_table,window_reachable,Edge,local_trace

def default_input():
 for parent in pathlib.Path(__file__).resolve().parents:
  path=parent/'reference'/'zfc_combined243_old.tm'
  if path.is_file():return path
 return None

class Search:
 def __init__(self,m,r,bound):
  self.m=m;self.r=r;self.bound=bound
  w=window_reachable(m,r)
  self.patterns={e:sorted((p for p in w[e[0]] if (p>>r)&1==e[1]),key=lambda p:(p.bit_count(),p)) for e in m.rows}
  self.incoming=defaultdict(list)
  for (s,b),edge in m.rows.items():self.incoming[edge.target].append((s,b))
  self.old={}
  self.states=m.states
 def trace_old(self,row,pattern):
  key=row,pattern
  if key not in self.old:self.old[key]=local_trace(self.m,row[0],pattern,self.r,self.bound)
  return self.old[key]
 def route(self,row,initial,dead,keep,graft,blocked,certificate=False):
  matches=[];r=self.r
  for pattern in self.patterns[row]:
   targets={c for c in self.trace_old(row,pattern) if c[0] not in (dead,keep)}
   tape=(pattern&~(1<<r))|(initial.write<<r)
   q,h=initial.target,initial.move
   for j in range(1,self.bound+1):
    if (q,h,tape) in targets:
      if certificate:matches.append([pattern,self.trace_old(row,pattern).index((q,h,tape))+1,j])
      break
    if q in (self.m.halt,dead) or not -r<=h<=r: return None
    b=(tape>>(h+r))&1
    if (q,b) in blocked:return None
    edge=graft[b] if q==keep else self.m.rows[q,b]
    tape=(tape&~(1<<(h+r)))|(edge.write<<(h+r))
    h+=edge.move;q=keep if edge.target==dead else edge.target
   else:return None
  return matches if certificate else True
 def recipe(self,dead,keep,bit,override=None):
  m=self.m
  graft={b:m.rows[(dead if b==bit else keep),b] for b in (0,1)}
  if override is not None:graft[bit]=override
  if graft=={b:m.rows[keep,b] for b in (0,1)}:return None
  # Internal transitions may only reference controls present in the candidate.
  graft={b:Edge(e.write,e.move,keep if e.target==dead else e.target) for b,e in graft.items()}
  blocked={row for dest in [dead,keep] for row in self.incoming[dest] if row[0] not in (dead,keep)}
  changes={}
  for row in self.incoming[dead]:
   if row[0] in (dead,keep):continue
   e=m.rows[row];initial=Edge(e.write,e.move,keep)
   if self.route(row,initial,dead,keep,graft,blocked) is None:return None
   changes[row]=initial
  # Copying the dead row is viable on every dead entry. Repair keep entries.
  for row in self.incoming[keep]:
   if row[0] in (dead,keep):continue
   e=m.rows[row]
   if self.route(row,e,dead,keep,graft,blocked) is not None:
    changes[row]=e;continue
   found=None
   for target in self.states:
    if target==dead:continue
    for move in [e.move,-e.move]:
     for write in [e.write,1-e.write]:
      initial=Edge(write,move,target)
      if self.route(row,initial,dead,keep,graft,blocked) is not None:
       found=initial;break
     if found:break
    if found:break
   if found is None:return {'status':'needs_repair','dead':dead,'keep':keep,'bit':bit,'failed':row,'earlier':[[*k,*v.__dict__.values()] for k,v in changes.items()]}
   changes[row]=found
  certificate={str(row):self.route(row,e,dead,keep,graft,blocked,True) for row,e in changes.items()}
  return {'status':'success','dead':dead,'keep':keep,'bit':bit,'changes':[[*k,v.write,v.move,v.target] for k,v in changes.items()],'graft':[[b,v.write,v.move,v.target] for b,v in graft.items()],'certificate':certificate}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=5);ap.add_argument('--bound',type=int,default=64)
 ap.add_argument('--input',type=pathlib.Path,default=default_input(),help='Transition table; defaults to nearest archive reference/zfc_combined243_old.tm')
 ap.add_argument('--expected-sha256',help='Reject a table with a different SHA256')
 ap.add_argument('--output',type=pathlib.Path,help='JSON result; defaults to the current working directory')
 ap.add_argument('--dead',type=int);ap.add_argument('--keep',type=int)
 ap.add_argument('--bit',type=int,choices=(0,1),help='Restrict to one copied row; omit for both bits')
 args=ap.parse_args()
 if args.input is None:ap.error('Supply --input when running outside the archive')
 if not 0<=args.radius<=10 or args.bound<1:ap.error('Radius must be 0..10 and bound positive')
 raw=args.input.read_bytes();input_sha=hashlib.sha256(raw).hexdigest()
 if args.expected_sha256 is not None and args.expected_sha256!=input_sha:ap.error('Input SHA256 mismatch')
 m=parse_table(raw.decode('utf-8'));S=Search(m,args.radius,args.bound)
 for control in (args.dead,args.keep):
  if control is not None and (control not in m.states or control==m.start):ap.error('Selected controls must be noninitial working states')
 if args.dead is not None and args.dead==args.keep:ap.error('Dead and keep must be different')
 result={'radius':args.radius,'bound':args.bound,'attempts':0,'findings':[],
         'input_sha256':input_sha,'input_filename':args.input.name,
         'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
         'auditor_sha256':hashlib.sha256(pathlib.Path(__file__).with_name('audit_tm.py').read_bytes()).hexdigest(),
         'scope':'Finite sufficient-certificate discovery; no minimality lower bound and no independent consistency calibration.'};t=time.monotonic()
 for dead in [args.dead] if args.dead is not None else S.states:
  if dead==m.start:continue
  for keep in [args.keep] if args.keep is not None else S.states:
   if keep in (m.start,dead):continue
   for bit in [args.bit] if args.bit is not None else (0,1):
    out=S.recipe(dead,keep,bit);result['attempts']+=1
    if out:
     result['findings'].append(out)
     if out['status']=='success':print(json.dumps({k:v for k,v in out.items() if k!='certificate'}),flush=True)
 result['elapsed']=time.monotonic()-t
 output=args.output or pathlib.Path.cwd()/f'compensated_{args.input.stem}_r{args.radius}_d{args.dead}_k{args.keep}.json'
 output.parent.mkdir(parents=True,exist_ok=True)
 output.write_text(json.dumps(result,indent=2)+'\n')
 print('DONE',result['attempts'],result['elapsed'],'findings',len(result['findings']),flush=True)

if __name__=='__main__':main()
