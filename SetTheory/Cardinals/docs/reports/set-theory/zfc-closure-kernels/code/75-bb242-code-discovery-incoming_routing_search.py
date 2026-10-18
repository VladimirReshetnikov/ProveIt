"""Delete a control by rerouting each incoming row independently.

Universal finite-window certificates compare positive whole-tape blocks.
Replacement traces may use only unmodified rows after their initial edge.
"""
import sys, json, pathlib, time, argparse, hashlib
from collections import defaultdict

from audit_tm import parse_table, window_reachable, Edge, local_trace

def default_input():
 for parent in pathlib.Path(__file__).resolve().parents:
  path=parent/'reference'/'zfc_combined243_old.tm'
  if path.is_file():return path
 return None

def check_row(m, dead, source, read, patterns, radius, bound):
    incoming={(s,b) for (s,b),e in m.rows.items() if e.target==dead and s!=dead}
    width=2*radius+1
    samples=sorted(patterns,key=lambda p:(p.bit_count(),p))
    old={p:local_trace(m,source,p,radius,bound) for p in samples}
    targets={p:{(q,h,t) for q,h,t in old[p] if q!=dead} for p in samples}
    hist=defaultdict(int)
    survivors=[]
    for target in m.states+[m.halt]:
      if target==dead: continue
      for move in [-1,1]:
       for write in [read,1-read]:
        matches=[]
        for index,pattern in enumerate(samples):
          tape=(pattern&~(1<<radius))|(write<<radius)
          q,h=target,move
          j=1
          while True:
            if (q,h,tape) in targets[pattern]:
              old_i=old[pattern].index((q,h,tape))+1
              matches.append((pattern,old_i,j));break
            if j>=bound or not -radius<=h<=radius or q==m.halt or q==dead:
              break
            b=(tape>>(h+radius))&1
            if (q,b) in incoming: break
            e=m.rows[q,b]
            tape=(tape&~(1<<(h+radius)))|(e.write<<(h+radius))
            h+=e.move;q=e.target;j+=1
          else:
            raise AssertionError('unreachable')
          if len(matches)!=index+1:
            hist[len(matches)]+=1;break
        else:
          survivors.append({'edge':[write,move,target],'cert':matches})
    return survivors,dict(hist)

def main():
  ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=5)
  ap.add_argument('--bound',type=int,default=64);ap.add_argument('--dead',type=int)
  ap.add_argument('--input',type=pathlib.Path,default=default_input(),help='Transition table; defaults to nearest archive reference/zfc_combined243_old.tm')
  ap.add_argument('--expected-sha256',help='Reject a table with a different SHA256')
  ap.add_argument('--output',type=pathlib.Path,help='JSON result; defaults to the current working directory')
  args=ap.parse_args()
  if args.input is None:ap.error('Supply --input when running outside the archive')
  if not 0<=args.radius<=10 or args.bound<1:ap.error('Radius must be 0..10 and bound positive')
  raw=args.input.read_text();input_sha=hashlib.sha256(args.input.read_bytes()).hexdigest()
  if args.expected_sha256 is not None and args.expected_sha256!=input_sha:ap.error('Input SHA256 mismatch')
  m=parse_table(raw);r=args.radius
  if args.dead is not None and (args.dead not in m.states or args.dead==m.start):ap.error('Selected control must be a noninitial working state')
  w=window_reachable(m,r)
  incoming=defaultdict(list)
  for (s,b),e in m.rows.items():
    if s!=e.target: incoming[e.target].append((s,b))
  report={'radius':r,'bound':args.bound,'survivors':[],'attempts':[],
          'input_sha256':input_sha,'input_filename':args.input.name,
          'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
          'auditor_sha256':hashlib.sha256(pathlib.Path(__file__).with_name('audit_tm.py').read_bytes()).hexdigest(),
          'scope':'Earlier incoming-only discovery family; not needed by the selected construction or its proof.'}
  t=time.monotonic()
  for dead in ([args.dead] if args.dead is not None else m.states):
    if dead==m.start:continue
    recipes=[]
    edges=sorted(incoming[dead],key=lambda e:len([p for p in w[e[0]] if (p>>r)&1==e[1]]),reverse=True)
    for source,b in edges:
      pats=[p for p in w[source] if (p>>r)&1==b]
      routes,hist=check_row(m,dead,source,b,pats,r,args.bound)
      report['attempts'].append([dead,source,b,len(routes),hist])
      if not routes:break
      recipes.append({'row':[source,b],'routes':routes})
      print('ROUTE',dead,source,b,[x['edge'] for x in routes],flush=True)
    else:
      report['survivors'].append({'dead':dead,'recipes':recipes})
      print('SUCCESS',dead,flush=True)
  report['elapsed']=time.monotonic()-t
  output=args.output or pathlib.Path.cwd()/f'incoming_routing_r{r}_d{args.dead}.json'
  output.parent.mkdir(parents=True,exist_ok=True)
  output.write_text(json.dumps(report,indent=2)+'\n')
  print('DONE',report['elapsed'],'survivors',[s['dead'] for s in report['survivors']],flush=True)

if __name__=='__main__':main()
