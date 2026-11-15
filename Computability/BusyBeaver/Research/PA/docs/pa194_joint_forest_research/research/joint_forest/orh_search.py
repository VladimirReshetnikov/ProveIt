"""Search history-only ORH control fusion; tests retain all source endpoints."""
from pathlib import Path
import sys,json,time,itertools,argparse
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[1]
sys.path.insert(0,str(PACKAGE/'construction/vendor'))
import symbolic_runtime as rt
import compiler as c
M=HERE/'inputs'
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'runs/orh_search');args=ap.parse_args()
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
def read(p):return {(int(q),int(b)):(int(w),d=='R',int(n)) for q,b,w,d,n in (x.split()for x in p.read_text().splitlines())}
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
rows=read(M/'machine.native.tm')
nodes={k:tup(v) for k,v in json.loads((M/'nodes.json').read_text()).items()}
c.raw_nodes=lambda:nodes
g=c.read_grammar(M/'grammar.json')
sites,ins,cs=c.source(g)
assert len(cs)==4778
assert rt.validate(rows,cs)['ok']
used={}; lengths=[]
for k,co in enumerate(cs):
 def observe(st):
  if not st[1] and st[3] and st[3][0][0]=='b':
   used.setdefault((st[0],st[3][0][1]),set()).add(k)
 lengths.append(rt.run(rows,co,observe=observe))
def merge(dst,acts):
 out={}
 for (q,b),(w,d,n) in rows.items():
  if q==92:continue
  if q==dst:w,d,n=acts[b]
  out[q,b]=(w,d,dst if n==92 else n)
 return out
states=sorted({q for q,b in rows}-rt.BOXSTATES-{92})
stats={};hits=[];trial=0;t0=time.monotonic()
for dst in states:
 for select in itertools.product(range(2),repeat=2):
  acts=[rows[[dst,92][select[b]],b] for b in (0,1)]
  out=merge(dst,acts)
  affected=set().union(*(used.get((q,b),set()) for q in (92,dst)for b in (0,1)))
  order=sorted(affected,key=lambda k:lengths[k])
  trial+=1
  for k in order:
   if rt.run(out,cs[k]) is None:
    stats[str(cs[k][:2])]=stats.get(str(cs[k][:2]),0)+1
    break
  else:
   v=rt.validate(out,cs)
   if v['ok']:
    name=f'merge92_{dst}_{select[0]}{select[1]}'
    (OUT/(name+'.tm')).write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'for (q,b),(w,d,n)in sorted(out.items())))
    hits.append(name);print('HIT',name,flush=True)
summary={'scope':'ORH inherited-action fusion of history control92 with every non-arithmetic-box control','trials':trial,'hits':hits,'first_failure_histogram':stats,'elapsed_seconds':time.monotonic()-t0}
(OUT/'orh_merges.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
