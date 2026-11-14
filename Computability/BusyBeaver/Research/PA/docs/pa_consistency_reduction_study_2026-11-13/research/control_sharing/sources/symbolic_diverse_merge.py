#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
import sys,json,time,itertools
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent/'base'))
import compiler as c, symbolic_runtime as s
PACKAGE=Path(__file__).resolve().parent.parent
OUTPUT_DIR=PACKAGE/'rerun_outputs'
OUTPUT_DIR.mkdir(parents=True,exist_ok=True)
c.ROOT=s.ROOT=PACKAGE/'inputs/pa196'
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
base=PACKAGE/'inputs/primary'
g=c.read_grammar(base/'source/pa194.grammar.json')
raw,ix,shape=c.build(g)
folds=json.loads((base/'source/pa194.folds.json').read_text())
alias={a:b for a,b,ac in folds};acts={b:ac for a,b,ac in folds}
rows={}
for (q,b),ac in raw.items():
 if q in alias:continue
 w,d,n=acts[q][b] if q in acts else ac
 rows[q,b]=w,bool(d),alias.get(n,n)
controls=sorted({q for q,b in rows})
sites,ins,contracts=c.source(g)
contexts={key:[] for key in rows if key[0] not in c.BOXSTATES}
seen={key:set() for key in contexts}
for contract in contracts:
 site,br,st,t=contract
 per_contract=set()
 def collect(x):
  q,onl,l,r=x
  if onl or q in c.BOXSTATES:return
  b=c.headbit(r)
  if b is None:return
  key=q,b
  if key not in contexts:return
  if key in per_contract:return
  per_contract.add(key)
  contexts[key].append((site,br,x,t))
 v=c.run(rows,contract,observe=collect)
 assert v is not None
for key,values in contexts.items():
 if len(values)>256:
  contexts[key]=[values[i*len(values)//256] for i in range(256)]
print('CONTEXTS',sum(map(len,contexts.values())), {q:[len(contexts.get((q,b),[])) for b in (0,1)] for q in controls},flush=True)
# Merely preferring keeper's original actions is a useful first screen.
actions=sorted(set(rows.values()))
solutions={key:[] for key in contexts}
start=time.time()
for q in controls:
 if q in c.BOXSTATES:continue
 for bit in (0,1):
  key=q,bit
  if not contexts[key]:continue
  old=rows[key]
  for act in actions:
   if act[2]==q:continue
   rows[key]=act
   good=True
   for contract in contexts[key]:
    if c.run(rows,contract,fuel=1600) is None:
     good=False;break
   if good:solutions[key].append(act)
  rows[key]=old
 print('Q',q,'solutions',solutions[q,0],solutions[q,1],'sec',round(time.time()-start,2),flush=True)
 (OUTPUT_DIR/'symbolic_diverse_solutions.json').write_text(json.dumps({f'{q},{b}':v for(q,b),v in solutions.items()}))
tested=0
for a,b in itertools.combinations([q for q in controls if q not in c.BOXSTATES],2):
 options=[set(solutions[a,x]) & set(solutions[b,x]) for x in (0,1)]
 if not all(options):continue
 for acts in itertools.product(*options):
  trial={(q,x):(w,d,b if n==a else n) for (q,x),(w,d,n) in rows.items() if q!=a}
  for x,(w,d,n) in enumerate(acts):trial[b,x]=w,d,b if n==a else n
  tested+=1
  if tested%100==0:print('TESTED',tested,flush=True)
  receipt=c.validate(trial,contracts)
  if receipt['ok']:
   print('HIT',a,b,acts,receipt,flush=True)
   (OUTPUT_DIR/f'hit_{a}_{b}.tm').write_text(''.join(f'{q} {x} {w} {"R" if d else "L"} {n}\n' for(q,x),(w,d,n) in sorted(trial.items())))

print('DONE',tested,'candidate quotients tested',flush=True)
