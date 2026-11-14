from support import *
from collections import defaultdict
p=(INC,INC);c.MACROS[p]=99;c.MACROS[(p,p)]=190

def endpoint(rows,q,p,v):
 tape={-1:p,0:v};pos=0
 for step in range(20):
  if step and pos==1:return q,tape[-1],tape[0]
  if pos not in tape:return None
  a=rows.get((q,tape[pos]))
  if a is None:return None
  w,d,q=a;tape[pos]=w;pos+=1 if d else -1
 return None

def screen(name):
 t=c.read_grammar(name);r,idx,sh=c.build(t);ch=bestcompatible_all(r,sh);rr,alias=apply(r,ch)
 incoming=defaultdict(set)
 for(q,b),(w,d,n)in r.items():
  if d and w==b:incoming[alias.get(n,n)].add(b)
 touched={n for a,b,acts in ch for w,d,n in acts if not d}
 possibilities=[]
 for q in sh:
  if q in alias or q in touched:continue
  ctx=incoming[q]
  if not ctx:continue
  want={(p,v):endpoint(rr,q,p,v) for p in ctx for v in (0,1)}
  if any(z is None for z in want.values()):continue
  for b in {q for q,k in rr if q<1300}:
   if all(endpoint(rr,b,p,v)==z for (p,v),z in want.items()):possibilities.append((q,b))
 if possibilities:
  print('LOCAL',name,possibilities,flush=True)
  ss,ins,cs=c.source(t)
  for q,b in possibilities:
   trial={(s,k):(w,d,b if n==q else n) for(s,k),(w,d,n)in rr.items() if s!=q}
   check=c.validate(trial,cs);print('CHECK',q,b,check,flush=True)
   if check['ok']:
    Path('fixed_reuse195.grammar.json').write_text(Path(name).read_text());Path('fixed_reuse195.folds.json').write_text(json.dumps(ch));Path('fixed_reuse195.extra.json').write_text(json.dumps([q,b]));Path('fixed_reuse195.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(trial.items())));raise SystemExit('FOUND195')
 return len(possibilities)
if __name__=='__main__':
 import sys
 files=sys.argv[1:] or json.loads(Path('fixed_reuse_inputs.json').read_text())
 found=sum(screen(p)for p in files)
 print('FINISHED',len(files),'grammars;',found,'local candidates')
