#!/usr/bin/env python3
"""Bounded search for a three-decoder/two-control contextual quotient.
Not a proof until a concrete model replays all universal local tape cases
and the complete source contracts. Existing unchanged rows are shared.
"""
from pathlib import Path
import sys,itertools,json,time,random,hashlib
import z3
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'reference/pa194/construction'))
import compiler as c
from build194 import read_table,table_text,startup,dense_table
native=read_table(HERE.parent/'reference/pa194/construction/tables/pa194.native.tm')
controls=sorted({q for q,b in native});N=len(controls);labels=controls+[254];indices={q:i for i,q in enumerate(labels)}
rows={(indices[q],bit):(w,bool(d),indices[n]) for (q,bit),(w,d,n) in native.items()}
inc={q:[] for q in range(N)}
for (q,b),(w,d,n) in rows.items():
 if n<N:inc[n].append((q,b,w,d))
def history(q):
 return {w for p,b,w,d in inc[q]} if all(d for p,b,w,d in inc[q]) else {0,1}
readers=[indices[q] for q in controls if q>=2000 and all(native[q,b][:2]==(b,True) for b in (0,1))]
pairs=[(a,b) for a in readers for b in readers if a!=b and history(a)=={0} and history(b)=={1}]
pairs.sort(key=lambda ab:-sum(rows[ab[0],bit]==rows[ab[1],bit] for bit in(0,1)))
rng=random.Random(194193);triples=[]
for a,b in pairs:
 choices=[q for q in readers if q not in (a,b)]
 choices.sort(key=lambda q:-sum(rows[q,bit][2] in (rows[a,bit][2],rows[b,bit][2]) for bit in(0,1)))
 choices=choices[:4]+rng.sample(choices[4:],min(4,len(choices[4:])))
 triples += [(a,b,q) for q in choices]
# Interleave pairs so the first pair does not dominate the finite budget.
triples=sorted(triples,key=lambda t:rng.random())
print('CANDIDATE_TRIPLES',len(triples),'READERS',len(readers),'PAIRS',len(pairs),flush=True)
baseW=z3.K(z3.IntSort(),z3.IntVal(0));baseD=z3.K(z3.IntSort(),z3.IntVal(1));baseQ=z3.K(z3.IntSort(),z3.IntVal(N))
for (q,b),(w,d,n) in rows.items():
 baseW=z3.Store(baseW,2*q+b,w);baseD=z3.Store(baseD,2*q+b,1 if d else -1);baseQ=z3.Store(baseQ,2*q+b,n)

def concrete(folded,a,b,q,B):
 alias=lambda s:b if s==a else s
 traces=[]
 for old in(a,b,q):
  for bits in itertools.product((0,1),repeat=3):
   if bits[0] not in history(old):continue
   target=rows[old,bits[1]];want=(alias(target[2]),1 if target[1] else -1,(bits[0],target[0],bits[2]))
   st,head,tape=alias(old),0,list(bits);trace=[(st,head,tape.copy())]
   for k in range(1,B+1):
    if head not in(-1,0,1) or st==N:return None
    w,d,st=folded[st,tape[head+1]];tape[head+1]=w;head+=1 if d else -1
    trace.append((st,head,tape.copy()))
    if (st,head,tuple(tape))==want:break
   else:return None
   traces.append({'old':labels[old],'initial':bits,'steps':k,'trace':trace})
 return traces

start=time.monotonic();satcount=0;timeouts=0;tested=0
for tid,(a,b,q) in enumerate(triples):
 if time.monotonic()-start>=300:break
 B=7;solver=z3.Solver();solver.set(timeout=300)
 vars={(st,bit):(z3.Int(f'w{st}_{bit}'),z3.Int(f'd{st}_{bit}'),z3.Int(f'n{st}_{bit}')) for st in(b,q) for bit in(0,1)}
 W,D,Q=baseW,baseD,baseQ
 for (st,bit),(ww,dd,nn) in vars.items():
  solver.add(ww>=0,ww<=1,z3.Or(dd==-1,dd==1),nn>=0,nn<=N,nn!=a)
  W=z3.Store(W,2*st+bit,ww);D=z3.Store(D,2*st+bit,dd);Q=z3.Store(Q,2*st+bit,nn)
 cases=0
 for old in(a,b,q):
  for bits in itertools.product((0,1),repeat=3):
   if bits[0] not in history(old):continue
   w0,d0,n0=rows[old,bits[1]];n0=b if n0==a else n0;wanted=(bits[0],w0,bits[2])
   st=z3.IntVal(b if old==a else old);head=z3.IntVal(0);tape=list(map(z3.IntVal,bits));done=z3.BoolVal(False)
   for k in range(B):
    solver.add(z3.Or(done,z3.And(head>=-1,head<=1,st!=N,st!=a)))
    bit=z3.If(head==-1,tape[0],z3.If(head==0,tape[1],tape[2]));ix=2*st+bit
    wr=z3.Select(W,ix);dr=z3.Select(D,ix);nr=z3.Select(Q,ix);nr=z3.If(nr==a,b,nr)
    newt=[z3.If(z3.And(z3.Not(done),head==j-1),wr,v) for j,v in enumerate(tape)]
    newh=z3.If(done,head,head+dr);newq=z3.If(done,st,nr)
    hit=z3.And(newq==n0,newh==(1 if d0 else -1),*[v==w for v,w in zip(newt,wanted)])
    done=z3.Or(done,hit);st,head,tape=newq,newh,newt
   solver.add(done);cases+=1
 result=solver.check();tested+=1
 if result==z3.sat:
  model=solver.model();folded={(st,bit):(w,d,b if n==a else n) for(st,bit),(w,d,n) in rows.items() if st!=a}
  for key,vs in vars.items():
   wr,dr,nr=[model.eval(v).as_long() for v in vs];folded[key]=(wr,dr==1,nr)
  traces=concrete(folded,a,b,q,B);assert traces is not None
  satcount+=1;out=HERE/'sat_hits'/f'hit{satcount}';out.mkdir(parents=True,exist_ok=True)
  nt={(labels[st],bit):(w,d,labels[n]) for(st,bit),(w,d,n) in folded.items()}
  (out/'machine.native.tm').write_text(table_text(nt));(out/'local.json').write_text(json.dumps({'remove':labels[a],'survivors':[labels[b],labels[q]],'bound':B,'cases':cases,'traces':traces},indent=2)+'\n')
  print('SAT_HIT',satcount,'TRIPLE',[labels[x] for x in(a,b,q)],'SEC',time.monotonic()-start,flush=True)
  sites,ins,contracts=c.source(c.read_grammar(HERE.parent/'reference/pa194/construction/source/pa194.grammar.json'))
  result=c.validate(nt,contracts);print('FULL_CONTRACTS',result,flush=True)
  if result['ok']:
   boot=startup(nt,sites[25][0]);dense,ls=dense_table(nt,193)
   (out/'machine.tm').write_text(table_text(dense));(out/'labels.json').write_text(json.dumps(ls));(out/'receipt.json').write_text(json.dumps({'validation':result,'startup':boot,'count':193},indent=2));break
 elif result==z3.unknown:timeouts+=1
 if tested%10==0:print('TESTED',tested,'SAT',satcount,'TIMEOUT',timeouts,'SEC',round(time.monotonic()-start,3),flush=True)
print('DONE',json.dumps({'tested':tested,'sat':satcount,'timeouts':timeouts,'seconds':time.monotonic()-start,'radius':1,'step_bound':7,'timeout_ms':300,'max_budget_seconds':300}),flush=True)
