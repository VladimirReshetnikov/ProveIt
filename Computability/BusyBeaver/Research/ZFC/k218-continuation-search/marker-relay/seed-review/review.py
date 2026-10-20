"""Independent bounded source-trace check; no delivered runner or Lean invocation."""
from pathlib import Path
import json,gzip,hashlib,math
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT=Path(__file__).parent
S=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json'
T=Path('/tmp/k217-row36-marker/source-continuation1/trace.json.gz')
rows=json.loads(S.read_text()); index={p:i for i,(p,_,_)in enumerate(rows)}
assert len(index)==len(rows)==4744
spans={}
def span(p):
 if p in index: v=(index[p],index[p]+1)
 else:
  l,r=span(p+'0'),span(p+'1');assert l[1]==r[0];v=l[0],r[1]
 spans[p]=v;return v
span('')
def exit_to(p,bit,k):
 anc=[p[:i]for i,b in enumerate(p)if b==bit]
 if len(anc)<k:return 0
 lo,hi=spans[anc[-k]]
 return lo if bit=='1'else hi%len(rows)
def step(pc,regs):
 p,op,a=rows[pc];r=list(regs);n=(pc+1)%len(rows)
 if op=='CI':r[a]+=1
 elif op=='CD':
  if r[a]:r[a]-=1
  else:n=exit_to(p,'0',1)
 elif op=='CB':n=exit_to(p,'0',a)
 elif op=='CC':n=exit_to(p,'1',a)
 else:raise AssertionError(('unexpected halt',pc))
 return [n,r]
trace=json.load(gzip.open(T,'rt'))
assert trace[0]==[148,[1,9,0,2,0,1,0,2,0]]
for i in range(629):assert step(*trace[i])==trace[i+1],i
assert trace[613]==[154,[1,0,67,2,0,1,0,0,0]]
assert trace[629]==[161,[1,2,67,2,0,1,0,0,0]]
def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(z):
 w=(math.isqrt(8*z+1)-1)//2;b=z-w*(w+1)//2
 return w-b,b
assert pair(10,1)==67 and unpair(67)==(10,1)and unpair(1)==(1,0)
assert 4*pair(0,1)+2==10
paths=[S,T,Path('/tmp/k217-row36-marker/source-continuation1/result.json'),Path('/tmp/k217-row36-marker/relay16_six_returns.native.tm'),Path(__file__),ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum222.lean',ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean',ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Axioms219.lean',Path('/tmp/zfc-intake188/drop-review/ZFC_218_Research_2026-10-20/ZFC_218_Research_2026-10-20/research/source218/general_seed_lemma.md')]
result={'status':'BOUNDED_SOURCE_TRACE_AND_SEED_SCOPE_REVIEW_PASS','reviewer_role':'Independent source/API reviewer; not relay candidate or continuation author.','inputs':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in paths],'checked_source_transitions':629,'snapshots':[{'step':k,'ordinal':trace[k][0],'registers':trace[k][1]}for k in(0,613,629)],'exact_stack_decoding':{'67':[10,1],'1':[1,0],'10':'wal 0 F = 4*P(0,1)+2'},'findings':['The complete-frame checkpoint at ordinal148 is inside AX, not a source-root seed.','After629 exact source transitions, stack67 contains Q_0(F),F,0,...; standard Inv requires each to be derivable.','Source146 arbitrary-clean-seed theorem allows arbitrary np/d/pl, not arbitrary tw/h/ws.','Inherited par3/f305 ordinary macro contracts preserve this tail beneath eight AX rows; no exact new Lean transport or future candidate-runtime correctness is claimed.'],'limits':['No binary trace replay or new runtime certificate.','No complete source run, final machine halting, or permanent contamination claim.','The original Dag219 literal source differs from primary218 by inherited source rewrites; macro correspondence is ordinary source review, not literal whole-word/CFG equality.','No new supplied-code or Lean execution.']}
(OUT/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'checked_source_transitions':629,'receipt_sha256':hashlib.sha256((OUT/'review.json').read_bytes()).hexdigest()}))
