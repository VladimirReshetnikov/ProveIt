#!/usr/bin/env python3
"""Search strict finite-context state folds with symbolic arbitrary exterior tapes.

An accepted row must simulate each old one-step action in at most MAX_STEPS,
without entering the patch control before reaching the exact target config.
This is a local finite certificate, not a finite blank-run experiment.
"""
import json, sys, itertools, time
from pathlib import Path
ROOT=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else Path(__file__).resolve().parent.parent/"inputs"
rows={}
labels=json.loads((ROOT/'pa194.labels.json').read_text())
for line in (ROOT/'pa194.tm').read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=(int(w),1 if d=='R' else -1,labels[int(n)])
START=74;HALT=254
MAX_STEPS=int(sys.argv[1]) if len(sys.argv)>1 else 15
states=sorted({q for q,b in rows})
incoming={q:set() for q in states}
for (q,bit),(w,d,n) in rows.items():
 if n in incoming:incoming[n].add((-d,w))
# Only contexts forced by every incoming edge; source initial control excluded.
contexts={q:next(iter(cs)) for q,cs in incoming.items() if len(cs)==1 and q!=START}

def check_action(a,b,bit,action,old,context):
  side,prev=context
  wr,dr,trg=old
  target=(b if trg==a else trg,dr)
  init={0:bit,side:prev}
  target_tape=dict(init);target_tape[0]=wr
  # Current tape only contains concretized cells. Unknown cells are assigned on
  # demand in init too. Their final value must agree with that assigned original.
  stack=[(b,0,dict(init),dict(init),0,[])]
  longest=0; leaves=[]
  while stack:
    q,h,tape,initial,k,trace=stack.pop()
    if k and (q,h)==target:
      expected=dict(initial);expected[0]=wr
      if tape==expected:
        longest=max(longest,k);leaves.append(trace);continue
    if k>=MAX_STEPS or (k and q==b) or q==a or q not in states:return None
    if h not in tape:
      for v in (0,1):
        ti=dict(tape);ini=dict(initial);ti[h]=ini[h]=v
        stack.append((q,h,ti,ini,k,trace))
      continue
    v=tape[h]
    if not k: act=action
    else: act=rows[q,v]
    w,d,n=act
    n=b if n==a else n
    tape[h]=w
    stack.append((n,h+d,tape,initial,k+1,trace+[[q,h,v,w,d,n]]))
  return {'max_steps':longest,'branches':len(leaves),'traces':leaves}

def main():
  start=time.monotonic();hits=[];pairs=0
  print(json.dumps({'states':len(states),'contexts':contexts,'max_steps':MAX_STEPS}),flush=True)
  for a,b in itertools.combinations(contexts,2):
    if contexts[a]==contexts[b]:continue
    pairs+=1;options=[]
    for bit in (0,1):
      opts=[]
      # One-step identical actions and arbitrary three/five/etc-step redirects.
      for w,d,h in itertools.product((0,1),(-1,1),states+[HALT]):
        if h==a:continue
        act=(w,d,h)
        ca=check_action(a,b,bit,act,rows[a,bit],contexts[a])
        if ca is None:continue
        cb=check_action(a,b,bit,act,rows[b,bit],contexts[b])
        if cb is not None:opts.append({'action':act,'a':ca,'b':cb})
      options.append(opts)
      if not opts:break
    if len(options)==2 and all(options):
      hit={'a':a,'b':b,'contexts':[contexts[a],contexts[b]],'options':options}
      hits.append(hit);print(json.dumps(hit),flush=True)
  receipt={'checked_pairs':pairs,'max_steps':MAX_STEPS,'seconds':time.monotonic()-start,'hits':hits}
  (ROOT/f'extended_local_fold_{MAX_STEPS}.json').write_text(json.dumps(receipt,indent=2)+'\n')
  print(json.dumps({k:v for k,v in receipt.items() if k!='hits'}),flush=True)
if __name__=='__main__':main()
