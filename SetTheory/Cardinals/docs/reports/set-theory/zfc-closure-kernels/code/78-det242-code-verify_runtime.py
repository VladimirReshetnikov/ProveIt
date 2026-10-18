#!/usr/bin/env python3
"""Recheck every source instruction against the literal detour242 table.

Expanded mode proves table-bound induction rules and quantifies all nine
independent natural registers, arbitrary gap>=64, and every nonempty finite
spare suffix. Affine mode is faster and relies on inherited box contracts.
This is ordinary symbolic verification, not a proof-assistant endpoint.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return sha256(p.read_bytes()).hexdigest()
def main():
 if not __debug__:raise RuntimeError('Run with assertions enabled.')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--expanded',action='store_true')
 ap.add_argument('--output',type=Path)
 args=ap.parse_args()
 ref=ROOT/'reference/baseline245';candidate=ROOT/'machine'
 index=json.loads((ROOT/'reference/reference-inputs.json').read_text())
 inputs={}
 for item in index['files']:
  path=ref/item['path'];assert digest(path)==item['sha256'],path
  inputs[str(path.relative_to(ROOT))]=digest(path)
 assert len(inputs)==291
 for path in [Path(__file__).resolve(),candidate/'zfc_detour242_old.tm',candidate/'zfc_detour242.tm',candidate/'renumbering.json',candidate/'sites_logical.json',candidate/'sites_physical.json']:
  inputs[str(path.relative_to(ROOT))]=digest(path)
 assert digest(candidate/'zfc_detour242_old.tm')=='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
 assert digest(candidate/'sites_logical.json')=='3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
 sys.path.insert(0,str(ref/'code'))
 import build_routing_machine as B
 from review_affine_source import full_inc,full_strip
 T,start=B.rebuild.read_table(candidate/'zfc_detour242_old.tm')
 assert start==95 and len(T)==484
 states={q for q,b in T};assert len(states)==242 and 254 not in states
 assert set(T)=={(q,b)for q in states for b in (0,1)}
 assert {q for w,d,q in T.values()}-states=={254}
 logical=json.loads((candidate/'sites_logical.json').read_text());physical=json.loads((candidate/'sites_physical.json').read_text())
 assert len(logical)==len(physical)==6459
 assert sum(2 if op=='CD'else 1 for p,op,r in logical)==8390
 records=[];counts=Counter();rules=Counter();used=set();begin=time.monotonic()
 if args.expanded:
  import full_symbolic_parametric as F
  assert F.PADDING==64
  F.m.TABLE=T
  F.m.prove_blocks();F.m.prove_word_identity()
  for i,(p,op,r) in enumerate(logical):
   for zero in ((True,False)if op=='CD'else(None,)):
    result=F.case(p,op,r,zero,[[0,9]]*9)
    for step in result['trace']:
     if 'state'in step:used.add((step['state'],step['read']))
     rules[step['rule']]+=1
    counts['cases']+=1;counts['symbolic_rules']+=result['rules']
    records.append(dict(index=i,pc=p,op=op,r=r,zero=zero,**{k:v for k,v in result.items()if k!='trace'}))
   if i%500==0:print('expanded sites',i,'cases',counts['cases'],'seconds',round(time.monotonic()-begin,2),flush=True)
  assert used<=set(T)
 else:
  import parametric_prefix_affine as affine
  affine.PADDING=64
  TT={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in T.items()}
  for i,(p,op,r) in enumerate(physical):
   for zero in ((True,False)if op=='CD'else(None,)):
    branch=(r,zero)if op=='CD'else None;extra=0;effect=None;overflow=False
    if op=='CI':successor,overflow=full_inc(p);effect=('inc',r)
    elif op=='CD'and not zero:successor,overflow=full_inc(p);effect=('dec',r);extra=1
    elif op=='CD':successor,overflow=full_inc(full_strip(p,'0',1))
    elif op=='CB':successor,overflow=full_inc(full_strip(p,'0',r))
    elif op=='CC':successor=full_strip(p,'1',r)
    else:assert op=='CH';successor=''
    right=[('b',int(b))for b in successor]+[('r',0,1,64+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
    rc,literal=affine.run(TT,p,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
    assert literal>0;counts['cases']+=1;rules.update(rc)
    records.append(dict(index=i,pc=p,op=op,r=r,zero=zero,symbolic_rules=sum(rc.values()),minimum_literal_steps=literal))
 assert counts['cases']==8390
 after={p:digest(ROOT/p)for p in inputs};assert inputs==after
 out=dict(status='PASS_UNIVERSAL_EXPANDED_RUNTIME'if args.expanded else'PASS_UNIVERSAL_AFFINE_RUNTIME',complete=True,
  table_sha256=digest(candidate/'zfc_detour242_old.tm'),source_sha256=digest(candidate/'sites_logical.json'),working_states=242,source_leaves=6459,expected_cases=8390,
  frame_padding=64,arbitrary_primary_registers=True,arbitrary_nonempty_finite_spare_suffix=True,positive_progress_checked=True,
  counts=dict(counts),rules=dict(rules),literal_rows=sorted(used),literal_rows_covered=len(used)if args.expanded else None,unused_rows=sorted(set(T)-used)if args.expanded else None,
  seconds=time.monotonic()-begin,inputs_before=inputs,inputs_after=after,cases=records,
  scope='Ordinary symbolic induction over the literal table; no new Lean/Rocq kernel endpoint or internal PA theorem.')
 dest=args.output or ROOT/'evidence'/('expanded-runtime.json'if args.expanded else'affine-runtime.json')
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('inputs_before','inputs_after','cases','literal_rows')},indent=2),flush=True)
if __name__=='__main__':main()
