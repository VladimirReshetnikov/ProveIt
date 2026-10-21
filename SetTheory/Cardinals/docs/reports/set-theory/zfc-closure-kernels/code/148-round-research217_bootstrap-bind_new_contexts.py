#!/usr/bin/env python3
"""Fresh literal startup and read-only source-prefix binding. No received code."""
from pathlib import Path
import collections, hashlib, json
D=Path(__file__).resolve().parent
ROOT=D.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
    out={}
    for l in p.read_text().splitlines():
        if l and not l.startswith('#'):
            q,b,w,d,n=l.split();out[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    return out
parent=ROOT/'latest218_baseline/candidate-k218/k218.native.tm'
source=ROOT/'latest218_baseline/candidate-k218/sites218.json'
T=table(parent);C=table(D/'initialized217.native.tm')
ones=set();q=h=0;exceptions=[];all51=0
for tick in range(312909):
    b=int(h in ones)
    if q==51 and b==0:
        all51+=1
        if h+1 not in ones:
            exceptions.append(dict(step=tick,head=h,relative_ones=sorted(p-h for p in ones),
                left6=sum(1<<i for i in range(6)if h-6+i in ones)))
    w,d,q=T[q,b]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
assert q==84 and h==-5 and len(ones)==277
assert [e['step']for e in exceptions]==[79,160,306,471,1496]
old=json.loads((ROOT/'research218_round2_blank/SCANNER51_BOOT_CONTEXTS.json').read_text())['zero_right_events']
old_new_differences=[dict(step=e['step'],extra=sorted(set(e['relative_ones'])-{p-o['head']for p in o['one_cells']}),missing=sorted({p-o['head']for p in o['one_cells']}-set(e['relative_ones'])))for e,o in zip(exceptions,old)]
decoder=[];outcomes=collections.Counter();maxread=-100
for i,(pc,op,arg) in enumerate(json.loads(source.read_text())):
    ones={-1}|{j for j,b in enumerate(pc)if b=='1'}
    q=h=0;q=84;seen=set();events=[]
    for tick in range(200):
        # All cells below 40 are fixed in the newly certified frame allowance.
        if h>=40:
            stop='HEADER_OR_GAP_FRONTIER';break
        if (q,h)in seen:
            stop='READ_ONLY_EXACT_CYCLE';break
        if q==254:
            stop='HALT';break
        seen.add((q,h));maxread=max(maxread,h)
        b=int(h in ones)
        if q==51 and b==0 and h+1 not in ones:
            assert h+1<40
            decoder.append(dict(source_index=i,site=[pc,op,arg],tick=tick,head=h,
                left6=sum(1<<j for j in range(6)if h-6+j in ones),
                left_bits=''.join(str(int(h-j in ones))for j in range(1,7)),trace=events.copy()))
        w,d,n=C[q,b]
        events.append([q,h,b,w,d,n])
        if w!=b:
            stop='FIRST_DESTRUCTIVE_STEP';break
        q,h=n,h+d
    else:stop='PREFIX_BOUND'
    outcomes[stop]+=1
result=dict(status='EXACT_NEW_BOOT_AND_SOURCE_READ_ONLY_PREFIX_BINDING',
    parent_sha256=H(parent),composed_sha256=H(D/'initialized217.native.tm'),source_sha256=H(source),
    blank_steps=312909,old_new_boot_differences=old_new_differences,all_boot51_read0_visits=all51,boot_exceptions=exceptions,
    decoder_prefix_events=decoder,decoder_prefix_left6=sorted({e['left6']for e in decoder}),
    prefix_outcomes=dict(outcomes),max_read_head=maxread,
    scope='The five complete startup tapes are freshly bound to new218. Decoder events '
          'cover the read-only prefix of every new source leaf, independently of all '
          'register values and extra gap. This is not yet a projection of later engine '
          'visits in every symbolic primitive trace.')
(D/'NEW_CONTEXT_BINDING.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('decoder_prefix_events','boot_exceptions')},indent=2))
print('boot masks',sorted(e['left6']for e in exceptions))
print('decoder masks',collections.Counter(e['left6']for e in decoder))
