#!/usr/bin/env python3
"""Two exact source interpreters check the proposed allocation-policy obstruction.

This does not execute a244 TM. It executes the certified Routing245 register
source, then evaluates the counterfactual recurrence of the proposed backend.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'reference/sites_logical.json'
EXPECTED_SOURCE='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==EXPECTED_SOURCE
sites=json.loads(SOURCE.read_text());assert len(sites)==6460
trie={};by_minimal={}
for p,op,r in sites:
    t=trie
    for b in p:
        assert 'leaf' not in t
        t=t.setdefault(b,{})
    assert not t;t['leaf']=(op,r)
    key=p.rstrip('0');assert key not in by_minimal;by_minimal[key]=(p,op,r)
def decode_a(pc):
    t=trie;i=0;p=''
    while 'leaf' not in t:
        b=pc[i] if i<len(pc) else '0';p+=b;i+=1;t=t[b]
    assert set(pc[i:])<=set('0')
    return p,*t['leaf']
def strip_a(p,b,k):
    i=len(p)
    while k and i:
        i-=1
        if p[i]==b:k-=1
    return p[:i]
def inc_a(p):
    i=len(p)
    while i and p[i-1]=='1':i-=1
    return (p[:i-1]+'1'+'0'*(len(p)-i),False) if i else ('',True)
def transition_a(regs,pc):
    p,op,r=decode_a(pc);out=regs.copy();ov=False;di=dd=0
    if op=='CI':out[r]+=1;di=1;nxt,ov=inc_a(p)
    elif op=='CD':
        if out[r]:out[r]-=1;dd=1;nxt,ov=inc_a(p)
        else:nxt,ov=inc_a(strip_a(p,'0',1))
    elif op=='CB':nxt,ov=inc_a(strip_a(p,'0',r))
    elif op=='CC':nxt=strip_a(p,'1',r)
    else:raise AssertionError('source unexpectedly halted')
    return p,op,r,out,nxt.rstrip('0'),int(ov),di,dd

def transition_b(regs,pc):
    # Independent decoding: a literal leaf is selected by its zero-trimmed word.
    p,op,r=by_minimal[pc];out=regs.copy();word=p;di=dd=0;advance=True
    if op=='CI':out[r]=out[r]+1;di=1
    elif op=='CD':
        if out[r]>0:out[r]=out[r]-1;dd=1
        else:
            positions=[i for i,b in enumerate(p) if b=='0']
            word=p[:positions[-1]] if positions else ''
    elif op in ('CB','CC'):
        positions=[i for i,b in enumerate(p) if b==('0' if op=='CB' else '1')]
        word=p[:positions[-r]] if len(positions)>=r else ''
        advance=op=='CB'
    else:raise AssertionError('source unexpectedly halted')
    if advance:
        value=int(word or '0',2)+1;ov=int(value>=2**len(word))
        nxt='' if ov else format(value,'0'+str(len(word))+'b').rstrip('0')
    else:ov=0;nxt=word.rstrip('0')
    return p,op,r,out,nxt,ov,di,dd

regs=[3,0,0,0,3,0,0,0,0];pc='';I=D=O=0;digest=hashlib.sha256();milestones=[];recent=[]
for step in range(1,3236):
    a=transition_a(regs,pc);b=transition_b(regs,pc);assert a==b,(step,a,b)
    p,op,r,regs,pc,ov,di,dd=a;I+=di;D+=dd;O+=ov
    g=181+D-I+O;assert g+sum(regs)==187+O
    rec=dict(step=step,path=p,op=op,r=r,registers=regs.copy(),pc=pc,increments=I,positive_decrements=D,root_overflows=O,counterfactual_gap=g)
    digest.update((json.dumps(rec,sort_keys=True,separators=(',',':'))+'\n').encode())
    recent.append(rec);recent=recent[-12:]
    if (len(milestones)==0 and g<64) or (len(milestones)==1 and g<0):
        milestones.append(dict(**rec,sum_primary=sum(regs),trace_sha256_through_step=digest.hexdigest(),last_twelve_steps=recent.copy()))
assert [(x['step'],x['counterfactual_gap']) for x in milestones]==[(2738,63),(3235,-1)]
out=dict(status='PASS_TWO_EXACT_SOURCE_REPLAYS',source_sha256=EXPECTED_SOURCE,source_leaves=6460,initial_pc='',initial_registers=[3,0,0,0,3,0,0,0,0],initial_gap=181,checked_source_steps=3235,allocation_recurrence='g=181+positive_decrements-increments+root_overflows',invariant='g+sum(primary)=187+root_overflows',milestones=milestones,scope='The source interpreter trace is exact. Gap is counterfactual. These witnesses refute automatic space closure for the proposed left increment with unchanged source/control allocation events. New grammar, new control flow, or explicit extension may change the recurrence or overflow count; no impossibility for all smaller machines follows.')
(HERE/'gap_budget_counterexamples.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='milestones'},indent=2))
print(json.dumps([{k:v for k,v in x.items() if k!='last_twelve_steps'} for x in milestones],indent=2))
