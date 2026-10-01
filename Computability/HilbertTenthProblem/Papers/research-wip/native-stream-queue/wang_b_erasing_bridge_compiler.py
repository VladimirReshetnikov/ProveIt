"""Explicit append-only erasing-TM to non-erasing-binary-TM compiler.

All binary transition rows are materialized by binary(table). The five-bit
record protocol and complete input loader are proved in the companion note.
The whole Wang DAG is not materialized; its inherited paid size is bounded.
"""
from collections import deque
from collections import Counter
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import wang_b_nonerasing_tm_compiler as bridge

recoder = bridge.recoder
DEFAULT = (((0, 'R', 1), (0, 'R', 1)),)
BLOCK=5
L,R=3,7
HALT=('HALT',)
SINK=('SINK',)
def norm(table):
 t=tuple(tuple(tuple(x) for x in row) for row in table);h=len(t)
 for row in t:
  assert len(row)==2
  for w,d,q in row:assert w in (0,1) and d in ('L','R') and type(q)is int and 0<=q<=h
 return t

def macro_step(table,state,v):
 h=len(table);kind=state[0]
 fail=(v,1,SINK)
 if state==SINK:return fail
 if kind=='start':
  q=state[1]
  return (v|16,1,('begin',q)) if v==L else fail
 if kind=='begin':
  q=state[1]
  return (L,-1,('return',(q,0,0,0,0))) if v==0 else (v,1,state)
 if kind=='return':
  ctx=state[1]
  return (v,1,('fetch',ctx)) if v&16 else (v,-1,state)
 if kind=='fetch':
  q,seen,bb,bh,pending=ctx=state[1]
  if v==R:
   return (v,1,('finish_seek',bb,bh,pending,q)) if seen else fail
  if v not in (1,5,9,13):return fail
  b=(v>>2)&1;head=(v>>3)&1
  current_head=pending;next_pending=0
  if head:
   if seen:return fail
   b,di,q=table[q][b];seen=1
   if di=='L':bh=1
   else:next_pending=1
  nxt=(q,seen,b,current_head,next_pending)
  return (v|16,1,('seek_emit',bb,bh,nxt))
 if kind=='seek_emit':
  _,b,h,ctx=state
  return (1+4*b+8*h,-1,('return',ctx)) if v==0 else (v,1,state)
 if kind=='finish_seek':
  _,b,h,pending,q=state
  return (1+4*b+8*h,1,('finish_pad',pending,q)) if v==0 else (v,1,state)
 if kind=='finish_pad':
  _,pending,q=state
  return (1+8*pending,1,('finish_R',q)) if v==0 else fail
 if kind=='finish_R':
  q=state[1]
  return (R,-1,('find_L',q)) if v==0 else fail
 if kind=='find_L':
  q=state[1]
  return (v,0,HALT if q==len(table) else ('start',q)) if v==L else (v,-1,state)
 raise ValueError(state)

def abstract(table):
 table=norm(table)
 if not table:return {},HALT
 rows={};todo=deque([('start',0)])
 while todo:
  s=todo.popleft()
  if s in rows or s==HALT:continue
  row=tuple(macro_step(table,s,v) for v in range(32))
  for v,(w,d,q) in enumerate(row):assert w|v==w;assert d in (-1,0,1)
  rows[s]=row
  todo.extend(q for w,d,q in row if q not in rows and q!=HALT)
 return rows,('start',0)

def binary(table):
 """Return the concrete total binary table, label map and block control table."""
 return _binary(norm(table))

@lru_cache(None)
def _binary(table):
 macro,start=abstract(table)
 if start==HALT:return [],{},macro
 def target(q):return HALT if q==HALT else ('read',q,0,0)
 root=target(start);rules={};todo=deque([root])
 def preserve(d,q):return tuple((b,d,q) for b in (0,1))
 def walk(steps,q):
  return target(q) if steps==0 else ('walk',steps,q)
 def action(v,w,d,q):
  # At offset4 after reading all five bits. Optimize unchanged low bits.
  if (v&15)==(w&15):
   steps=5*d-4
   assert steps
   sign=1 if steps>0 else -1
   return ((w>>4)&1,sign,walk(steps-sign,q))
  return ((w>>4)&1,-1,('write',w,3,d,q))
 while todo:
  s=todo.popleft()
  if s in rules or s==HALT:continue
  if s[0]=='read':
   _,q,pos,sofar=s;row=[]
   for b in (0,1):
    v=sofar+(b<<pos)
    if pos<4:row.append((b,1,('read',q,pos+1,v)))
    else:
     w,d,nxt=macro[q][v]
     row.append(action(v,w,d,nxt))
  elif s[0]=='walk':
   _,steps,q=s;di=1 if steps>0 else -1
   row=preserve(di,walk(steps-di,q))
  else:
   _,w,pos,di,q=s
   if pos: direction=-1;nxt=('write',w,pos-1,di,q)
   elif di:direction=di;nxt=walk(4*di,q)
   else:direction=1;nxt=walk(-1,q)
   row=tuple((b|((w>>pos)&1),direction,nxt) for b in(0,1))
  rules[s]=tuple(row)
  for b,di,q in row:
   assert di in(-1,1)
   if q not in rules and q!=HALT:todo.append(q)
 ids={s:i for i,s in enumerate(rules)};ids[HALT]=len(ids)
 out=[tuple((b,'R' if di==1 else 'L',ids[q]) for b,di,q in row)for row in rules.values()]
 assert ids[root]==0
 assert all(row[1][0]==1 for row in out)
 return out,ids,macro

def word(x,n):
 assert 0<x<2**n
 blocks=[L]+[1+4*((x>>i)&1)+8*(i==0) for i in range(n)]+[R]
 return {5*i+j for i,b in enumerate(blocks) for j in range(5) if(b>>j)&1}

def check(table,x,n,limit=10):
 bt,ids,mac=binary(table);wt=word(x,n);nh=0;ns=0
 tape={i for i in range(n) if (x>>i)&1};head=0;state=0;left=0;size=n;record=0;steps=0;micro=0
 while state<len(table) and steps<limit:
  w,di,state=table[state][int(head in tape)]
  if w:tape.add(head)
  else:tape.discard(head)
  head+=1 if di=='R' else -1
  expected_tape=set(wt)
  expected_tape.update(record+5*i+4 for i in range(size+1))
  nxtrecord=record+5*(size+2);left-=1;size+=2
  expected_blocks=[L]+[1+4*(left+i in tape)+8*(left+i==head)
                            for i in range(size)]+[R]
  expected_tape.update(nxtrecord+5*i+j for i,v in enumerate(expected_blocks)
                       for j in range(5) if (v>>j)&1)
  target=ids[HALT] if state==len(table) else ids[('read',('start',state),0,0)]
  # Run one full record copy, target location distinguishes loops.
  while ns!=target or nh!=nxtrecord:
   read=int(nh in wt);ww,dd,ns=bt[ns][read]
   assert ww>=read
   if ww:wt.add(nh)
   nh+=1 if dd=='R' else -1;micro+=1
   assert micro<10000000
  assert sum((int(nh+j in wt)<<j) for j in range(5))==L
  for i in range(size):
   val=sum(int(nh+5*(i+1)+j in wt)<<j for j in range(5))
   assert val==1+4*(left+i in tape)+8*(left+i==head),(table,x,n,steps,i,val,tape,head,left)
  assert sum(int(nh+5*(size+1)+j in wt)<<j for j in range(5))==R
  assert wt==expected_tape, 'old record or exterior changed unexpectedly'
  record=nxtrecord;steps+=1
 return len(bt),len(mac),steps,micro,state==len(table)


def paired_word(x,n):
    """Direct literal double encoding in spatial, least-significant-bit order."""
    tape=word(x,n)
    return sum((1+2*int(j in tape)) << (2*j) for j in range(5*(n+2)))


def loader():
    """Complete ordinary-x graph for the framed Wang input, with output y."""
    old=recoder.build(width=10)
    extra=[('frame_repunit_multiple','*',1023,'frame_repunit'),
           ('frame_repeat','*',401563648,'frame_repunit'),
           ('frame_data','*',32768,'z'),
           ('frame_sum','+','frame_repeat','frame_data'),
           ('frame_input','+','frame_sum',523615)]
    return dict(old,source=list(old['source'])+extra,
        parameters=['x'],auxiliaries=['z']+list(old['auxiliaries'])+['frame_repunit'],
        comparisons=list(old['comparisons'])+[('frame_repunit_multiple','modulus')],
        operations=old['operations']+5,multiplications=old['multiplications']+3,
        additions_subtractions=old['additions_subtractions']+2,
        witnesses=old['witnesses']+2,equations=old['equations']+1,
        input_output='frame_input')


def loader_ledger():
    p=loader();s,out=recoder.polynomial_source(p)
    bridge.actions.scale.checked_source(s,p['parameters'],p['auxiliaries'])
    count=Counter('M' if op=='*' else 'A' for _,op,_,_ in s)
    assert len(s)==190 and count=={'M':94,'A':96}
    assert (p['operations'],p['equations'],p['witnesses'])==(143,16,38)
    inherited=recoder.degree_audit(recoder.build(width=10))
    degree={n:1 for n in p['parameters']+p['auxiliaries']}
    value=lambda x:degree[x] if isinstance(x,str) else 0
    for n,op,a,b in p['source']:
        degree[n]=value(a)+value(b) if op=='*' else max(value(a),value(b))
    assert degree['modulus']==10 and degree['frame_input']==1
    assert inherited['outer_residual_degree']>=10
    return dict(certificate=p['operations'],polynomial=len(s),M=count['M'],A=count['A'],
                comparisons=p['equations'],witnesses=p['witnesses'],parameters=1,
                degree_upper_bound=402,
                inherited_unit_degree=inherited['unit_degree'],
                inherited_outer_residual_degree=inherited['outer_residual_degree'],
                new_residual_degree_upper_bound=10,output_degree=1,
                source_sha256=hashlib.sha256(repr(s).encode()).hexdigest())


def machine_ledger(table=DEFAULT):
    table=norm(table)
    bt,ids,macro=binary(table)
    program=bridge.compile_tm(bt)
    h=len(bt);j=3*h;K=16*h+1;delta=int(h>0);lanes=12+K+2*delta
    chain=lanes.bit_length()+lanes.bit_count()-2
    certificate_bound=115+7*K+6*lanes+chain+delta*(j+3)
    # Use the frozen parent's proved upper bound. The computed-action
    # successor only removes gates/comparisons, so cannot increase it.
    wang_polynomial_bound=certificate_bound+45
    return dict(source_states=len(table),record_control_states=len(macro),
        nonerasing_states=h,nonerasing_transition_rows=2*h,
        table_sha256=hashlib.sha256(repr(bt).encode()).hexdigest(),
        wang_instructions=len(program),wang_jumps=j,wang_edges=K,joined_lanes=lanes,
        binary_chain_length=chain,parent_certificate_upper_bound=certificate_bound,
        complete_polynomial_upper_bound=wang_polynomial_bound+190+3,
        complete_degree_upper_bound=2*max(402,255*lanes+157),
        complete_comparisons=25,complete_witnesses=65+K+delta,
        scope='Literal finite machine; paid whole-compiler upper bound, not a materialized whole DAG or universal table.')


def macro_audit(table=DEFAULT):
    bt,ids,macro=binary(norm(table));rng=random.Random(514)
    count=steps=0
    for state,row in macro.items():
      for v,(w,di,nxt) in enumerate(row):
        tape={i for i in range(-10,15) if i not in range(5) and rng.randrange(2)}
        tape.update(i for i in range(5) if (v>>i)&1)
        expected=(tape-set(range(5)))|{i for i in range(5) if (w>>i)&1}
        q=ids[('read',state,0,0)];head=0
        target=ids[HALT] if nxt==HALT else ids[('read',nxt,0,0)]
        local=0
        while local==0 or q!=target or head!=5*di:
            read=int(head in tape);write,move,q=bt[q][read]
            assert write>=read
            if write:tape.add(head)
            head+=1 if move=='R' else -1;local+=1
            assert local<=20
        assert tape==expected
        count+=1;steps+=local
    return dict(complete_block_transition_cases=count,binary_microsteps=steps)


def loader_audit():
    p=loader();base=recoder.build(width=10);raw=recoder.generic.recoder(10)
    ps,out=recoder.polynomial_source(p);rng=random.Random(51410)
    for case in range(128):
        vals={n:rng.randrange(1,5) if case<64 else rng.randrange(-3,5)
              for n in p['parameters']+p['auxiliaries']}
        small={n:vals[n] for n in base['parameters']+base['auxiliaries']}
        lifted=recoder.lift(base,small);env=bridge.execute(raw['source'],lifted)
        value=lambda x:env[x] if isinstance(x,str) else x
        residuals={tuple(pair):value(pair[0])-value(pair[1]) for pair in raw['comparisons']}
        product=1
        for record,name in zip(base['factor_residuals'],base['unit_factors']):
            factor=1+record['multiplier']*residuals[tuple(record['pair'])]
            if name in base['auxiliary_strong_corrections']:
                correction=base['auxiliary_strong_corrections'][name]
                factor-=residuals[tuple(correction['pair'])]*env[correction['gap']]
            product*=factor
        omit=set(map(tuple,base['removed_parent_comparisons']))
        residuals=[v for k,v in residuals.items() if k not in omit]
        residuals.append(1023*vals['frame_repunit']-(env['Q']-1))
        wanted=product*(1+sum(r*r for r in residuals))-1
        assert bridge.execute(ps,vals)[out]==wanted
    words=0
    for n in range(2,11):
      for x in range(1,1<<n):
        Q=1<<(10*n);r=(Q-1)//1023
        z=sum(((x>>j)&1)<<(10*j) for j in range(n))
        assert paired_word(x,n)==523615+401563648*r+32768*z
        words+=1
    return dict(complete_loader_output_identities=128,signed_cases=64,
                exact_ordinary_input_words=words,
                scope='Complete loader algebra and finite morphism, not constructed Pell zeros.')


def verify():
    rng=random.Random(51510);totals=Counter();ledgers=[]
    # Every total one-state ordinary binary table, including all erasing rules.
    choices=[(w,d,q) for w in (0,1) for d in 'LR' for q in (0,1)]
    for zero in choices:
      for one in choices:
        table=((zero,one),)
        for x in (1,2,5):
          for n in (3,5):
            _,_,steps,micro,halted=check(table,x,n,6)
            totals.update(runs=1,tm_steps=steps,nonerasing_steps=micro,halts=int(halted))
    for h in (2,3,4):
      for _ in range(8):
        table=tuple(tuple((rng.randrange(2),rng.choice('LR'),rng.randrange(h+1))
                          for read in (0,1)) for q in range(h))
        for _ in range(3):
            x=rng.randrange(1,32);n=x.bit_length()+rng.randrange(1,4)
            _,_,steps,micro,halted=check(table,x,n,8)
            totals.update(runs=1,tm_steps=steps,nonerasing_steps=micro,halts=int(halted))
    for table in ((),DEFAULT,(((1,'L',0),(0,'R',1)),),
                  (((0,'R',1),(0,'L',1)),((1,'L',2),(0,'R',2)))):
        ledgers.append(machine_ledger(table))
    assert binary(())[0]==[] and bridge.compile_tm([])==('M',)
    invalid=[(((0,'S',0),(1,'R',1)),),(((0,'R',2),(1,'R',1)),),(((0,'R',1),),)]
    for table in invalid:
        try:norm(table)
        except AssertionError:pass
        else:raise AssertionError('malformed source accepted')
    return dict(status='PASS_EXPLICIT_ERASING_TM_NONERASING_BRIDGE',
        loader=loader_ledger(),machine_ledgers=ledgers,block_audit=macro_audit(),
        differential=dict(totals),loader_audit=loader_audit(),
        rejected_malformed_tables=len(invalid),
        scope='Effective finite compiler and paid ordinary-input loader; no fixed universal table or improved universal bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['loader']);print(result['differential']);print(result['scope'])
