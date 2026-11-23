#!/usr/bin/env python3
"""Canonical numerical machine codec and independent sparse-tape checks.

No external packages. Run: python3 code/machine_checks.py
These finite implementation checks are not Lean/object-iPRA certificates and
Python integer digit operations are not claimed to be unit-cost TM steps.
"""
from dataclasses import dataclass, replace
from itertools import product
from random import Random
import json


def word(bits):
    assert all(b in (0,1) for b in bits)
    return (1 << len(bits)) + sum(b << i for i,b in enumerate(bits))

def word_bits(x):
    assert x >= 1
    return [(x >> i) & 1 for i in range(x.bit_length()-1)]

def width(q): return (27*q-1).bit_length()

def encode_rule(rule):
    state,symbol,imove,wmove=rule
    return 27*state+9*symbol+3*imove+wmove

def decode_rule(r): return (r//27,(r//9)%3,(r//3)%3,r%3)

def encode_machine(q,rules):
    assert q>=3 and len(rules)==12*q
    fields=[encode_rule(r) for r in rules]
    assert all(0<=r<27*q for r in fields)
    w=width(q)
    return word([1]*(q-3)+[0]+[(r>>i)&1 for r in fields for i in range(w)])

def decode_machine(e):
    if e<1: return None
    n=e.bit_length()-1
    j=0
    while j<n and ((e>>j)&1): j+=1
    if j==n: return None
    q=j+3; w=width(q)
    if n != q-2+12*q*w: return None
    mask=(1<<w)-1
    rules=[(e>>(q-2+i*w))&mask for i in range(12*q)]
    return (q,rules) if all(r<27*q for r in rules) else None

@dataclass(frozen=True)
class Config:
    state: int=2
    input_head: int=0
    work_head: int=0
    tape: int=0

REJECT=Config(0,0,0,0)

def move(h,d): return max(0,h-1) if d==0 else h if d==1 else h+1

def packed_step(machine,x,c,budget=None):
    q,rules=machine
    n=x.bit_length()-1
    if budget is not None and c.work_head>=budget: return REJECT
    if c.state<2: return c
    if c.state>=q or c.input_head>n+1: return REJECT
    a=0 if c.input_head==0 else 3 if c.input_head==n+1 else 1+((x>>(c.input_head-1))&1)
    power=3**c.work_head; b=(c.tape//power)%3
    state,symbol,imove,wmove=decode_rule(rules[12*c.state+3*a+b])
    out=Config(state,min(n+1,move(c.input_head,imove)),move(c.work_head,wmove),
               c.tape-b*power+symbol*power)
    return REJECT if budget is not None and out.work_head>=budget else out

def run(e,x,t,budget=None):
    machine=decode_machine(e)
    if machine is None or x<1 or budget==0: return REJECT
    c=Config()
    for _ in range(t):
        c=packed_step(machine,x,c,budget)
        if c.state<2: break  # justified by absorption
    return c

def config_bound(e,x,s):
    machine=decode_machine(e)
    q=machine[0] if machine is not None else 3
    n=x.bit_length()-1 if x>=1 else 0
    return (q+2)*(n+2)*(s+1)*3**s

def space_accept(e,x,s): return run(e,x,config_bound(e,x,s),s).state==1

# Independent reference: table entries remain four-tuples; tape is a dictionary,
# input is a list with explicit sentinels; no packed-digit read/write is used.
def sparse_run(q,table,bits,t,budget=None):
    state,ih,wh=2,0,0
    tape={}
    stream=[0]+[1+b for b in bits]+[3]
    if budget==0: return REJECT
    for _ in range(t):
        if state in (0,1): break
        nxt,symbol,imove,wmove=table[state*12+stream[ih]*3+tape.get(wh,0)]
        if symbol: tape[wh]=symbol
        else: tape.pop(wh,None)
        if imove==0 and ih>0: ih-=1
        elif imove==2 and ih+1<len(stream): ih+=1
        if wmove==0 and wh>0: wh-=1
        elif wmove==2: wh+=1
        if budget is not None and wh>=budget: return REJECT
        state=nxt
    packed=sum(symbol*3**position for position,symbol in tape.items())
    return Config(state,ih,wh,packed)

def self_description(e,c,k):
    assert e>=1 and c>=1 and k>=0
    bits=word_bits(e)
    return word([1]*len(bits)+[0]+bits+[1]*c+[0]+[1]*k+[0])

def parse_description(x):
    if x<1: return None
    bits=word_bits(x); end=len(bits)
    def unary_at(i):
        start=i
        while i<end and bits[i]==1: i+=1
        return None if i==end else (i-start,i+1)
    first=unary_at(0)
    if first is None: return None
    m,i=first
    if i+m>end: return None
    e=word(bits[i:i+m]); second=unary_at(i+m)
    if second is None: return None
    c,i=second; third=unary_at(i)
    if third is None: return None
    k,i=third
    return (e,c,k) if c>=1 and i==end else None

def diagonal(x):
    parsed=parse_description(x)
    if parsed is None: return False
    e,c,k=parsed
    n=x.bit_length()-1
    return run(e,x,c*(n+1)**k).state!=1

def check_all():
    stats={}; rng=Random(20261122)
    rules_checked=0
    for q in range(3,8):
        for rule in product(range(q),range(3),range(3),range(3)):
            r=encode_rule(rule)
            assert r<27*q and decode_rule(r)==rule
            rules_checked+=1
    stats['rule_codec_roundtrips']=rules_checked
    machines=[]
    for q in range(3,8):
        for _ in range(20):
            table=[(rng.randrange(q),rng.randrange(3),rng.randrange(3),rng.randrange(3))
                   for _ in range(12*q)]
            e=encode_machine(q,table)
            decoded=decode_machine(e)
            assert decoded==(q,list(map(encode_rule,table)))
            assert e.bit_length()-1==(q-2)+12*q*width(q)
            assert encode_machine(q,list(map(decode_rule,decoded[1])))==e
            machines.append((q,table,e))
    # Include head motion, all halting states, all write symbols, and all moves
    # exhaustively for homogeneous three-state tables.
    for rule in product(range(3),range(3),range(3),range(3)):
        table=[rule]*36; machines.append((3,table,encode_machine(3,table)))
    stats['machine_codec_roundtrips']=100
    stats['distinct_machine_tables_tested']=len(machines)
    words=[list(bits) for n in range(4) for bits in product((0,1),repeat=n)]
    comparisons=0
    for q,table,e in machines:
        for bits in words:
            x=word(bits)
            assert word_bits(x)==bits
            for t in (0,1,2,5,12):
                for budget in (None,0,1,2,4):
                    got=run(e,x,t,budget)
                    expected=sparse_run(q,table,bits,t,budget)
                    assert got==expected,(q,bits,t,budget,got,expected)
                    if budget is not None and budget>0:
                        assert got.work_head<budget and got.tape<3**budget
                    comparisons+=1
    stats['packed_vs_sparse_configuration_comparisons']=comparisons
    # Check numeral writeback against an unrelated digit-vector update.
    writes=0
    for tape in range(3**5):
        for h in range(7):
            digits=[(tape//(3**i))%3 for i in range(7)]
            for symbol in range(3):
                expected=digits.copy(); expected[h]=symbol
                got=tape-((tape//3**h)%3)*3**h+symbol*3**h
                assert got==sum(d*3**i for i,d in enumerate(expected))
                writes+=1
    stats['ternary_write_checks']=writes
    invalid=[0,1,word([1]),word([0]),word([1]*20)]
    e=machines[0][2]; payload=word_bits(e)
    invalid.extend((word(payload[:-1]),word(payload+[0])))
    q=machines[0][0]; w=width(q); bad=payload.copy()
    bad[q-2:q-2+w]=[(27*q>>i)&1 for i in range(w)]
    invalid.append(word(bad))
    for e in invalid:
        assert decode_machine(e) is None
        for t in (0,1,5): assert run(e,word([1,0]),t)==REJECT
    stats['invalid_machine_encodings_rejected']=len(invalid)
    for _,_,e in machines[:5]: assert run(e,0,5)==REJECT
    # The all-right, accepting rule must reject when it escapes the budget.
    escape=encode_machine(3,[(1,2,1,2)]*36)
    assert run(escape,word([]),1,1)==REJECT
    assert run(escape,word([]),1,2).state==1
    # Configuration clocks agree with a separately detected first repeated
    # sparse record for small budgets; packed run is not the reference logic.
    space_cases=0
    for q,table,e in machines[::11]:
        for bits in words[:7]:
            for s in (1,2):
                seen=set(); expected=False
                for t in range(config_bound(e,word(bits),s)+1):
                    c=sparse_run(q,table,bits,t,s)
                    if c.state==1: expected=True; break
                    if c.state==0 or c in seen: break
                    seen.add(c)
                assert space_accept(e,word(bits),s)==expected
                space_cases+=1
    stats['space_clock_vs_independent_cycle_checks']=space_cases
    desc_checks=0; demonstrations=[]
    for _,_,e in machines[:3]+[(3,[],1)]:
        for c,k in ((1,0),(2,0),(1,1)):
            x=self_description(e,c,k); n=x.bit_length()-1
            assert parse_description(x)==(e,c,k)
            assert n==2*(e.bit_length()-1)+c+k+3
            candidate=run(e,x,c*(n+1)**k).state==1
            value=diagonal(x)
            assert value!=candidate
            demonstrations.append({'input_length':n,'coefficient':c,'exponent':k,
                                   'clock':c*(n+1)**k,'candidate':candidate,'diagonal':value})
            assert parse_description(word(word_bits(x)+[0])) is None
            desc_checks+=1
    stats['self_description_roundtrips_and_diagonal_mismatches']=desc_checks
    stats['diagonal_examples']=demonstrations
    stats['status']='PASS'
    return stats

if __name__=='__main__':
    print(json.dumps(check_all(),indent=2,sort_keys=True))
