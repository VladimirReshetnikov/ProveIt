#!/usr/bin/env python3
"""Exact finite counterexample to the first, rejected 245-state emission.

The claim refuted is its universal one-instruction source simulation, not
its consistency-equivalence on the blank tape, which has not been decided.
"""
import json, hashlib
import compile_rebracket as c

lit=c.module(c.BASE/'code/check_literal_instructions.py')

def parse_frame(q,h,ones):
    if q!=96 or not ones or min(ones)!=h-1:return None
    choices=[p for p in ones if p>=h+36]
    if not choices:return None
    header=min(choices)
    if header-h<40:return None
    pos=header+1;values=[]
    while pos<=max(ones):
        if pos in ones or pos+1 not in ones:return None
        start=pos+1;pos=start
        while pos in ones:pos+=1
        values.append(pos-start-1)
    if len(values)<10:return None
    return dict(head=h,header_distance=header-h,pc=''.join(str(int(p in ones)) for p in range(h,header)).rstrip('0'),physical_registers=values[:9],spares=values[9:])

def main():
    table_path=c.HERE/'rebracket245_first.tm';t=lit.read_table(table_path)
    pc='11101001001010100111000000';op='CD';logical_register=1
    physical=[1,0,0,0,0,0,0,0,0];spares=[0];h=0;span=40
    expected=lit.expected(pc,op,logical_register,physical,spares,h,span)
    ones=lit.paint(pc,span,physical,spares,h);q=96
    for steps in range(1,100001):
        w,d,q=t[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
        frame=parse_frame(q,h,ones)
        if frame is not None:break
    else:raise AssertionError('No complete frame in the prescribed finite window')
    assert (h,ones)!=(expected[0],expected[1])
    out=dict(status='COUNTEREXAMPLE',refuted='The inherited first-complete-frame instruction contract of the direct245 emission.',
        blank_tape_halting_claim='Not decided by this test.',table_sha256=hashlib.sha256(table_path.read_bytes()).hexdigest(),
        initial=dict(pc=pc,logical_operation='decrement T',physical_registers=physical,spares=spares,head=0,header_distance=40),
        expected=dict(head=expected[0],pc=expected[2].rstrip('0'),header_distance=expected[3],physical_registers=expected[4],spares=expected[5]),
        actual=dict(steps=steps,**frame),actual_one_cells=sorted(ones),expected_one_cells=sorted(expected[1]))
    (c.HERE/'literal_rebracket_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if not k.endswith('_cells')},indent=2))

if __name__=='__main__':main()
