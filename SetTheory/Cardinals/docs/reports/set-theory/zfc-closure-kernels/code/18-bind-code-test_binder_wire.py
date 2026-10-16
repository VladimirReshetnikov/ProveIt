#!/usr/bin/env python3
import argparse
import itertools
import json
from pathlib import Path

import binder_kernel as k
import binder_wire as wire
from test_binder_kernel import make_example,line


def run(output=None,example_path=None):
    doc=make_example(); bits=wire.encode(doc)
    a,lines=wire.check(bits)
    assert len(lines)==8 and not wire.accepts_refutation(bits)
    assert wire.encode(wire.decode(bits))==bits
    rejected=0
    for i in range(len(bits)):
        try: wire.check(bits[:i])
        except k.Invalid: rejected+=1
        else: raise AssertionError(f'truncated example accepted at {i}')
    for junk in (None,'x','2',bits+'0',bits+'1',bits+'\n'):
        assert not wire.accepts_refutation(junk)
    a=k.Arena(); p=a.mem(k.F(0),k.F(1))
    ws=[k.produce(a,p,m) for m in (k.Mode('plug',2,0,3),k.Mode('plug',1,0,4),k.Mode('plug',0,1,4))]
    doc={'formulas':a.nodes,'lines':[line('PSC',[p],ws)]}
    psc_bits=wire.encode(doc); assert len(wire.check(psc_bits)[1])==1
    assert wire.encode(wire.decode(psc_bits))==psc_bits
    tested=valid=refutations=0
    for n in range(1,2**17):
        b=bin(n)[3:]; tested+=1
        try: a,ls=wire.check(b)
        except k.Invalid: continue
        valid+=1; refutations+=bool(ls) and ls[-1]==a.bot
    assert refutations==0
    result={'scope':'finite binary-codec tests and bounded census, not consistency evidence',
            'example_bits':len(bits),'example_lines':8,'example_is_refutation':False,
            'rejected_example_truncations':rejected,'psc_example_bits':len(psc_bits),
            'census_max_bits':16,'census_tested':tested,'census_valid':valid,
            'census_refutations':refutations,'roundtrips_exact':True}
    if output: Path(output).write_text(json.dumps(result,indent=2)+'\n')
    if example_path: Path(example_path).write_text(bits)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--output'); parser.add_argument('--example')
    args=parser.parse_args(); print(json.dumps(run(args.output,args.example),indent=2))
