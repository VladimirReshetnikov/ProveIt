"""Public ParallelCompiler API contract regression, including python -O."""
import argparse
from dataclasses import FrozenInstanceError
import json
from pathlib import Path
import sys
from parallel_particles import ParallelCompiler


def check(x, detail):
    if not x: raise RuntimeError(detail)


def rejects(fn, expected=TypeError):
    try:fn()
    except expected:return
    raise RuntimeError('Invalid input unexpectedly accepted')


def source():
    return dict(schema='reversible-two-counter-v1',controls=['q','h'],start='q',halt='h',class_cut=0,
                branches=[dict(name='e',source='q',target='h',side=1,delta=1,guard={'op':'true'})])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    data=source(); c=ParallelCompiler(data); x=c.old.encode('q',0,0); want=c.step(x)
    failures=0
    class IntSubclass(int):pass
    for invalid in [[],tuple(x),iter(x),None,'123',{True},{False},{1.0},{IntSubclass(1)},{'1'}]:
        rejects(lambda invalid=invalid:c.step(invalid));failures+=1
        rejects(lambda invalid=invalid:c.E.apply(invalid));failures+=1
        rejects(lambda invalid=invalid:c.P.local_output(invalid));failures+=1
    for invalid in [0,1,None,'true',[],1.0]:
        rejects(lambda invalid=invalid:c.step(x,inverse=invalid));failures+=1
        rejects(lambda invalid=invalid:c.step(x,verify=invalid));failures+=1
        rejects(lambda invalid=invalid:c.E.apply(x,verify=invalid));failures+=1
    for invalid in [True,0.0,IntSubclass(0),'0']:
        rejects(lambda invalid=invalid:c.P.local_output(x,invalid));failures+=1
    mutable=set(x); y=c.step(mutable); mutable.clear()
    check(y==want and type(y) is frozenset,'input alias retained')
    data['controls'].append('extra');data['branches'][0]['guard']['op']='false'
    check(c.step(x)==want and c.old.controls==('q','h'),'source alias retained')
    for target,name,value in [(c,'radius',0),(c,'E',None),(c.E,'r',0),
                              (c.E.patterns[0],'P',frozenset()),(c.E.patterns[-1].guard,'Z',0)]:
        rejects(lambda target=target,name=name,value=value:setattr(target,name,value),FrozenInstanceError)
        failures+=1
    ledger=c.ledger();ledger['radius']=0
    check(c.ledger()['radius']!=0,'ledger mutation affected rule')
    check(c.step(want,inverse=True,verify=True)==x,'valid inverse')
    bad=source();bad['class_cut']=True
    rejects(lambda:ParallelCompiler(bad));failures+=1
    out=dict(status='passed',invalid_input_or_mutation_rejections=failures,
             public_entry_point='ParallelCompiler',finite_support='set/frozenset of exact Python ints',
             flags='exact bool',source_snapshots_immutable=True,
             generic_custom_guards='internal harness contract; not public source API')
    print(json.dumps(out,indent=2))
    (args.output_dir/('api-receipt-optimized.json' if sys.flags.optimize else 'api-receipt.json')).write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
