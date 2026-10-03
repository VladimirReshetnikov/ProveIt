"""Portable API, dependency-pin, source-count, and immutable-snapshot checks."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import lazy_reversible as lazy

ROOT = Path(__file__).resolve().parent
CORE = '42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'
SOURCE = 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'
checks = []

def require(ok, detail):
    if not ok:
        raise RuntimeError(detail)
    checks.append(detail)

def rejects(fn, label, expected=(TypeError, ValueError, AttributeError)):
    try:
        fn()
    except expected:
        checks.append(label)
    else:
        raise RuntimeError('Accepted invalid operation: '+label)

class SetSubclass(set): pass
class FrozenSubclass(frozenset): pass
class IntSubclass(int): pass
class StrSubclass(str): pass
class GateSubclass(lazy.ref.Gate): pass

def main():
    require(hashlib.sha256((ROOT/'lazy_reversible.py').read_bytes()).hexdigest()==CORE,'exact evaluator pin')
    source=dict(schema='reversible-two-counter-v1',controls=['q','h'],start='q',halt='h',class_cut=0,
                branches=[dict(name='e',source='q',target='h',side=1,delta=1,guard={'op':'true'})])
    rule=lazy.compile_lazy_source(source)
    g=rule.gate_at(0)
    bad_positions=[[],(),{},None,False,1,'0',SetSubclass({0}),FrozenSubclass({0}),{True},{1.0},{IntSubclass(0)}]
    methods=[('step',lambda x:rule.step(x)),('candidate_indices',lambda x:rule.candidate_indices(x)),
             ('apply_gate',lambda x:lazy.apply_gate(g,x))]
    for name,fn in methods:
        for j,x in enumerate(bad_positions):
            rejects(lambda fn=fn,x=x:fn(x),name+' position type '+str(j))
    for name in ('inverse','verify','trace'):
        for j,value in enumerate((0,1,None,'False',[],IntSubclass(0))):
            rejects(lambda name=name,value=value:rule.step(set(),**{name:value}),'step flag '+name+' '+str(j))
    for j,value in enumerate((0,1,None,[],IntSubclass(0))):
        rejects(lambda value=value:lazy.apply_gate(g,set(),value),'apply_gate verify '+str(j))
    for j,value in enumerate((True,False,1.0,'0',None,IntSubclass(0),-1,rule.factors)):
        rejects(lambda value=value:rule.gate_at(value),'factor index '+str(j))
    for j,value in enumerate((True,1.0,None,IntSubclass(0),-1)):
        for side in (0,1):
            args=['q',0,0];args[side+1]=value
            rejects(lambda args=args:rule.encode(*args),'encoder counter '+str(side)+' '+str(j))
    for j,value in enumerate((None,True,StrSubclass('q'),'missing')):
        rejects(lambda value=value:rule.encode(value,0,0),'encoder control '+str(j))
    for j,value in enumerate((None,True,StrSubclass('+'),'x')):
        rejects(lambda value=value:rule.encode('q',0,0,value),'encoder sign '+str(j))
    for cls in (lazy.LazySource,lazy.ref.Branch,lazy.ref.Gate,lazy.ref._ClassGuard):
        rejects(lambda cls=cls:cls(),'private direct constructor '+cls.__name__)
    for j,value in enumerate((object(),object.__new__(GateSubclass))):
        rejects(lambda value=value:lazy.apply_gate(value,set()),'exact frozen Gate '+str(j))
    for name,fn in methods:
        for x in (set(),frozenset(),{-(1<<1024),1<<1024}):
            result=fn(x)
            require(result is not None,name+' accepted exact support '+str(len(x)))
    y,stats=rule.step({-118,-112,0,18,23},trace=True,verify=True)
    require(type(y) is frozenset,'result exact frozenset')
    require(tuple(event[0] for event in stats['events'])==(0,1,47,60),'cascade indices')
    require(y==frozenset((-119,-113,0,19,24)),'cascade output')
    mutations=[lambda:setattr(rule,'D',0),lambda:rule.control_index.__setitem__('q',3),
               lambda:rule.home_out.__setitem__(0,()),lambda:rule.home_in.__setitem__(0,()),
               lambda:rule.source_data.__setitem__('class_cut',4),
               lambda:rule.source_data['branches'][0].__setitem__('delta',0),
               lambda:rule.source_data['branches'][0]['guard'].__setitem__('op','false'),
               lambda:setattr(rule.branches[0],'delta',0),lambda:setattr(g,'B',0),
               lambda:stats.__setitem__('tested_factors',0)]
    for j,fn in enumerate(mutations): rejects(fn,'immutable object '+str(j))
    before=rule.source_data
    source['controls'][0]='changed';source['branches'][0]['guard']['op']='false';source['branches'].clear()
    require(rule.source_data['controls'][0]=='q' and len(rule.branches)==1,'snapshot independent of original containers')
    ledger=rule.ledger();ledger['D']=-1;ledger['alphabet'].append(9)
    require(rule.D==8 and rule.ledger()['alphabet']==[0,1],'ledger detached values')
    require(rule.step(set())==frozenset() and rule.step(set(),inverse=True)==frozenset(),'empty support both directions')
    with tempfile.TemporaryDirectory(prefix='pin-check-') as td:
        d=Path(td)
        (d/'lazy_reversible.py').write_bytes((ROOT/'lazy_reversible.py').read_bytes())
        (d/'frozen_reversible_binary.py').write_bytes(b"print('UNVERIFIED_REFERENCE_EXECUTED')\n"+(ROOT/'frozen_reversible_binary.py').read_bytes())
        mode=['-O'] if sys.flags.optimize else []
        run=subprocess.run([sys.executable,*mode,'-E','-s','-B','-c','import lazy_reversible'],cwd=d,capture_output=True,text=True)
        require(run.returncode!=0 and 'Frozen compiler dependency has changed' in run.stderr,'tampered reference rejected before execution')
        require('UNVERIFIED_REFERENCE_EXECUTED' not in run.stdout,'tampered reference side effect absent')
    raw=(ROOT/'source.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==SOURCE,'exact decompressed source pin')
    data=json.loads(raw);m=len(data['controls']);p=sum(r['delta']!=0 for r in data['branches']);a=len(data['branches'])-p;J=data['class_cut'];D=2*m+4*p
    count=dict(m=m,p=p,a=a,J=J,D=D,E=p*(4*D+15)+a,P=p*(4*D+14)+m,factors=8*p*D+29*p+m+a)
    require((m,p,a,J,count['factors'])==(122622,66066,75495,0,269291358255),'independent universal table count')
    receipt=dict(status='passed',optimization_level=sys.flags.optimize,evaluator_sha256=CORE,compiler_sha256=lazy.FROZEN_SHA256,source_sha256=SOURCE,checks=len(checks),check_labels=checks,independent_ledger=count)
    target='package-receipt-optimized.json' if sys.flags.optimize else 'package-receipt.json'
    (ROOT/target).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='check_labels'},indent=2))

if __name__=='__main__': main()
