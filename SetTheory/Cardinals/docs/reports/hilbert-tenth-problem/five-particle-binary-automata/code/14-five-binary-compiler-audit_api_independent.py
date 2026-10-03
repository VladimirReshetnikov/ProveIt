"""Independent API audit. Checks stay active with python -O."""
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from five_binary import Machine,BinaryCA
from frontend import Frontend,polynomial

ROOT=Path(__file__).parent
counts={}
def inc(k):counts[k]=counts.get(k,0)+1

def require(condition,message):
    if not condition:raise AssertionError(message)

def rejects(label,call,exceptions=(ValueError,TypeError)):
    try:call()
    except exceptions:inc('rejected_invalid_calls');return
    except Exception as exc:raise AssertionError(f'{label}: unexpected {type(exc).__name__}: {exc}') from exc
    raise AssertionError(f'{label}: invalid call was accepted')

def mutation_rejected(label,call):
    rejects(label,call,(TypeError,AttributeError,ValueError))
    inc('mutation_attempts')

def setitem(obj,key,value):obj[key]=value

def run():
    invalid_rows=[
        {'a':[]},{'a':['NOP']},{'a':['NOP','H','extra']},
        {'a':['ADD',True,'H']},{'a':['ADD',False,'H']},
        {'a':['SUB',True,'H','H']},{'a':['SUB',False,'H','H']},
        {'a':['ADD',0.0,'H']},{'a':['SUB',1.0,'H','H']},
        {'a':['ADD',-1,'H']},{'a':['ADD',2,'H']},
        {'a':['ADD',0]},{'a':['ADD',0,'H','extra']},
        {'a':['SUB',0,'H']},{'a':['SUB',0,'H','H','extra']},
        {'a':['UNKNOWN',0,'H']},{'a':'NOP'},
        {'a':['NOP','missing']},{'a':['ADD',0,'missing']},
        {'a':['SUB',0,'H','missing']},{'a':None},
        {'a':['NOP',None]},{'a':['ADD',0,True]},
        {1:['NOP','H']},{'H':['NOP','H']},{'':['NOP','H']},
    ]
    for rows in invalid_rows:rejects(repr(rows),lambda rows=rows:Machine(rows,'a','H'))
    for rows,entry,halt in (([], 'a','H'),({'a':['NOP','H']},None,'H'),
            ({'a':['NOP','H']},'a',None),({'a':['NOP','H']},'missing','H')):
        rejects('source schema',lambda:Machine(rows,entry,halt))
    raw={'a':['ADD',0,'b'],'b':['SUB',0,'H','a'],'n':['NOP','H']}
    m=Machine(raw,'a','H');ca=BinaryCA(m)
    before=(m.step('a',0,0),ca.encode('a',0,0),ca.duration('a',0,0),ca.ledger())
    raw['a'][1]=1;raw['b'][0]='NOP';raw['new']=['NOP','H'];del raw['n']
    after=(m.step('a',0,0),ca.encode('a',0,0),ca.duration('a',0,0),ca.ledger())
    require(before==after,'source caller mutation altered compiled behavior');inc('source_snapshot_checks')
    for label,call in (
        ('machine rows mapping',lambda:setitem(m.rows,'a',('ADD',1,'H'))),
        ('machine row tuple',lambda:setitem(m.rows['a'],1,1)),
        ('machine rows replacement',lambda:setattr(m,'rows',{})),
        ('machine entry replacement',lambda:setattr(m,'entry','H')),
        ('CA codes mapping',lambda:setitem(ca.codes,('H','a'),999)),
        ('CA decode mapping',lambda:setitem(ca.decode,1,('H','H'))),
        ('CA codes replacement',lambda:setattr(ca,'codes',{})),
        ('CA radius replacement',lambda:setattr(ca,'radius',1)),
        ('CA machine replacement',lambda:setattr(ca,'machine',Machine({},'H','H'))),
        ('CA codes deletion',lambda:delattr(ca,'codes')),
        ('CA frozen-flag deletion',lambda:delattr(ca,'_frozen')),
        ('machine rows deletion',lambda:delattr(m,'rows')),
    ):mutation_rejected(label,call)
    require(before==(m.step('a',0,0),ca.encode('a',0,0),ca.duration('a',0,0),ca.ledger()),'mutation test changed compiler')
    bad_numbers=(-1,True,False,0.0,1.5,float('nan'),float('inf'),'1',None,Fraction(1,1))
    for q in ('a','b','n','H'):
        for bad in bad_numbers:
            for a,b in ((bad,0),(0,bad)):
                rejects('Machine.step counters',lambda:m.step(q,a,b))
                rejects('BinaryCA.duration counters',lambda:ca.duration(q,a,b))
                rejects('BinaryCA.encode counters',lambda:ca.encode(q,a,b))
    for q in ('missing',None,True,0,[]):
        for method in (m.step,ca.duration,ca.encode):
            rejects('invalid control',lambda:method(q,0,0))
    invalid_occupancy=([True],[False],[0.0],[1.0],[0,False],[1,True],[0,0.0],
                       [1,1.0],[0,'0'],[None],[-1,-1.0],[Fraction(1,1)])
    for points in invalid_occupancy+([1,1],[0,0],[-1,-1]):
        rejects('step occupancy before dedup',lambda:ca.step(points))
        rejects('local occupancy before dedup',lambda:ca.local(points))
        rejects('components occupancy before dedup',lambda:ca.components(points))
    rejects('local upper radius',lambda:ca.local([ca.radius+1]))
    rejects('local lower radius',lambda:ca.local([-ca.radius-1]))
    require(ca.step([-10**30])=={-10**30},'negative integral coordinates must work')
    require(ca.step(iter([-123]))=={-123},'integral iterator must work')
    require(ca.local([-ca.radius,ca.radius]) in (0,1),'radius endpoints must work')
    # Strict helper and compiled-frontend mutation boundaries.
    rejects('BinaryCA source type',lambda:BinaryCA({}))
    rejects('Frontend CA type',lambda:Frontend({},0))
    for coefficient,monomial in ((True,(0,)),(1.0,(0,)),(1,(True,)),(1,(0.0,)),(1,(-1,))):
        rejects('polynomial exact coefficient/index',lambda:polynomial([(coefficient,monomial)]))
    for points in ([],[1,0],[0,ca.K+1],[0,False],[1,1]):
        rejects('malformed rewrite component',lambda:ca.rewrite(points,lambda x:False))
    for role,q in (('H','a'),('O','H'),('I','n'),(True,'a'),('O',None)):
        rejects('invalid packet direction',lambda:ca.direction(role,q))
    for marker,side,gap in ((True,1,1),(0,True,1),(0,0,1),(0,1,True),(0,1,0),(0,1,ca.D+1)):
        rejects('invalid packet geometry',lambda:ca.pair(marker,side,gap))
    initial=[0,0];sealed=Frontend(ca,2,initial_counters=initial)
    stable=sealed.witness();initial[0]=100
    require(sealed.witness()==stable,'caller initial-counter mutation changed frontend')
    inc('frontend_snapshot_checks')
    for h in (0,2):
        sealed=Frontend(ca,h)
        for label,call in (
            ('frontend names replacement',lambda:setattr(sealed,'names',())),
            ('frontend residual deletion',lambda:delattr(sealed,'residuals')),
            ('frontend frozen-flag deletion',lambda:delattr(sealed,'_frozen')),
            ('frontend control mapping',lambda:setitem(sealed.control,'H',0)),
            ('frontend add variable',lambda:sealed.variable('unpaid')),
            ('frontend add residual',lambda:sealed.add('unpaid',[(1,())])),
        ):mutation_rejected(label,call)
    # Strict front-end boundaries, including horizon-zero/HALT short circuits.
    for h in (-1,True,False,0.0,1.0,'1',None,Fraction(1,1)):
        rejects('frontend horizon',lambda:Frontend(ca,h))
    for h in (0,1):
        for q in ('a','H'):
            for bad in bad_numbers:
                for ab in ((bad,0),(0,bad)):
                    rejects('frontend counters',lambda:Frontend(ca,h,q,ab))
            for ab in ((),(0,),(0,0,0),None,'00'):
                rejects('frontend counter shape',lambda:Frontend(ca,h,q,ab))
    for state in ('missing',True,0,[],{}):
        rejects('frontend state',lambda:Frontend(ca,0,state))
    for value in (0,1,None,'yes',[],{}):
        rejects('frontend clock flag',lambda:Frontend(ca,1,clock=value))
        rejects('frontend real flag',lambda:Frontend(ca,1,nonnegative_real=value))
    # Valid behaviors are compared to the analytical geometric trace oracle.
    from audit_independent import analytic
    for q in ca.states:
        for a in range(3):
            for b in range(3):
                trace=iter(analytic(ca,q,a,b));x=next(trace);ticks=0
                for expected in trace:
                    x=ca.step(x);ticks+=1
                    require(x==expected,'valid microtrace changed after API hardening')
                    require(len(x)==5,'valid microtrace lost mass')
                    inc('valid_microsteps')
                require(ticks==ca.duration(q,a,b),'valid duration changed')
                require(x==ca.encode(*m.step(q,a,b)),'valid source result changed')
                inc('valid_macro_cases')
    # Exact accepted and rejected source horizons under both witness domains.
    for real in (False,True):
        for clock in (False,True):
            for h in range(4):
                f=Frontend(ca,h,initial_counters=(0,0),clock=clock,nonnegative_real=real)
                w=f.witness()
                require((w is not None)==(h==2),'valid frontend acceptance changed')
                if w is not None:
                    require(f.evaluate(w)==0,'valid frontend witness changed')
                    if clock:require(w[f.theta]==sum((ca.duration('a',0,0),ca.duration('b',1,0))),'frontend physical clock changed')
                    for k in range(len(w)):
                        for bad in (float('nan'),float('inf'),-float('inf'),True,False,'1',None,complex(1,0)):
                            altered=w.copy();altered[k]=bad
                            rejects('non-real/nonfinite witness',lambda:f.residual_values(altered))
                inc('valid_frontend_cases')
    real=Frontend(ca,2,nonnegative_real=True)
    require(real.evaluate([Fraction(v) for v in real.witness()])==0,'exact rational real witness rejected')
    report={'status':'passed','optimization_enabled':not __debug__,
        'compiler_sha256':hashlib.sha256((ROOT/'five_binary.py').read_bytes()).hexdigest(),
        'frontend_sha256':hashlib.sha256((ROOT/'frontend.py').read_bytes()).hexdigest(),
        'counts':counts,'assertions_survive_optimization':True}
    name='audit_api_optimized.json' if not __debug__ else 'audit_api_normal.json'
    (ROOT/name).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':run()
