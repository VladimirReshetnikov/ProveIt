#!/usr/bin/env python3
"""Independent audit: polynomial schema, natural witnesses, CA microstep timing.

Uses frozen producer files, but builds its own source interpreter, expected affine
forms, monomial expansion, natural enumeration, and step-by-step CA simulator.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib, importlib.util, json, random, sys
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args()
SOURCE=args.source_dir.resolve();ROOT=args.output_dir.resolve();ROOT.mkdir(parents=True,exist_ok=True)
def source(name):
    canonical={'certificate_snapshot.py':'certificate.py','ca_snapshot.py':'three_mass_collision_generator.py'}[name]
    path=SOURCE/name
    return path if path.exists() else SOURCE/canonical

def module(name, filename):
    s=importlib.util.spec_from_file_location(name,source(filename))
    m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
C=module('certificate_snapshot','certificate_snapshot.py')
G=module('ca_snapshot','ca_snapshot.py')
I=C.Instruction
report={'status':'RUNNING','source_sha256':{source(n).name:hashlib.sha256(source(n).read_bytes()).hexdigest() for n in ['certificate_snapshot.py','ca_snapshot.py']}}
counts=Counter()

# Own affine arithmetic, schema, and literal ledger; no producer helpers.
def lin(const=0, **kw):
    r=dict(kw)
    if const:r['']=const
    return {k:v for k,v in r.items() if v}
def plus(*aa):
    r=Counter()
    for a in aa:
        for k,v in a.items():r[k]+=v
    return {k:v for k,v in r.items() if v}
def mult(a,m):return {k:v*m for k,v in a.items() if v*m}
def ev(a,x):return sum(c*(x[k] if k else 1) for k,c in a.items())
def value(cert,x):return sum(ev(r['affine'],x)**2 for r in cert['squares'])+sum(ev(r['left'],x)*ev(r['right'],x) for r in cert['products'])
def expanded(cert):
    out=Counter()
    pairs=[(r['affine'],r['affine']) for r in cert['squares']]+[(r['left'],r['right']) for r in cert['products']]
    for left,right in pairs:
        for a,ca in left.items():
            for b,cb in right.items():out[tuple(sorted(z for z in (a,b) if z))]+=ca*cb
    return {k:v for k,v in out.items() if v}
def schema(cert):
    states=cert['machine']['states']; instr=cert['machine']['instructions']; branches=[]
    for j,i in enumerate(instr):
        p=2 if i['counter']==0 else 3
        for r in (list(range(1,p)) if i['operation']=='zero' else [0]):
            branches.append(dict(instruction=j,source=i['source'],target=i['target'],operation=i['operation'],prime=p,residue=r))
    assert cert['branches']==branches
    B,h=len(branches),cert['horizon']; oldq=lin(states.index(cert['initial_state'])); oldN=cert['initial_N']; total={}; squares=[];products=[]
    for t in range(h):
        olds=[];news=[];qs=[];qt=[];es=[];us=[]
        for j,b in enumerate(branches):
            e,u=f'e_{t}_{j}',f'u_{t}_{j}';p=b['prime'];op=b['operation'];E={e:1};U={u:1};S={e:1,u:1};es.append(E);us.append(U)
            if op=='inc':bef=S;aft={e:p,u:p};time={e:108+96*p+8,u:108+96*p}
            elif op=='dec':bef={e:p,u:p};aft=S;time={e:96*p+108+8,u:96*p+108}
            elif op=='positive':bef=aft={e:p,u:p};time={e:192*p+8,u:192*p}
            elif op=='zero':bef=aft={e:b['residue'],u:p};time={e:192*b['residue']+8,u:192*p}
            elif op=='nop':bef=aft=S;time={e:200,u:192}
            else:assert False
            assert cert['steps'][t][j]==dict(branch=j,e=e,u=u,old=bef,new=aft,ticks=time)
            olds.append(bef);news.append(aft);qs.append(mult(E,states.index(b['source'])));qt.append(mult(E,states.index(b['target'])));total=plus(total,time)
        squares += [dict(label=f'step-{t}:one-hot',affine=plus(*es,lin(-1))),dict(label=f'step-{t}:control',affine=plus(*qs,mult(oldq,-1))),dict(label=f'step-{t}:value',affine=plus(*olds,mult(oldN,-1)))]
        for j in range(B):
            products.append(dict(label=f'step-{t}:inactive-{j}',left=plus(*(es[k] for k in range(B) if k!=j)),right=plus(es[j],us[j])))
        oldq=plus(*qt);oldN=plus(*news)
    squares.append(dict(label='terminal:halt',affine=plus(oldq,lin(-states.index(cert['machine']['halt'])))))
    assert [r for r in cert['squares'] if r['label'].startswith(('step-','terminal:halt'))]==squares
    assert cert['products']==products
    assert cert['final_N']==oldN and cert['physical_time']==total
    l=cert['ledger'];load=cert['loader'].get('selector_count',0);ls=3 if load else 0;end=int(cert['output_spec'] is not None)+int(cert['time_spec'] is not None)
    expected=dict(branch_count=B,source_horizon=h,core_variables=2*B*h,input_variables=len(cert['input_variables']),output_variables=len(cert['output_variables']),loader_variables=load,total_variables=2*B*h+len(cert['input_variables'])+len(cert['output_variables'])+load,core_squares=3*h+1,loader_squares=ls,endpoint_squares=end,total_squares=3*h+1+ls+end,product_slots=B*h,maximum_degree=2)
    assert l==expected
    assert len(cert['variables'])==l['total_variables'] and len(set(cert['variables']))==len(cert['variables'])
    p=expanded(cert);q={tuple(r['monomial']):r['coefficient'] for r in C.expand_polynomial(cert)}
    assert p==q and max(map(len,p),default=0)<=2
    assert all(type(c) is int for c in p.values())
    assert all(all(v>=0 for v in r[side].values()) for r in products for side in ('left','right'))
    counts['schema_and_literal_ledger_cases']+=1
    return p

# Independent source execution tracks actual counters and invariant cofactor.
def decode(N):
    a=b=0
    while N%2==0:a+=1;N//=2
    while N%3==0:b+=1;N//=3
    return a,b,N

def source_run(machine,q,N,h):
    a,b,c=decode(N);trace=[]
    for _ in range(h):
        if q==machine.halt:return None
        options=[]
        for idx,ins in enumerate(machine.instructions):
            counter=(a,b)[ins.counter];op=ins.operation
            if ins.source!=q:continue
            if op in ('dec','positive') and counter==0:continue
            if op=='zero' and counter!=0:continue
            options.append((idx,ins))
        if len(options)!=1:return None
        idx,ins=options[0];old=N;cs=[a,b]
        if ins.operation=='inc':cs[ins.counter]+=1
        if ins.operation=='dec':cs[ins.counter]-=1
        a,b=cs;N=c*2**a*3**b
        motion=12*old if ins.operation=='inc' else 12*N if ins.operation=='dec' else 0
        ticks=96*old+96*N+motion+8
        trace.append((q,old,idx,ins.target,N,ticks));q=ins.target
    return trace if q==machine.halt else None

def independent_witness(cert,trace,inputs=None):
    x={k:0 for k in cert['variables']};x.update(inputs or {})
    if cert['input_spec']['mode']=='bounded_counters':
        a=ev(cert['loader']['counter_a'],x);b=ev(cert['loader']['counter_b'],x);x[f'load_{a}_{b}']=1
    for t,(_,old,idx,_,_,_) in enumerate(trace):
        matches=[(j,b) for j,b in enumerate(cert['branches']) if b['instruction']==idx and (b['operation']!='zero' or b['residue']==old%b['prime'])]
        assert len(matches)==1;j,b=matches[0];p=b['prime']
        x[f'e_{t}_{j}']=1
        x[f'u_{t}_{j}']=(old-b['residue'])//p if b['operation']=='zero' else old//p-1 if b['operation'] in ('dec','positive') else old-1
    final=trace[-1][4] if trace else ev(cert['initial_N'],x);ticks=sum(r[5] for r in trace)
    for spec,val,name in [(cert['output_spec'],final,'output_N'),(cert['time_spec'],ticks,'physical_time')]:
        if spec and spec['mode']=='free':x[spec.get('name',name)]=val
    return x

rng=random.Random(20261002)
for op,counter,N,h in product(('inc','dec','positive','zero','nop'),(0,1),range(1,37),range(3)):
    m=C.Machine(('run','halt'),'halt',(I('run','halt',op,counter),))
    cert=C.export_certificate(m,'run',h,{'mode':'fixed_raw','N':N},{'mode':'free'},{'mode':'free'})
    p=schema(cert);trace=source_run(m,'run',N,h)
    if trace is None:
        try:C.make_witness(cert)
        except ValueError:pass
        else:raise AssertionError(('false accepted witness',op,counter,N,h))
        counts['correct_rejected_horizons_or_guards']+=1
    else:
        x=independent_witness(cert,trace);assert C.make_witness(cert)==x and value(cert,x)==C.polynomial_value(cert,x)==0
        for name in cert['variables']:
            y=dict(x);y[name]+=1;assert value(cert,y)>0
            if x[name]>0:y[name]=x[name]-1;assert value(cert,y)>0
        counts['correct_unique_constructed_witnesses']+=1
    for _ in range(2):
        x={v:rng.randint(-3,5) for v in cert['variables']}
        assert value(cert,x)==sum(coef*(__import__('functools').reduce(lambda a,v:a*x[v],mon,1)) for mon,coef in p.items())
        counts['expanded_polynomial_evaluations']+=1

# Finite exhaustive zero enumeration, including all inactive selectors and bases.
brute=[]
for prime in (2,3):
    counter=prime-2
    m=C.Machine(('run','halt'),'halt',(I('run','halt','zero',counter),I('run','halt','positive',counter)))
    for N in range(1,8):
        cert=C.export_certificate(m,'run',1,{'mode':'fixed_raw','N':N});schema(cert)
        zeros=[]
        for vals in product(range(4),repeat=len(cert['variables'])):
            x=dict(zip(cert['variables'],vals));counts['exhaustive_natural_assignments']+=1
            if value(cert,x)==0:zeros.append(x)
        expected=independent_witness(cert,source_run(m,'run',N,1))
        assert zeros==[expected],(prime,N,zeros,expected)
        brute.append({'prime':prime,'N':N,'variables':len(cert['variables']),'box_max':3,'zeros':len(zeros)})
m=C.Machine(('a','b','halt'),'halt',(I('a','b','inc',0),I('b','halt','dec',0)))
for N in (1,2):
    cert=C.export_certificate(m,'a',2,{'mode':'fixed_raw','N':N});schema(cert);zeros=[]
    for vals in product(range(3),repeat=len(cert['variables'])):
        x=dict(zip(cert['variables'],vals));counts['exhaustive_natural_assignments']+=1
        if value(cert,x)==0:zeros.append(x)
    assert zeros==[independent_witness(cert,source_run(m,'a',N,2))]
report['exhaustive_zero_fibers']=brute

# Literal mixed fixture: nine source instructions, ten residue-expanded branches.
mixed=C.Machine(tuple([f'q{i}' for i in range(9)]+['halt']),'halt',tuple(I(f'q{i}',f'q{i+1}' if i<8 else 'halt',op,c) for i,(op,c) in enumerate([('inc',0),('inc',1),('positive',0),('positive',1),('dec',0),('dec',1),('zero',0),('zero',1),('nop',0)])))
cert=C.export_certificate(mixed,'q0',9,{'mode':'fixed_raw','N':1},{'mode':'free'},{'mode':'free'});p=schema(cert);w=independent_witness(cert,source_run(mixed,'q0',1,9));assert C.make_witness(cert)==w
(ROOT/'literal-mixed-certificate.json').write_text(json.dumps(cert,indent=2)+'\n');(ROOT/'literal-mixed-witness.json').write_text(json.dumps(w,indent=2)+'\n')
report['literal_mixed_ledger']=cert['ledger'];report['literal_mixed_final_N']=w['output_N'];report['literal_mixed_microtime']=w['physical_time'];report['literal_mixed_expanded_terms']=len(p)

# h=0: only the initial halt is legal; empty instruction set is supported.
for q,h,N in product(('run','halt'),range(3),(1,5,12)):
    m=C.Machine(('run','halt'),'halt',());cert=C.export_certificate(m,q,h,{'mode':'fixed_raw','N':N},{'mode':'free'},{'mode':'free'});schema(cert)
    if q=='halt' and h==0:
        w=C.make_witness(cert);assert w=={'output_N':N,'physical_time':0} and value(cert,w)==0
    else:
        try:C.make_witness(cert)
        except ValueError:pass
        else:assert False
    counts['empty_program_h0_cases']+=1

# Paid bounded loader and raw coordinates; free outputs are unique as well.
loader_ledgers=[]
m=C.Machine(('run','halt'),'halt',(I('run','halt','nop',0),))
for A,B in product(range(3),range(3)):
    cert=C.export_certificate(m,'run',1,{'mode':'bounded_counters','A':A,'B':B},{'mode':'free'},{'mode':'free'});schema(cert);loader_ledgers.append(cert['ledger'])
    for a,b in product(range(A+1),range(B+1)):
        inputs={'input_a':a,'input_b':b};N=2**a*3**b;w=independent_witness(cert,source_run(m,'run',N,1),inputs)
        assert C.make_witness(cert,inputs)==w and value(cert,w)==0;counts['bounded_loader_witnesses']+=1
    for bad in ({'input_a':A+1,'input_b':0},{'input_a':0,'input_b':B+1}):
        try:C.make_witness(cert,bad)
        except ValueError:pass
        else:assert False
cert=C.export_certificate(m,'run',1,{'mode':'free_raw','name':'x'},{'mode':'free'},{'mode':'free'});schema(cert)
for x in range(40):
    w=C.make_witness(cert,{'x':x});N=x+1;assert w==independent_witness(cert,source_run(m,'run',N,1),{'x':x});counts['free_raw_witnesses']+=1
report['loader_ledger_A2_B2']=loader_ledgers[-1]

# Compiler rejection checks, separated syntax both directions and numeric modes.
def rejects(label,f,exc=ValueError):
    try:f()
    except exc:counts['validation_rejections']+=1;return
    raise AssertionError(('missing rejection',label))
for label,machine in [
 ('empty states',C.Machine((),'halt',())),('duplicate states',C.Machine(('a','a','halt'),'halt',())),('missing halt',C.Machine(('a',),'halt',())),
 ('unknown source',C.Machine(('a','halt'),'halt',(I('b','halt','nop'),))),('unknown target',C.Machine(('a','halt'),'halt',(I('a','b','nop'),))),
 ('halt outgoing',C.Machine(('a','halt'),'halt',(I('halt','a','nop'),))),('bad operation',C.Machine(('a','halt'),'halt',(I('a','halt','INC'),))),('bad counter',C.Machine(('a','halt'),'halt',(I('a','halt','inc',2),))),
 ('forward motion overlap',C.Machine(('a','b','halt'),'halt',(I('a','b','inc'),I('a','halt','zero')))),
 ('inverse motion overlap',C.Machine(('a','b','halt'),'halt',(I('a','halt','inc'),I('b','halt','zero')))),
 ('forward different counter tests',C.Machine(('a','b','halt'),'halt',(I('a','b','zero',0),I('a','halt','positive',1)))),
 ('inverse different counter tests',C.Machine(('a','b','halt'),'halt',(I('a','halt','zero',0),I('b','halt','positive',1)))),
 ('forward same guard',C.Machine(('a','b','halt'),'halt',(I('a','b','zero'),I('a','halt','zero')))),
 ('inverse same guard',C.Machine(('a','b','halt'),'halt',(I('a','halt','zero'),I('b','halt','zero'))))]:rejects(label,machine.validate)
base=C.Machine(('run','halt'),'halt',(I('run','halt','nop'),))
for h in (-1,1.0,True):rejects('horizon',lambda h=h:C.export_certificate(base,'run',h,{'mode':'fixed_raw','N':1}))
for N in (0,-1,1.0,True):rejects('raw N',lambda N=N:C.export_certificate(base,'run',1,{'mode':'fixed_raw','N':N}))
for spec in ({'mode':'unknown'},{'mode':'bounded_counters','A':-1,'B':1},{'mode':'bounded_counters','A':1,'B':False},{'mode':'bounded_counters','A':1,'B':1,'a':-1},{'mode':'free_raw','name':'e_0_0'},{'mode':'free_raw','name':''}):rejects('input specification',lambda spec=spec:C.export_certificate(base,'run',1,spec))
rejects('unknown initial state',lambda:C.export_certificate(base,'unknown',1,{'mode':'fixed_raw','N':1}))
for endpoint in ({'mode':'unknown'},{'mode':'fixed','value':-1},{'mode':'fixed','value':True},{'mode':'free','name':'u_0_0'}):rejects('endpoint specification',lambda endpoint=endpoint:C.export_certificate(base,'run',1,{'mode':'fixed_raw','N':1},endpoint))
cert=C.export_certificate(base,'run',1,{'mode':'fixed_raw','N':1})
for x in ({},{'e_0_0':1,'u_0_0':0,'extra':0},{'e_0_0':1,'u_0_0':-1},{'e_0_0':True,'u_0_0':0},{'e_0_0':1,'u_0_0':Fraction(1,2)}):rejects('natural domain',lambda x=x:C.polynomial_value(cert,x))
for endpoint in ('output','time'):
    args=({'mode':'fixed','value':2},None) if endpoint=='output' else (None,{'mode':'fixed','value':201})
    cert=C.export_certificate(base,'run',1,{'mode':'fixed_raw','N':1},*args)
    rejects('wrong fixed endpoint',lambda:C.make_witness(cert))

# Explicit rational false positive: zero-test of counter 0 at raw N=2.
m=C.Machine(('run','halt'),'halt',(I('run','halt','zero',0),));cert=C.export_certificate(m,'run',1,{'mode':'fixed_raw','N':2},{'mode':'fixed','value':2},{'mode':'fixed','value':392})
x={'e_0_0':Fraction(1),'u_0_0':Fraction(1,2)};assert value(cert,x)==0 and C.polynomial_value(cert,x,allow_rational=True)==0
rejects('rational false positive domain',lambda:C.polynomial_value(cert,x));rejects('zero test incorrectly enabled',lambda:C.make_witness(cert))
report['rational_false_positive']={'operation':'zero counter 0','initial_N':2,'assignment':{k:str(v) for k,v in x.items()},'polynomial_value':0,'why_invalid':'v2(2)=1, so the zero-test is disabled; natural integrality is essential'}

# Independent simulator applies raw local maps and channel shifts, never step()/ready().
def physical_step(ca,conf):
    cells=defaultdict(list)
    for pos,typ in conf:cells[pos].append(typ)
    result=[]
    for pos,tt in cells.items():
        assert len(tt)<=2 and len(tt)==len(set(tt))
        if len(tt)==1:out=[ca.single[tt[0]]]
        else:
            pair=tuple(sorted(tt));assert pair in ca.specified_pairs;out=ca.pairs[pair]
        result.extend((pos+ca.velocity[t],t) for t in out)
    assert len(result)==3 and len(set(result))==3
    return tuple(sorted(result))
def read_section(ca,conf):
    names=[(pos,ca.names[t]) for pos,t in conf]
    right=[pos for pos,name in names if name==('R',)]
    sh=[pos for pos,name in names if name==('S',0)]
    left=[(pos,name[2]) for pos,name in names if name[:2]==('L',0) and name[2][1:]==(0,0)]
    if not (right==[0] and len(sh)==len(left)==1 and sh[0]==left[0][0]):return None
    pos,(q,_,_)=left[0];assert pos<0 and (-pos)%12==0
    return q,-pos//12
micro=[]
for op,counter in product(('inc','dec','positive','zero','nop'),(0,1)):
    m=C.Machine(('run','halt'),'halt',(I('run','halt',op,counter),));ca=G.ThreeMassCA(m.states,m.halt,[G.Instruction('run','halt',op,counter)])
    for N in range(1,25):
        trace=source_run(m,'run',N,1)
        if trace is None:continue
        expected=trace[0][5];finalN=trace[0][4];conf=ca.initial('run',N)
        for tick in range(1,expected+1):
            conf=physical_step(ca,conf);section=read_section(ca,conf)
            if tick<expected:assert section is None,(op,counter,N,tick,section)
            else:assert section==('halt',finalN)
        counts['actual_microstep_runs']+=1;counts['actual_microsteps']+=expected
        micro.append({'operation':op,'prime':2+counter,'initial_N':N,'final_N':finalN,'first_committed_halt_tick':expected})
    del ca
# Whole mixed instruction chain, including p=3 residue 2 through raw cofactor 5.
ca=G.ThreeMassCA(mixed.states,mixed.halt,[G.Instruction(i.source,i.target,i.operation,i.counter) for i in mixed.instructions])
for N in (1,5,7):
    trace=source_run(mixed,'q0',N,9);assert trace is not None
    conf=ca.initial('q0',N);total=0
    for oldq,oldN,idx,newq,newN,duration in trace:
        for tick in range(1,duration+1):
            conf=physical_step(ca,conf)
            assert read_section(ca,conf)==((newq,newN) if tick==duration else None)
        total+=duration;counts['actual_microsteps']+=duration;counts['actual_microstep_runs']+=1
    cert=C.export_certificate(mixed,'q0',9,{'mode':'fixed_raw','N':N},{'mode':'free'},{'mode':'free'});w=C.make_witness(cert)
    assert w['physical_time']==total and w['output_N']==N
    counts['whole_physical_trajectories']+=1
# Both underflows: exact escape entry and subsequent drift never create Ready.
traps=[]
for counter in (0,1):
    ca=G.ThreeMassCA(('run','halt'),'halt',[G.Instruction('run','halt','dec',counter)])
    for N in (1,5,7):
        conf=ca.initial('run',N);escape_tick=96*N+5
        for tick in range(1,escape_tick+1001):
            conf=physical_step(ca,conf);assert read_section(ca,conf) is None
            names=[(pos,ca.names[t]) for pos,t in conf]
            if tick==escape_tick:
                assert any(name==('trap',('run',0,0)) and pos==-12*N for pos,name in names)
                assert any(name==('escape',) and pos==-12*N-1 for pos,name in names)
            if tick>escape_tick:
                assert any(name==('escape',) and pos==-12*N-1-(tick-escape_tick) for pos,name in names)
        traps.append({'prime':2+counter,'N':N,'escape_tick':escape_tick,'post_escape_ticks':1000})
        counts['actual_microsteps']+=escape_tick+1000
report['microstep_cases']=micro;report['underflow_traps']=traps
report['counts']=dict(counts);report['status']='PASS'
(ROOT/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('microstep_cases','exhaustive_zero_fibers')},indent=2))
