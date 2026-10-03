#!/usr/bin/env python3
"""Exact local Grill Tag arithmetic and finite-history scout; no universal bound.

Uses an independently specified string oracle, literal +,-,* DAGs and integers.
No downloaded code is imported. All program coefficients are fixed numerals.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path


def need(ok,msg):
    if not ok: raise ValueError(msg)


def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def macro(w,n):
    need(type(w) is str and set(w)<=set('01'),'binary string')
    need(type(n) is int and n>=0,'natural exponent')
    if not w: return None
    return w[1:]+('0'+'10'*n if w[0]=='1' else '')


def micro(w,command):
    need(command in ('10','11'),'command')
    if not w:return None
    if command=='10':return w[1:]+('0' if w[0]=='1' else '')
    return w+('01' if w[0]=='1' else '')


def encode(w):
    return 1<<len(w), sum(int(b)<<i for i,b in enumerate(w))


def decode(p,z):
    need(type(p) is int and p>0 and p&(p-1)==0,'dyadic positive scale')
    need(type(z) is int and 1<=z<=p and (p-z)%3==0,'positive code cone')
    x=(p-z)//3
    return ''.join(str((x>>i)&1) for i in range(p.bit_length()-1))


def orbit_step(p,z,n):
    w=decode(p,z)
    need(type(n) is int and n>=0,'natural program numeral')
    if not w:return None
    d=z%2
    return ((p//2,z//2) if not d else ((4**n)*p,(z+p+3)//2))


def emit(rows,name,op,a,b):
    if type(a) is int and type(b) is int:
        return a+b if op=='+' else a-b if op=='-' else a*b
    if op=='*':
        if a==0 or b==0:return 0
        if a==1:return b
        if b==1:return a
    if op=='+':
        if a==0:return b
        if b==0:return a
    if op=='-':
        if b==0:return a
        if a==b:return 0
    rows.append((name,op,a,b));return name


def compile_history(program,t,positive=True,ordinary=False,*,square_boolean=False):
    need(type(program) is tuple and program and all(type(n) is int and n>=0 for n in program),'fixed nonempty program')
    need(type(t) is int and t>=1,'positive external horizon')
    need(type(positive) is bool and type(ordinary) is bool and type(square_boolean) is bool,'Boolean mode')
    rows=[];res=[];witnesses=[]
    def gate(name,op,a,b):return emit(rows,name,op,a,b)
    if ordinary:
        gate('three_x','*',3,'x');gate('P0','+','three_x','Z0');witnesses.append('Z0')
    for j in range(t):
        prefix=f's{j}_'; p='P0' if j==0 else f'P{j}';z='Z0' if j==0 else f'Z{j}'
        pn=1 if j+1==t else f'P{j+1}';zn=1 if j+1==t else f'Z{j+1}'
        if j+1<t:witnesses.extend([pn,zn])
        head=f'D{j}';witnesses.append(head)
        d=gate(prefix+'d','-',head,1) if positive else head
        h=4**program[j%len(program)];a=2*h-1
        v=gate(prefix+'T','*',p,d)
        av=gate(prefix+'AT','*',a,v)
        pr=gate(prefix+'pr','+',p,av)
        pl=gate(prefix+'pl','+',pn,pn)
        ep=gate(prefix+'ep','-',pl,pr)
        th=gate(prefix+'three_d','*',3,d)
        zv=gate(prefix+'zt','+',z,v)
        zr=gate(prefix+'zr','+',zv,th)
        zl=gate(prefix+'zl','+',zn,zn)
        ez=gate(prefix+'ez','-',zl,zr)
        dm=gate(prefix+'dm','-',d,1)
        eb=gate(prefix+'eb','*',d,dm)
        res.extend([ep,ez,eb])
    boolean_residuals=res[2::3]
    squares=[r if not square_boolean and r in boolean_residuals else gate('sq'+str(i),'*',r,r) for i,r in enumerate(res)]
    out=squares[0]
    for i,s in enumerate(squares[1:]):out=gate('sum'+str(i),'+',out,s)
    counts=Counter(r[1] for r in rows)
    return dict(program=list(program),horizon=t,positive=positive,ordinary=ordinary,square_boolean=square_boolean,boolean_residuals=boolean_residuals,inputs=['x'] if ordinary else ['P0','Z0'],witnesses=witnesses,source=rows,residuals=res,output=out,ledger=dict(M=counts['*'],A=counts['+']+counts['-'],operations=len(rows),witnesses=len(witnesses),residuals=len(res)))


def compile_projected(program,t,*,square_boolean=False):
    need(type(square_boolean) is bool,'Boolean mode')
    need(type(program) is tuple and program and all(type(n) is int and n>=0 for n in program),'fixed nonempty program')
    need(type(t) is int and t>=1,'positive external horizon')
    rows=[];res=[];witnesses=['Z0']
    def gate(name,op,a,b):return emit(rows,name,op,a,b)
    gate('three_x','*',3,'x');gate('P0','+','three_x','Z0')
    acc='Z0'
    for j in range(t):
        pre=f's{j}_';p='P0' if j==0 else f'P{j}';pn=1 if j+1==t else f'P{j+1}'
        if j+1<t:witnesses.append(pn)
        head=f'D{j}';witnesses.append(head);d=gate(pre+'d','-',head,1)
        v=gate(pre+'T','*',p,d);av=gate(pre+'AT','*',2*4**program[j%len(program)]-1,v)
        pr=gate(pre+'pr','+',p,av);pl=gate(pre+'pl','+',pn,pn);ep=gate(pre+'ep','-',pl,pr)
        th=gate(pre+'three_d','*',3,d);term=gate(pre+'term','+',v,th)
        weighted=term if j==0 else gate(pre+'weighted','*',2**j,term)
        acc=gate(pre+'acc','+',acc,weighted)
        dm=gate(pre+'dm','-',d,1);eb=gate(pre+'eb','*',d,dm)
        res.extend([ep,eb])
    res.append(gate('aggregate','-',acc,2**t))
    boolean_residuals=res[1:-1:2]
    squares=[r if not square_boolean and r in boolean_residuals else gate('sq'+str(i),'*',r,r) for i,r in enumerate(res)]
    out=squares[0]
    for i,v in enumerate(squares[1:]):out=gate('sum'+str(i),'+',out,v)
    c=Counter(r[1] for r in rows)
    return dict(program=list(program),horizon=t,positive=True,ordinary=True,square_boolean=square_boolean,boolean_residuals=boolean_residuals,inputs=['x'],witnesses=witnesses,source=rows,residuals=res,output=out,ledger=dict(M=c['*'],A=c['+']+c['-'],operations=len(rows),witnesses=len(witnesses),residuals=len(res)))


def restore_projected(packet,values):
    energy,env=evaluate(packet,values)
    need(energy==0 and all(type(v) is int and v>0 for v in values.values()),'positive zero required')
    result=dict(values);numerator=values['Z0']
    for j in range(packet['horizon']-1):
        d=values['D'+str(j)]-1;p=env['P'+str(j)]
        numerator+=(2**j)*d*(p+3)
        need(numerator%(2**(j+1))==0,'integral restoration')
        result['Z'+str(j+1)]=numerator//(2**(j+1))
        need(result['Z'+str(j+1)]>0,'positive restoration')
    return result


def evaluate(packet,values):
    env=dict(values)
    for out,op,a,b in packet['source']:
        av=env[a] if isinstance(a,str) else a;bv=env[b] if isinstance(b,str) else b
        env[out]=av+bv if op=='+' else av-bv if op=='-' else av*bv
    return env[packet['output']],env


def verify():
    checks=Counter(); max_length=10
    for length in range(max_length+1):
        for bits in itertools.product('01',repeat=length):
            w=''.join(bits);p,x=encode(w);z=p-3*x
            for n in range(6):
                direct=macro(w,n)
                slow=w
                for _ in range(n):slow=micro(slow,'11')
                slow=micro(slow,'10')
                need(direct==slow,'micro/macro orientation');checks['micro_macro']=checks['micro_macro']+1
                if z<=0:continue
                need(decode(p,z)==w,'positive coordinate inverse');checks['positive_decode']+=1
                arith=orbit_step(p,z,n)
                if direct is None:
                    need(arith is None,'empty queue');checks['empty_halts']+=1;continue
                pp,xx=encode(direct);zz=pp-3*xx
                need(arith==(pp,zz) and zz>0,'positive arithmetic step');checks['arithmetic_steps']+=1
                d=int(w[0]);h=4**n;a=2*h-1;c=2*(h-1)//3
                ep=2*pp-p-a*p*d;ex=2*xx-x+d-c*p*d;ez=2*zz-z-p*d-3*d
                need(ep==ex==ez==0 and ez==ep-3*ex,'residual mapping');checks['natural_zero_maps']+=1
    # Full signed off-zero identity under the coordinate substitution Z=P-3X.
    for p,x,pp,xx,d,n in itertools.product(range(-2,3),range(-2,3),range(-2,3),range(-2,3),range(-1,3),range(4)):
        h=4**n;a=2*h-1;c=2*(h-1)//3;z=p-3*x;zz=pp-3*xx
        ep=2*pp-p-a*p*d;ex=2*xx-x+d-c*p*d;ez=2*zz-z-p*d-3*d;eb=d*(d-1)
        old=ep*ep+ex*ex+eb*eb;new=ep*ep+ez*ez+eb*eb
        need(ez==ep-3*ex and new-old==ep*ep-6*ep*ex+8*ex*ex,'signed correction');checks['signed_corrections']+=1
    # Step graph check over complete bounded positive candidate boxes.
    for p in (1,2,4,8):
        for z in range(1,p+1):
            if (p-z)%3:continue
            for n in (0,1):
                expected=orbit_step(p,z,n)
                for pp,zz,d in itertools.product(range(1,33),range(1,33),range(4)):
                    ep=2*pp-p-(2*4**n-1)*p*d;ez=2*zz-z-p*d-3*d;eb=d*(d-1)
                    zero=ep==ez==eb==0
                    need(zero==(expected==(pp,zz) and d==z%2),'bounded complete graph');checks['bounded_step_candidates']+=1
    packets=[]
    for positive in (False,True):
        for t in range(1,7):
            packet=compile_history((0,1,1),t,positive)
            need(packet['ledger']==dict(M=6*t-(t+2)//3,A=(12 if positive else 11)*t-3,operations=(18 if positive else 17)*t-3-(t+2)//3,witnesses=3*t-2,residuals=3*t),'full history ledger')
            known=set(packet['inputs']+packet['witnesses'])
            for out,op,a,b in packet['source']:
                need(out not in known and all(not isinstance(v,str) or v in known for v in (a,b)),'source closure');known.add(out)
            checks['complete_source_ledgers']+=1
            for seed in range(5):
                values={name:(seed+2*i)%11-4 for i,name in enumerate(packet['inputs']+packet['witnesses'])}
                energy,env=evaluate(packet,values)
                need(energy==sum(env[r] if r in packet['boolean_residuals'] else env[r]**2 for r in packet['residuals']),'full emitted nonnegative finalizer');checks['full_dag_outputs']+=1
            packets.append(packet)
    # Complete ordinary-input sources have only positive auxiliary coordinates.
    ordinary_packets=[]; halting_examples=[]
    for t in range(1,7):
        p=compile_history((0,1,1),t,True,True)
        need(p['ledger']==dict(M=6*t+1-(t+2)//3,A=12*t-2,operations=18*t-1-(t+2)//3,witnesses=3*t-1,residuals=3*t),'ordinary full ledger')
        known=set(p['inputs']+p['witnesses'])
        for out,op,a,b in p['source']:
            need(out not in known and all(not isinstance(v,str) or v in known for v in (a,b)),'ordinary source closure');known.add(out)
        ordinary_packets.append(p);checks['ordinary_complete_ledgers']+=1
    for x in range(1,33):
        p=1
        while p<=3*x:p*=2
        w=''.join(str((x>>i)&1) for i in range(p.bit_length()-1));state=(p,p-3*x)
        states=[state];heads=[]
        for j in range(80):
            if not w:break
            heads.append(int(w[0]));w=macro(w,(0,1,1)[j%3]);state=orbit_step(*state,(0,1,1)[j%3]);states.append(state)
        if w:continue
        t=len(heads);packet=compile_history((0,1,1),t,True,True)
        values={'x':x,'Z0':states[0][1]}
        for j,d in enumerate(heads):values['D'+str(j)]=d+1
        for j,(p,z) in enumerate(states[1:-1],1):values['P'+str(j)]=p;values['Z'+str(j)]=z
        energy,env=evaluate(packet,values)
        need(energy==0 and all(type(v) is int and v>0 for v in values.values()),'complete positive ordinary witness')
        need(all(p&(p-1)==0 and (p-z)%3==0 for p,z in states),'terminal dyadic/congruence')
        need(states[-1]==(1,1) and t>=3,'terminal state or short boundary')
        halting_examples.append(dict(x=x,steps=t,initial=states[0],heads=heads,states=states));checks['ordinary_positive_halting_histories']+=1
    need(halting_examples and halting_examples[0]['x']==1 and halting_examples[0]['steps']==3,'first positive input boundary')
    projected_packets=[]
    for t in range(1,7):
        packet=compile_projected((0,1,1),t)
        need(packet['ledger']==dict(M=6*t+1-(t+2)//3,A=9*t+1,operations=15*t+2-(t+2)//3,witnesses=2*t,residuals=2*t+1),'projected full ledger')
        known=set(packet['inputs']+packet['witnesses'])
        for out,op,a,b in packet['source']:
            need(out not in known and all(not isinstance(v,str) or v in known for v in (a,b)),'projected source closure');known.add(out)
        projected_packets.append(packet);checks['projected_complete_ledgers']+=1
        for seed in range(5):
            values={name:(seed+2*i)%11-4 for i,name in enumerate(packet['inputs']+packet['witnesses'])}
            energy,env=evaluate(packet,values)
            need(energy==sum(env[r] if r in packet['boolean_residuals'] else env[r]**2 for r in packet['residuals']),'projected full emitted nonnegative finalizer');checks['projected_full_dag_outputs']+=1
    for fixture in halting_examples:
        t=fixture['steps'];p=compile_projected((0,1,1),t);states=fixture['states']
        values={'x':fixture['x'],'Z0':states[0][1]}
        for j,d in enumerate(fixture['heads']):values['D'+str(j)]=d+1
        for j,(width,z) in enumerate(states[1:-1],1):values['P'+str(j)]=width
        need(evaluate(p,values)[0]==0,'projected positive witness')
        oldvalues=restore_projected(p,values)
        need(evaluate(compile_history((0,1,1),t,True,True),oldvalues)[0]==0,'restored full zero')
        need(all(oldvalues['Z'+str(j)]==states[j][1] for j in range(t)),'unique intended restoration')
        checks['projected_positive_roundtrips']+=1
    # The positive ordinary-input family has no length1 or length2 halting history.
    for t in (1,2):
        p=compile_projected((0,1,1),t)
        for x in range(1,5):
            for ws in itertools.product(range(1,6),repeat=len(p['witnesses'])):
                vals=dict(zip(p['witnesses'],ws));vals['x']=x
                need(evaluate(p,vals)[0]>0,'short false zero');checks['short_positive_candidates']+=1
    for packet in packets+ordinary_packets+projected_packets:
        reference=compile_projected(tuple(packet['program']),packet['horizon'],square_boolean=True) if packet in projected_packets else compile_history(tuple(packet['program']),packet['horizon'],packet['positive'],packet['ordinary'],square_boolean=True)
        need(reference['ledger']['M']-packet['ledger']['M']==packet['horizon'] and reference['ledger']['A']==packet['ledger']['A'],'Boolean square saving')
        need(reference['witnesses']==packet['witnesses'] and reference['residuals']==packet['residuals'],'Boolean mode interfaces')
        for seed in range(5):
            values={name:(seed+2*i)%11-4 for i,name in enumerate(packet['inputs']+packet['witnesses'])}
            new,env=evaluate(packet,values);old,oldenv=evaluate(reference,values)
            bs=[env[r] for r in packet['boolean_residuals']]
            need(all(v>=0 for v in bs),'integer Boolean factor sign')
            need(old-new==sum(v*v-v for v in bs),'complete Boolean offzero correction')
            need((old==0)==(new==0),'integer Boolean zero equivalence')
            checks['complete_boolean_corrections']+=1
        used={packet['output']}
        for out,op,a,b in reversed(packet['source']):
            need(out in used,'dead emitted operation')
            need(not(type(a) is int and type(b) is int),'constant-only operation')
            used.update(v for v in (a,b) if isinstance(v,str))
        checks['live_complete_sources']+=1
    # A local step alone does not imply dyadic width: this all-natural step is real.
    p,z,pp,zz,d,n=6,3,6,6,1,0
    need(2*pp-p-(2*4**n-1)*p*d==0 and 2*zz-z-p*d-3*d==0,'non-dyadic local zero')
    need(encode('1')==(2,1) and 2-3*1<0,'coordinate positivity restriction')
    result=dict(status='PASS_LOCAL_SCOUT_NO_UNIVERSAL_BOUND',helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=dict(checks),finite_history_packets=packets,ordinary_history_packets=ordinary_packets,ordinary_halting_examples=halting_examples,projected_history_packets=projected_packets,non_dyadic_local_zero=dict(P=6,Z=3,P_next=6,Z_next=6,d=1,n=0),constant_folding='All constant-only gates and neutral0/1 arithmetic removed; costs are literal live DAG counts, not optimality claims.',limits=['A standalone step requires a valid width/code input. Complete terminal histories force dyadic widths and congruence; ordinary mode loads P0=3x+Z0 and uses positive Z0.','The full finite-horizon source accepts some zero-padded binary x; no universal padding-insensitive program/decoder or fixed-arity unbounded history is instantiated.','Counts include whole externally fixed histories and final nonnegative integer finalizer, not an existentially quantified horizon.','Primary creator code could not be fetched; no downloaded interpreter executed.'])
    # Canonical JSON types preserve exact receipt comparison, including bool versus int.
    return json.loads(json.dumps(result,sort_keys=True))


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify()
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'receipt differs')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=r['status'],checks=r['checks']),sort_keys=True))
