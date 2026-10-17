#!/usr/bin/env python3
"""Algebraic acceleration discovered from the literal p254 control graph.

Recognizes exact transfer/copy and Cantor-pair loops by their finite control
graphs, checks all local fixed-gap TM cases traversed, and uses closed forms.
This is an executable research certificate, not a kernel proof.
"""
from pathlib import Path
import importlib.util, sys, json, collections, time, argparse, math
HELPER=Path(__file__).resolve().with_name('runtime252_short_gap.py')
sp=importlib.util.spec_from_file_location('sg',HELPER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
sys.set_int_max_str_digits(0)
m.NODES=m.program()
OPS={}
def gather(edge,p=''):
    if edge.startswith('CN '):
        for b,e in enumerate(m.NODES[int(edge[3:])]):gather(e,p+str(b))
    else:
        op,*v=edge.split(); r=int(v[0]) if v else 0
        if op in ('CI','CD'):r=m.PHYS[r]
        OPS[p]=(op,r)
gather('CN 0')
def inc(p):
    if '0' not in p:return None
    return p[:p.rindex('0')]+'1'
def strip(b,k,p):
    while k and p:
        if p[-1]==b:k-=1
        p=p[:-1]
    return p
def canonical(p):return None if p is None else m.walk(p)[0]
def nxt(p,br='-'):
    op,r=OPS[p]
    if op=='CI' or op=='CD' and br=='p':z=inc(p)
    elif op=='CD':z=inc(strip('0',1,p))
    elif op=='CB':z=inc(strip('0',r,p))
    elif op=='CC':z=strip('1',r,p)
    else:return None
    return canonical(z)
def skip_controls(p):
    trace=[];seen=set()
    while p is not None and OPS[p][0] in ('CB','CC'):
        if p in seen:return None,trace
        seen.add(p);trace.append((p,'-'));p=nxt(p)
    return p,trace
TRANSFER={}
for entry,(op,r) in OPS.items():
    if op!='CD':continue
    p=nxt(entry,'p');trace=[(entry,'p')];dest=[];seen=set()
    while p is not None and p!=entry and p not in seen:
        seen.add(p);o,s=OPS[p]
        if o=='CI':dest.append(s)
        elif o not in ('CB','CC'):break
        trace.append((p,'-'));p=nxt(p)
    if p==entry and r not in dest:
        TRANSFER[entry]={'kind':'transfer','source':r,'dest':dict(collections.Counter(dest)),
                         'exit':nxt(entry,'z'),'cases':trace+[(entry,'z')],
                         'cycle_length':len(trace),'entry':entry}
PAIR={}
for entry,t1 in TRANSFER.items():
    if len(t1['dest'])!=2 or any(v!=1 for v in t1['dest'].values()):continue
    p,c0=skip_controls(t1['exit'])
    if p is None or OPS[p][0]!='CD':continue
    x=OPS[p][1];t=t1['source']
    if x not in t1['dest']:continue
    y=next(r for r in t1['dest'] if r!=x)
    u,c1=skip_controls(nxt(p,'p'))
    if u is None or OPS[u]!=('CI',y):continue
    v,c2=skip_controls(nxt(u))
    if v not in TRANSFER:continue
    t2=TRANSFER[v]
    if t2['source']!=x or t2['dest']!={t:1}:continue
    end,c3=skip_controls(t2['exit'])
    if end!=entry:continue
    PAIR[entry]={'kind':'pair','x':x,'t':t,'y':y,'exit':nxt(p,'z'),
        'cases':t1['cases']+c0+[(p,'p'),(p,'z')]+c1+[(u,'-')]+c2+t2['cases']+c3,
        'entry':entry,'loop_guard':p,'copy':t1,'transfer':t2,
        'prefix_control':len(c0),'positive_constant':4+len(c0)+len(c1)+len(c2)+len(c3)}

def unP(n):
    k=(math.isqrt(8*n+1)-1)//2;b=n-k*(k+1)//2;return k-b,b
def P(a,b):return (a+b)*(a+b+1)//2+b

def discover_unpair():
    out={}
    for entry,(op,r) in OPS.items():
        if op!='CD':continue
        a,c0=skip_controls(nxt(entry,'p'))
        if a is None or OPS[a][0]!='CI':continue
        y=OPS[a][1];b,c1=skip_controls(nxt(a))
        if b is None or OPS[b][0]!='CD':continue
        x=OPS[b][1]
        if len({x,y,r})!=3:continue
        c,c2=skip_controls(nxt(b,'p'))
        d,c3=skip_controls(nxt(b,'z'))
        if c!=entry or d not in TRANSFER:continue
        tr=TRANSFER[d]
        if tr['source']!=y or tr['dest']!={x:1}:continue
        e,c4=skip_controls(tr['exit'])
        if e!=entry:continue
        out[entry]={'kind':'unpair','source':r,'x':x,'y':y,'entry':entry,
            'exit':nxt(entry,'z'),'cases':[(entry,'p'),(entry,'z')]+c0+[(a,'-')]+c1+[(b,'p'),(b,'z')]+c2+c3+tr['cases']+c4,
            'ordinary_cost':3+len(c0)+len(c1)+len(c2),
            'wrap_constant':4+len(c0)+len(c1)+len(c3)+len(c4),
            'transfer_cycle':tr['cycle_length']}
    return out
UNPAIR=discover_unpair()
MACROS={**TRANSFER,**PAIR,**UNPAIR}

def apply_macro(mac,R):
    S=R.copy(); k=mac['kind']
    if k=='transfer':
        n=S[mac['source']]
        for r,c in mac['dest'].items():S[r]+=c*n
        S[mac['source']]=0
    elif k=='pair':
        x,t,y=mac['x'],mac['t'],mac['y'];S[y]+=P(S[x],S[t]);S[x]=S[t]=0
    else:
        r,x,y=mac['source'],mac['x'],mac['y'];S[x],S[y]=unP(P(S[x],S[y])+S[r]);S[r]=0
    return S

def macro_decrements(mac,R):
    k=mac['kind']
    if k=='transfer':return R[mac['source']]
    if k=='pair':return R[mac['t']] + (R[mac['x']]+R[mac['t']])**2
    r,x,y=mac['source'],mac['x'],mac['y']
    u,v=unP(P(R[x],R[y])+R[r]);a=R[x]+R[y];b=u+v
    return 2*R[r]+(b-a)*(b+a-1)//2

def macro_rm_steps(mac,R):
    kind=mac['kind']
    if kind=='transfer':return mac['cycle_length']*R[mac['source']]+1
    if kind=='pair':
        n=R[mac['x']]+R[mac['t']];c1=mac['copy']['cycle_length'];c2=mac['transfer']['cycle_length']
        return (c1+c2)*n*(n-1)//2+c1*R[mac['t']]+mac['positive_constant']*n+2+mac['prefix_control']
    r,x,y=mac['source'],mac['x'],mac['y'];u,v=unP(P(R[x],R[y])+R[r]);a=R[x]+R[y];b=u+v
    return 1+R[r]*mac['ordinary_cost']+(b-a)*(mac['wrap_constant']-mac['ordinary_cost'])+mac['transfer_cycle']*(b-a)*(a+b+1)//2

def raw_graph_run(entry,R,exit,fuel=1000000):
    p=entry;R=R.copy();steps=0;decs=0
    while steps<fuel:
        if steps and p==exit:return R,steps,decs
        op,r=OPS[p];br=('p' if R[r] else 'z') if op=='CD' else '-'
        if op=='CI':R[r]+=1
        if op=='CD' and br=='p':R[r]-=1;decs+=1
        if op=='CH':return None,steps,decs
        p=nxt(p,br);steps+=1
        if p is None:return None,steps,decs
    raise RuntimeError('finite macro test fuel')

def self_test():
    tests=0
    # One instance per semantic shape, all 0..5 triples; direct exact RM control.
    instances={}
    for p,z in MACROS.items():
        key=z['kind'],str(sorted((k,v) for k,v in z.items() if k in ('source','dest','x','t','y')))
        instances.setdefault(key,z)
    import itertools
    for z in instances.values():
        fields=list(dict.fromkeys(z[k] for k in ('source','x','t','y') if k in z))
        if len(fields)<3 and z['kind']=='transfer':fields+=list(z['dest'])
        fields=list(dict.fromkeys(fields))[:3]
        for vals in itertools.product(range(6),repeat=len(fields)):
            R=[3]*9
            for r,v in zip(fields,vals):R[r]=v
            got,steps,decs=raw_graph_run(z['entry'],R,z['exit'])
            assert got==apply_macro(z,R),(z,R,got,apply_macro(z,R))
            assert decs==macro_decrements(z,R),(z,R,decs,macro_decrements(z,R))
            assert steps==macro_rm_steps(z,R),(z,R,steps,macro_rm_steps(z,R))
            tests+=1
    return {'macro_instances':dict(collections.Counter(z['kind'] for z in MACROS.values())),
            'semantic_shapes':len(instances),'exact_small_graph_tests':tests}

def main(limit=100000,initial=None):
    tested=self_test();print('DISCOVERY',tested,flush=True)
    st=m.blank_checkpoint() if initial is None else initial
    ns=m.executor();p=st['p'];g=st['gap'];regs=st['regs'].copy()
    cache={};macro_cache={};record=[];roots=[];counts=collections.Counter();started=time.monotonic();decs=0;rmsteps=0
    def check(case):
        cp,br=case;op,r=OPS[cp];key=cp,op,r,br,g
        if key not in cache:cache[key]=m.case(ns,*key,exact_gap=True)
        return cache[key]
    for i in range(limit):
        p=canonical(p);op,r=OPS[p];state={'iteration':i,'p':p,'op':op,'r':r,'gap':g,'regs':regs.copy(),'positive_decs':decs,'rm_steps':rmsteps}
        if 'spares' in st:state['initial_spares']=st['spares']
        if 'tail' in st:state['initial_tail_segments']=st['tail']
        if max(v.bit_length() for v in regs)>100000:
            return {'result':'integer_size_checkpoint','state':state,'discovery':tested,'counts':dict(counts),'record':record,'cases':len(cache)}
        if p in MACROS:
            mac=MACROS[p]
            if p not in macro_cache:
                bad=[(c,check(c)) for c in mac['cases'] if not check(c)[0]]
                macro_cache[p]=bad
            bad_local=macro_cache[p]
            if bad_local and mac['kind']!='transfer' and p in TRANSFER:
                mac=TRANSFER[p]
                bad_local=[(c,check(c)) for c in mac['cases'] if not check(c)[0]]
            if not bad_local:
                old=regs;regs=apply_macro(mac,regs);counts[mac['kind']]+=1;decs+=macro_decrements(mac,old);rmsteps+=macro_rm_steps(mac,old)
                record.append({'iteration':i,'entry':p,'kind':mac['kind'],'before':old,'after':regs.copy(),'exit':mac['exit']})
                p=mac['exit'];continue
            if mac['kind']=='transfer' and regs[mac['source']]>0:
                # The positive loop may be valid even when its eventual zero
                # exit collides with a short header. Stop on that guard.
                bad=bad_local
                if all(c==(p,'z') for c,res in bad):
                    old=regs;regs=apply_macro(mac,regs);counts['positive_transfer']+=1
                    n=old[mac['source']];decs+=n;rmsteps+=mac['cycle_length']*n
                    record.append({'iteration':i,'entry':p,'kind':'positive_transfer','before':old,'after':regs.copy(),'exit':p})
                    continue
        br=('p' if regs[r] else 'z') if op=='CD' else '-'
        good,rawsucc,res=check((p,br))
        if not good:
            return {'result':'failed_local_contract','detail':res,'state':state,'branch':br,'macro_failures':macro_cache.get(p), 'discovery':tested,'counts':dict(counts),'record':record,'cases':len(cache),'seconds':time.monotonic()-started}
        if op=='CH':return {'result':'halt','state':state,'discovery':tested,'counts':dict(counts),'record':record,'cases':len(cache)}
        if op=='CI':regs[r]+=1
        if op=='CD' and br=='p':regs[r]-=1;decs+=1
        counts['atomic']+=1;rmsteps+=1
        if rawsucc is None:
            g+=1;p=''
        else:p=rawsucc
        if p in ('','0','00','000'):
            return {'result':'root','state':{'iteration':i+1,'p':p,'gap':g,'regs':regs},'discovery':tested,'counts':dict(counts),'record':record,'cases':len(cache)}
        if i and i%10000==0:print('PROGRESS',i,'maxbits',max(x.bit_length() for x in regs),'counts',dict(counts),flush=True)
    return {'result':'fuel','state':state,'discovery':tested,'counts':dict(counts),'record':record,'cases':len(cache)}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=100000);ap.add_argument('--out',default=str(Path(__file__).resolve().parents[1]/'certificates/macro32.json'));a=ap.parse_args()
    result=main(a.limit);Path(a.out).write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='record'})
