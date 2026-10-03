#!/usr/bin/env python3
"""Bounded pinned Grill source/finite-history audit; no universality claim."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import types

PINS={'scout':'2f3a1b2525e82ea935d27480dd77750254cfd31236092a7a063e78708379fa81',
      'encoding':'66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3'}

def need(x,msg):
    if not x: raise ValueError(msg)

def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def load(path,kind):
    data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==PINS[kind],kind+' source pin')
    m=types.ModuleType('_independent_grill_'+kind);m.__file__=str(path)
    exec(compile(data,str(path),'exec'),m.__dict__);return m

def const(v): return {():v} if v else {}
def var(v): return {(v,):1}
def add(a,b,sign=1):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,0)+sign*v
    return {k:v for k,v in r.items() if v}
def mul(a,b):
    r={}
    for k,v in a.items():
        for l,w in b.items():
            q=tuple(sorted(k+l));r[q]=r.get(q,0)+v*w
    return {k:v for k,v in r.items() if v}
def scale(a,c): return mul(a,const(c))
def get(e,x): return e[x] if type(x) is str else const(x)

def formal(packet):
    names=packet['inputs']+packet['witnesses'];need(len(set(names))==len(names),'unique input names')
    e={x:var(x) for x in names};counts=Counter()
    for name,op,a,b in packet['source']:
        need(type(name) is str and name not in e and op in ('+','-','*'),'typed SSA')
        need(all(type(x) in (int,str) and (type(x) is int or x in e) for x in (a,b)),'operands')
        need(not(type(a) is int and type(b) is int),'unfolded constants')
        need(not(op=='*' and (a in (0,1) or b in (0,1))),'unfolded neutral product')
        e[name]=mul(get(e,a),get(e,b)) if op=='*' else add(get(e,a),get(e,b),1 if op=='+' else -1)
        counts['M' if op=='*' else 'A']+=1
    live={packet['output']}
    for name,op,a,b in reversed(packet['source']):
        need(name in live,'dead gate');live.update(x for x in (a,b) if type(x) is str)
    need(packet['ledger']['operations']==sum(counts.values())==len(packet['source']),'full paid count')
    return e,counts

def manual(packet,projected):
    t=packet['horizon'];r=[];p=add(scale(var('x'),3),var('Z0')) if packet['ordinary'] else var('P0')
    z=var('Z0');agg=z;bs=[]
    for j in range(t):
        d=add(var('D'+str(j)),const(-1)) if packet['positive'] else var('D'+str(j))
        pn=const(1) if j+1==t else var('P'+str(j+1))
        zn=const(1) if j+1==t else var('Z'+str(j+1))
        pd=mul(p,d);ep=add(add(scale(pn,2),p,-1),scale(pd,2*4**packet['program'][j%len(packet['program'])]-1),-1)
        ez=add(add(add(scale(zn,2),z,-1),pd,-1),scale(d,3),-1)
        eb=mul(d,add(d,const(-1)));bs.append(eb)
        r.extend([ep,eb] if projected else [ep,ez,eb])
        agg=add(agg,scale(add(pd,scale(d,3)),2**j));p=pn;z=zn
    if projected:r.append(add(agg,const(-(2**t))))
    f={}
    bidx=set(range(1,2*t,2)) if projected else set(range(2,3*t,3))
    for i,a in enumerate(r):f=add(f,a if i in bidx and not packet['square_boolean'] else mul(a,a))
    return r,f

def assignment(states,heads,x=None,projected=False):
    vals={'P0':states[0][0],'Z0':states[0][1]} if x is None else {'x':x,'Z0':states[0][1]}
    for j,d in enumerate(heads):vals['D'+str(j)]=d+1
    for j,(p,z) in enumerate(states[1:-1],1):
        vals['P'+str(j)]=p
        if not projected:vals['Z'+str(j)]=z
    return vals

def verify(scout_path,encoding_path):
    s=load(scout_path,'scout');enc=load(encoding_path,'encoding');c=Counter()
    programs=[(0,),(1,),(2,),(0,1,1),(2,0,1),(0,0,2,1)]
    for program,t,squared,shape in itertools.product(programs,range(1,9),(False,True),range(4)):
        projected=shape==3;positive=shape!=0;ordinary=shape>=2
        packet=s.compile_projected(program,t,square_boolean=squared) if projected else s.compile_history(program,t,positive,ordinary,square_boolean=squared)
        e,counts=formal(packet);r,f=manual(packet,projected)
        need(all(e[name]==p for name,p in zip(packet['residuals'],r)),'literal residual identity')
        need(e[packet['output']]==f,'whole polynomial identity')
        need(max(map(len,f))==4,'exact quartic degree')
        zeros=sum(program[j%len(program)]==0 for j in range(t))
        mm=(6+int(squared))*t-zeros+int(ordinary)
        aa=9*t+1 if projected else (12 if positive else 11)*t-3+int(ordinary)
        ww=2*t if projected else 3*t-2+int(ordinary)
        rr=2*t+1 if projected else 3*t
        need(packet['ledger']==dict(M=mm,A=aa,operations=mm+aa,witnesses=ww,residuals=rr),'all ledger formulas')
        c['complete_sources']+=1;c['literal_residual_identities']+=len(r);c['exact_quartic_degrees']+=1
    for program,t in itertools.product(programs,range(1,11)):
        for heads in itertools.product((0,1),repeat=t):
            c['reverse_boolean_histories']+=1
            states=[(1,1)];good=True
            for j in range(t-1,-1,-1):
                pn,zn=states[-1];d=heads[j];h=4**program[j%len(program)]
                if d and pn%h:good=False;break
                p=pn//h if d else 2*pn;z=2*zn-d*(p+3)
                if p<=0 or z<=0:good=False;break
                states.append((p,z))
            if not good:continue
            states.reverse();c['positive_raw_terminal_histories']+=1
            need(all(p&(p-1)==0 and (p-z)%3==0 for p,z in states),'terminal dyadic and congruence')
            raw=s.compile_history(program,t,True,False)
            need(s.evaluate(raw,assignment(states,heads))[0]==0,'raw complete zero')
            x=(states[0][0]-states[0][1])//3
            if x<=0:continue
            c['ordinary_positive_zero_bijections']+=1
            full=s.compile_history(program,t,True,True);project=s.compile_projected(program,t)
            fv=assignment(states,heads,x);pv=assignment(states,heads,x,True)
            need(s.evaluate(full,fv)[0]==s.evaluate(project,pv)[0]==0,'two complete positive zeros')
            need(s.restore_projected(project,pv)==fv,'unique restoration inverse')
            word=''.join(str((x>>k)&1) for k in range(states[0][0].bit_length()-1))
            for j,d in enumerate(heads):
                need(bool(word) and int(word[0])==d,'causal head and no early halt')
                word=word[1:]+('0'+'10'*program[j%len(program)] if d else '')
                pp=2**len(word);xx=sum(int(bit)*2**k for k,bit in enumerate(word))
                need(states[j+1]==(pp,pp-3*xx),'independent string step')
            need(word=='','exact terminal empty')
    # Explicit boundaries: real false zero and raw invalid initial content.
    real_packet=s.compile_projected((0,),1)
    vals={'x':Fraction(1,3),'Z0':Fraction(1,3),'D0':Fraction(3,2)}
    need(s.evaluate(real_packet,vals)[0]==0,'nonnegative-real counterexample')
    need(s.evaluate(s.compile_projected((0,),1,square_boolean=True),vals)[0]==Fraction(5,16),'squared real separation')
    states=[(2,5),(8,5),(8,8),(4,4),(2,2),(1,1)];heads=(1,1,0,0,0)
    need(s.evaluate(s.compile_history((1,0,0,0,0),5),assignment(states,heads))[0]==0,'raw invalid-code zero')
    need(states[0][0]-states[0][1]==-3,'negative initial content')
    c['scope_counterexamples']=2
    # Reconstruct finite source-encoding receipts; no downloaded code runs.
    er=enc.verify();need(er['checks']['two_generation_fixtures']==10240,'encoding finite scope')
    c['encoding_two_generation_cases']=10240
    # Typed compiler entry parameters, not a canonical supplied-packet API claim.
    bad=[lambda:s.compile_history([0],1),lambda:s.compile_history((True,),1),lambda:s.compile_history((0.0,),1),lambda:s.compile_history((0,),True),lambda:s.compile_history((0,),0),lambda:s.compile_history((0,),1,1),lambda:s.compile_history((0,),1,ordinary=1),lambda:s.compile_projected((0,),1,square_boolean=0)]
    for f in bad:
        try:f()
        except ValueError:c['typed_compiler_rejections']+=1
        else:raise ValueError('invalid compiler parameter accepted')
    return dict(status='PASS_BOUNDED_INDEPENDENT_REVIEW',helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_pins=PINS,checks=dict(c),scope='Literal finite-history sources, positive-zero projection and primary encoding fragment only. No complete universal compiler or fixed-arity horizon encoding.',counterexamples={'real_unsquared_false_zero':{'program':[0],'t':1,'x':'1/3','Z0':'1/3','D0':'3/2','default':0,'squared':'5/16'},'raw_invalid_initial_content':{'program':[1,0,0,0,0],'states':states,'heads':heads,'initial_X':-1}})

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--scout',type=Path,default=Path(__file__).with_name('grill_tag_affine_scout.py'));ap.add_argument('--encoding',type=Path,default=Path(__file__).with_name('review_grill_encoding_e.py'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    r=json.loads(json.dumps(verify(a.scout,a.encoding),sort_keys=True))
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'receipt differs')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':r['status'],'checks':r['checks']},sort_keys=True))
