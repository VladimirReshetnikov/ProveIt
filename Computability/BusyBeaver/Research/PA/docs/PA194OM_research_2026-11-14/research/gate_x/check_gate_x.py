#!/usr/bin/env python3
"""Independent source-expression binding for the proposed arbitrary-consequent gate.

The inherited check_source_commands.py supplies the written-and-tested arithmetic
template definitions; this checker adds only unpair-L, transfer-X-to-T and the
ordinary AX break.  It does not simulate enormous formula integers and does not
establish a state count for any proposed binary implementation.
"""
from pathlib import Path
import argparse, importlib.util, json, hashlib

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'ax11h_audit' / 'verification' / 'check_source_commands.py'
spec = importlib.util.spec_from_file_location('inherited_arithmetic_templates', BASE)
b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
N,T,W,A,D,H,X,Y,L = range(9)

def require(p, message):
    if not p: raise AssertionError(message)

TOKENS = dict(b.TOKENS, node32=['readX'], node42=['moveXT'])

def word(tree):
    if isinstance(tree, str): return TOKENS[tree]
    if tree == ['leaf','inc',1]: return ['incT']
    if tree == ['leaf','breakTo',1]: return ['breakAX']
    require(isinstance(tree,list) and len(tree)==2,'unexpected source token')
    return word(tree[0])+word(tree[1])

class Templates(b.Templates):
    def atom(self,name):
        if name == 'readX': self.unpair(L)
        elif name == 'moveXT': self.transfer(X,T)
        else: super().atom(name)

class Arithmetic(b.Arithmetic):
    def atom(self,name):
        if name == 'readX': self.unpair(L)
        elif name == 'moveXT': self.transfer(X,T)
        elif name == 'breakAX': self.cost += 1
        else: super().atom(name)

def full_templates(ww):
    q=Templates()
    q.compare(10,11);q.emit('halt');q.unpair(W);q.transfer(X,H)
    ports={'fetch':len(q.rows)};q.fetch_prefix()
    ports['decode']=len(q.rows);q.unpair(L);q.transfer(X,A)
    require(len(q.rows)==48,'prefix size')
    q.emit('dec',A,0,49);q.emit('dec',A,0,50)
    ports['AX']=len(q.rows)
    require(ww[-1]=='breakAX' and ww.count('breakAX')==1,'one terminal AX break')
    for token in ww[:-1]: q.atom(token)
    ports['AX_break']=len(q.rows);q.jump(0)
    ports['MP']=len(q.rows);q.atom('readDCons');q.transfer(T,X)
    ports['MP_compare']=len(q.rows);q.compare(0,0)
    ports['MP_success']=len(q.rows);q.copy(D)
    ports['return']=len(q.rows);q.jump(25)
    ports['Shift']=len(q.rows);q.clear(T);q.copy(H);q.inc(X);q.jump(0)
    q.rows[48][2]=ports['Shift'];q.rows[49][2]=ports['MP']
    q.rows[ports['AX_break']][1]=ports['return']
    q.rows[ports['MP_compare']+4][2]=ports['MP_success']
    q.rows[ports['MP_compare']+9][1]=ports['return']
    return q,ports

def resolve_graph(names, tree):
    sites=[]
    def expand(t,p=''):
        if isinstance(t,str):return expand(tree if t=='x67' else names[t],p)
        if t[0]=='leaf':sites.append([p,t[1],t[2]]);return
        expand(t[0],p+'0');expand(t[1],p+'1')
    expand('node172')
    ranges={};indices={p:i for i,(p,_,_) in enumerate(sites)}
    def interval(p):
        if p in indices: v=(indices[p],indices[p]+1)
        else:
            a,c=interval(p+'0'),interval(p+'1')
            require(a[1]==c[0],'contiguous source interval');v=(a[0],c[1])
        ranges[p]=v;return v
    interval('')
    def unwind(p,bit,k):
        while p:
            ch,p=p[-1],p[:-1]
            if ch==bit:
                k-=1
                if not k:return ranges[p][1]%len(sites) if bit=='0' else ranges[p][0]
        return 0
    rows=[]
    for i,(p,op,a) in enumerate(sites):
        after=(i+1)%len(sites)
        if op=='inc':r=['inc',a,after]
        elif op=='dec':r=['dec',a,unwind(p,'0',1),after]
        elif op=='breakTo':r=['jump',unwind(p,'0',a)]
        elif op=='continueTo':r=['jump',unwind(p,'1',a)]
        else:require(op=='halt','opcode');r=['halt']
        rows.append(r)
    return sites,rows

def symbolic_AX(ww):
    Z,pp,ii,add=b.Z,b.pp,b.ii,b.add
    hd,tl,cut=b.hd,b.tl,b.cut
    mm,uu,ee,nn,conj,ex=b.mm,b.uu,b.ee,b.nn,b.conj,b.ex
    n,t,w,a,d,h,x,y,z,tail=[('var',s) for s in ('n','t','w','a','d','h','x','y','z','tail')]
    r=[n,t,w,a,d,h,Z,Z,pp(y,pp(x,pp(z,tail)))]
    def push():r[W]=pp(r[T],r[W]);r[T]=Z
    for index,token in enumerate(ww):
        if token=='compareGuard':
            require(r[A]==Z and r[X]==r[Y],'comparison scratch')
            require(ww[index-1]=='copyGuard','comparison predecessor')
        elif token=='moveXT':
            require(r[T]==r[Y]==Z and ww[index-1]=='readX','transfer scratch and predecessor')
        else: require(r[X]==r[Y]==Z,'ordinary scratch')
        if token=='incT':r[T]=b.su(r[T])
        elif token=='push':push()
        elif token in ('copyD','copyH','copyA'):
            push();r[T]=r[{'copyD':D,'copyH':H,'copyA':A}[token]]
        elif token=='cons':r[T]=ii(hd(r[W]),r[T]);r[W]=tl(r[W])
        elif token=='readH':r[H]=add(r[H],hd(r[L]));r[L]=tl(r[L])
        elif token=='readDCons':
            r[D]=add(r[D],hd(r[L]));r[L]=tl(r[L]);r[T]=ii(r[T],r[D])
        elif token=='readX':r[X]=hd(r[L]);r[L]=tl(r[L])
        elif token=='moveXT':r[T]=r[X];r[X]=Z
        elif token=='copyGuard':r[X]=r[Y]=r[A];r[A]=Z
        elif token=='compareGuard':
            r[T]=cut(r[X],r[H],r[T]);r[H]=r[X]=Z
            r[X]=r[Y];r[Y]=Z;r[H]=r[D];r[D]=Z
            r[T]=cut(r[X],r[H],r[T]);r[H]=r[X]=Z
        else:require(token=='breakAX','symbolic token')
    dv,hv=add(d,x),add(h,y)
    heads=[ii(ex(dv,uu(dv,hv)),hv),ii(uu(dv,uu(a,hv)),uu(a,uu(dv,hv))),
       ii(mm(hv,dv),ii(ee(hv,a),mm(a,dv))),ii(ee(hv,dv),ii(mm(a,hv),mm(a,dv))),
       ex(dv,ee(hv,dv)),ii(uu(dv,a),ii(uu(dv,ii(a,hv)),uu(dv,hv)))]
    rho=ii(ii(ii(hv,d),dv),ii(ii(dv,hv),ii(a,hv)))
    gamma=ii(a,uu(a,a));point=ii(a,mm(a,dv));v=ii(mm(hv,dv),uu(a,mm(hv,dv)))
    ss=uu(dv,conj(ii(mm(hv,dv),point),ii(mm(a,dv),a)))
    qq=uu(a,ii(ss,nn(point)));gate=ii(ii(v,qq),z)
    guarded=cut(a,dv,cut(a,hv,gate))
    stack=w
    for term in [t,uu(d,h),rho]+heads+[gamma]:stack=pp(term,stack)
    expected=[n,guarded,stack,Z,Z,Z,Z,Z,tail]
    require(r==expected,'nine-register source identity')
    return dict(status='PASS',entries=10,visible='guarded G_z',stack='q1,...,q9,t;w',
                offset=0,cache=0,residual='tail',all_registers=True,
                guards_symbolic=True,scratch_preconditions=True)

def main():
    tree=json.loads((HERE/'grammar.tree.json').read_text())
    names=json.loads((HERE/'nodes.json').read_text())
    ins=json.loads((HERE/'instructions.json').read_text())
    sites=json.loads((HERE/'sites.json').read_text())
    ww=word(tree);templates,ports=full_templates(ww)
    require(ins==templates.rows,'entire instruction graph versus independent arithmetic templates')
    ownsites,ownins=resolve_graph(names,tree)
    require(ownsites==sites and ownins==ins,'independent source-tree graph resolution')
    alg=symbolic_AX(ww)
    # Check the two newly used macros against literal primitive steps.
    durations=0
    for z in range(10):
        for tail in range(10):
            r=[7,0,11,13,17,19,0,0,b.pair(z,tail)]
            q=Templates();q.atom('readX');q.atom('moveXT')
            ar=Arithmetic(r);ar.atom('readX');ar.atom('moveXT')
            require(ar.r==[7,z,11,13,17,19,0,0,tail],'new macro arithmetic')
            require(b.step_exact(q.rows,0,r,ar.cost)==(len(q.rows),ar.r),'new macro exact clock')
            durations+=1
    receipt=dict(status='PASS',source_sites=len(ins),source_outcomes=sum(2 if x[0]=='dec' else 1 for x in ins),
        expanded_macro_tokens=len(ww),ports=ports,algebra=alg,new_macro_duration_examples=durations,
        inherited_template_sha256=hashlib.sha256(BASE.read_bytes()).hexdigest(),
        source_binding='All source instruction rows and resolved edges agree with independent primitive templates.',
        proof_status='Finite expression/cfg identity plus inherited uniform template proofs; no binary state-count claim.')
    (HERE/'source_binding_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
