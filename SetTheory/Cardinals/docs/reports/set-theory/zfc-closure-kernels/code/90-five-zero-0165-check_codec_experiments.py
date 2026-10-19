#!/usr/bin/env python3
"""Independent arithmetic and literal-register checks for codec experiments."""
from __future__ import annotations
import argparse, json, math, sys
from pathlib import Path
from functools import lru_cache
from codec_source_experiment import DEFAULT, HERE, construct

P=lambda a,b:(a+b)*(a+b+1)//2+b
def unP(n):
    s=(math.isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2;return s-b,b

def code(variant,op,a,b):
    if variant=='uniform4': k,t={'imp':(4,0),'rel':(4,1),'all':(4,2),'eq':(4,3)}[op]
    elif variant=='uniform4_swap': k,t={'imp':(4,0),'rel':(4,1),'all':(4,3),'eq':(4,2)}[op]
    elif variant=='prefix_2488': k,t={'imp':(2,0),'rel':(4,1),'all':(8,3),'eq':(8,7)}[op]
    elif variant=='prefix_2848': k,t={'imp':(2,0),'rel':(8,1),'all':(4,3),'eq':(8,5)}[op]
    elif variant=='atom_parity3':
        if op in ('rel','eq'):return 3*P(2*a+int(op=='eq'),b)+1
        k,t={'imp':(3,0),'all':(3,2)}[op]
    else:raise ValueError(variant)
    return k*P(a,b)+t

def decode_root(v,n):
    if n==0:return ('truth',)
    if v=='atom_parity3':
        tag=n%3;a,b=unP(n//3)
        if tag==1:return ('eq' if a%2 else 'rel',a//2,b)
        return ('imp' if tag==0 else 'all',a,b)
    if v in ('uniform4','uniform4_swap'):
        names=('imp','rel','all','eq') if v=='uniform4' else ('imp','rel','eq','all')
        return (names[n%4],*unP(n//4))
    if n%2==0:return ('imp',*unP(n//2))
    if v=='prefix_2488':
        if n%4==1:return ('rel',*unP(n//4))
        return ('all' if n%8==3 else 'eq',*unP(n//8))
    if n%4==3:return ('all',*unP(n//4))
    return ('rel' if n%8==1 else 'eq',*unP(n//8))

def inc(p):
    j=p.rfind('0')
    return p[:j]+'1'+'0'*(len(p)-j-1) if j>=0 else '0'*len(p)
def strip(p,b,k):
    while k:
        assert p
        k-=int(p[-1]==b);p=p[:-1]
    return p

class Macro:
    def __init__(self,nodes,q):
        nodes={int(i):tuple(map(tuple,p)) for i,p in nodes.items()}
        top=max(nodes)+1;nodes[top]=('N',q),('H',)
        self.rows=[];paths={}
        def walk(e,p):
            if e[0]!='N':paths[p]=len(self.rows);self.rows.append((e,p));return
            walk(nodes[e[1]][0],p+'0');walk(nodes[e[1]][1],p+'1')
        walk(('N',top),'')
        def lookup(p):
            for j in range(len(p)+1):
                if p[:j] in paths:
                    assert set(p[j:])<={'0'}
                    return paths[p[:j]]
            while p not in paths:p+='0'
            return paths[p]
        self.code=[]
        for e,p in self.rows:
            if e[0]=='H':self.code.append(('H',));continue
            if e[0]=='I':self.code.append(('I',e[1],lookup(inc(p))))
            elif e[0]=='D':self.code.append(('D',e[1],lookup(inc(p)),lookup(inc(strip(p,'0',1)))))
            elif e[0]=='B':self.code.append(('J',lookup(inc(strip(p,'0',e[1])))))
            elif e[0]=='C':self.code.append(('J',lookup(strip(p,'1',e[1]))))
            else:raise AssertionError(e)
        self.start=lookup('')
    def execute(self,regs):
        r=list(regs);pc=self.start
        for steps in range(1,1000001):
            e=self.code[pc]
            if e[0]=='H':return r,steps
            if e[0]=='I':r[e[1]]+=1;pc=e[2]
            elif e[0]=='D':
                if r[e[1]]:r[e[1]]-=1;pc=e[2]
                else:pc=e[3]
            else:pc=e[1]
        raise AssertionError('macro test exhausted finite budget')

def canonical(nodes,q):
    @lru_cache(None)
    def go(e):
        if e[0]!='N':return e
        return ('N',go(tuple(nodes[str(e[1])][0])),go(tuple(nodes[str(e[1])][1])))
    return go(('N',q))

def check(raw,variant):
    d=construct(raw,variant)
    if variant=='uniform4':
        out={str(k):v for k,v in d['nodes'].items()}
        assert canonical(raw['nodes'],raw['root'])==canonical(out,d['root'])
    roundtrips=0;decodings=0;cases=0;maxsteps=0
    for op in ['imp','rel','all','eq']:
        for a in range(24):
            for b in range(24):
                n=code(variant,op,a,b)
                assert decode_root(variant,n)==(('truth',) if n==0 else (op,a,b))
                if n>0:assert a<n and b<n
                roundtrips+=1
    for n in range(1,20000):
        op,a,b=decode_root(variant,n);assert code(variant,op,a,b)==n
        assert a<n and b<n;decodings+=1
    assert code(variant,'rel',0,0)==1
    for macro,op in [(119,'imp'),(181,'rel'),(180,'all'),(182,'eq')]:
        m=Macro(d['nodes'],d['constructors'][str(macro)])
        for a in range(9):
            for b in range(9):
                for tail in [0,1,3,11]:
                    before=[7,b,P(a,tail),5,13,17,0,0,19]
                    expected=before[:];expected[1]=code(variant,op,a,b);expected[2]=tail
                    after,steps=m.execute(before);assert after==expected,(variant,op,a,b,tail,after,expected)
                    cases+=1;maxsteps=max(maxsteps,steps)
    return {'variant':variant,'roundtrips':roundtrips,'decoded_positive_codes':decodings,
            'literal_register_contracts':cases,'max_literal_register_steps':maxsteps,
            'exact_old_source_control':variant=='uniform4'}

def compile_wade(d,backend_path,outdir):
    sys.path.insert(0,str(backend_path));import TMBuilder
    b=TMBuilder.TMBuilder();names=['nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist']
    registers=[b.reg(n) for n in names]
    dense={q:i for i,q in enumerate(d['nodes'])}
    def leaf(e):
        if e[0]=='N':return dense[e[1]]
        if e[0]=='H':return 'halt'
        if e[0]=='I':return registers[e[1]].inc
        if e[0]=='D':return registers[e[1]].decnz
        return f"_{'break' if e[0]=='B' else 'continue'}.{e[1]}"
    labels={q:('main().0' if q==d['root'] else f'codec_{dense[q]}.0') for q in dense}
    for q,p in d['nodes'].items():
        s=TMBuilder.Sequence(tuple(leaf(e) for e in p));s.name=labels[q];b.sequences.append(s)
    b.generate();b.tm.gc()
    # Invert direct source-node edges and require one decision state per source node.
    assert all((labels[q],bit) in b.tm.states for q in dense for bit in ['0','1'])
    for q,p in d['nodes'].items():
        for bit,e in enumerate(p):
            action=b.tm.states[labels[q],str(bit)]
            if e[0]=='N':assert (action.write,action.direction,action.nextstate)==(str(bit),'R',labels[e[1]])
            if e[0] in ('I','D','H'):assert (action.write,action.direction,action.nextstate)==(str(bit),'R',leaf(e))
    path=outdir/(d['variant']+'-wade.tm');b.tm.save(str(path))
    states={q for q,bit in b.tm.states};framework={q for q in states if q[0].isdigit()}
    missing=[(q,bit) for q in sorted(states) for bit in ['0','1'] if (q,bit) not in b.tm.states]
    return {'variant':d['variant'],'working_states':len(states),'decision_states':len(states-framework),
            'framework_states':len(framework),'rows':len(b.tm.states),'missing_rows':missing,
            'terminal_targets':sorted({a.nextstate for a in b.tm.states.values()}-states),
            'table_file':path.name,'scope':'Generated Wade compiler control; not a verified alternative consistency machine.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=DEFAULT)
    p.add_argument('--backend',type=Path);p.add_argument('--output-dir',type=Path,default=HERE/'codec-source-results')
    a=p.parse_args();raw=json.loads(a.source.read_text());a.output_dir.mkdir(parents=True,exist_ok=True)
    tests=[];builds=[]
    for variant in ['uniform4','uniform4_swap','prefix_2488','prefix_2848','atom_parity3']:
        tests.append(check(raw,variant))
        if a.backend:builds.append(compile_wade(construct(raw,variant),a.backend,a.output_dir))
    r={'status':'PASS','tests':tests,'compiler_controls':builds}
    (a.output_dir/'checks.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

if __name__=='__main__':main()
