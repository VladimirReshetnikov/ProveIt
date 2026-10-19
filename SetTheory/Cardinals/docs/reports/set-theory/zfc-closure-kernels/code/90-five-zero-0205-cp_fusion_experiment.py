#!/usr/bin/env python3
"""Exact symbolic AX re-emission controls for equivalent CP presentations.

The four-variable presentations reserve variable zero and shift only the CP
labels a,b,c to a+1,b+1,c+1. All original logical rows, GIC, vacuity, reads,
and gate operations are retained. Emitted Wade tables are raw cost controls,
not calibrated consistency machines.
"""
from __future__ import annotations
import argparse, json, itertools
from functools import lru_cache
from pathlib import Path
from codec_source_experiment import DEFAULT, HERE
from check_codec_experiments import compile_wade, Macro, P, canonical

MACROS={166:'a',121:'b',168:'c',171:'zero',177:'one',119:'imp',181:'rel',
        182:'eq',180:'all',218:'not',178:'and',183:'exists',176:'read_b',
        158:'read_u',208:'move_u',192:'copy_c',131:'gate',211:'restore_c',197:'a_to_b',
        -1:'A',-2:'B',-3:'C',-4:'two',-5:'three'}
TAIL=[192,131,211,197,131]
def Imp(a,b):return ('imp',a,b)
def Rel(a,b):return ('rel',a,b)
def Eq(a,b):return ('eq',a,b)
def All(a,b):return ('all',a,b)
def Not(a):return Imp(a,1)
def And(a,b):return Not(Imp(a,Not(b)))
def Ex(a,b):return Not(All(a,Not(b)))

def old_C(a,b,c,lift=False):
    cover=All(b,Imp(All(c,Imp(Rel(c,b),Rel(c,a))),Rel(b,c)))
    tr=All(c,Imp(Rel(c,a),Rel(c,b)))
    pow_=Ex(c,And(And(cover,Rel(c,b)),tr)) if lift else Ex(c,And(cover,Rel(c,b)))
    body=pow_ if lift else And(pow_,tr)
    return Ex(b,And(All(a,Imp(Rel(a,b),body)),Rel(c,b)))

def new_C(mode):
    if mode=='old':return old_C('a','b','c')
    if mode=='scope_lift':return old_C('a','b','c',True)
    if mode=='old_shift':return old_C('A','B','C')
    if mode=='fixed_old':return All(3,old_C(1,2,3))
    if mode=='fixed_scope_lift':return All(3,old_C(1,2,3,True))
    fixed=mode.startswith('fixed_')
    if fixed:mode=mode[6:]
    a,b,c,z=(1,2,3,0) if fixed else ('A','B','C',0)
    # Each subset's dummy binder can shadow a variable unused in that subset.
    subset_z_x=All(c,Imp(Rel(c,z),Rel(c,a)))
    subset_z_V=All(a,Imp(Rel(a,z),Rel(a,b)))
    if mode=='absorbed':
        matrix=Imp(subset_z_x,And(Rel(z,c),subset_z_V))
    elif mode in ('fused','fused_reverse'):
        trans=Imp(Rel(z,a),Rel(z,b))
        cover=Imp(subset_z_x,Rel(z,c))
        matrix=And(trans,cover) if mode=='fused' else And(cover,trans)
    else:raise ValueError(mode)
    core=Ex(b,And(All(a,Imp(Rel(a,b),Ex(c,And(All(z,matrix),Rel(c,b))))),Rel(c,b)))
    return All(c,core) if fixed else core

def G(a,b,c):
    w=Ex(b,And(c,Rel(b,c)))
    return Ex(c,And(All(a,Imp(Rel(a,b),All(b,Imp(c,w)))),All(b,Imp(Rel(b,c),Ex(a,c)))))

def rows():
    a,b,c,u,h='a','b','c','u','h'
    return [All(a,h),Imp(Imp(Imp(c,u),a),Imp(Imp(a,c),Imp(b,c))),
      Imp(Eq(c,a),Imp(Eq(c,b),Eq(a,b))),Imp(Ex(a,All(a,b)),b),
      Imp(Eq(c,a),Imp(Rel(c,b),Rel(a,b))),Imp(All(a,All(b,c)),All(b,All(a,c))),
      Imp(Eq(a,b),Imp(Rel(c,a),Rel(c,b))),Imp(All(a,Imp(b,c)),Imp(All(a,b),All(a,c))),Ex(a,Eq(a,b))]

def bundle(C):
    a,b,c='a','b','c'
    return And(And(C,G(a,b,c)),And(Imp(Rel(a,b),All(c,Rel(a,b))),Imp(Eq(a,b),All(c,Eq(a,b)))))

def emit(f):
    leaves={'a':[166],'b':[121],'c':[168],'A':[-1],'B':[-2],'C':[-3],'u':[171,158,208],0:[171],1:[177],2:[-4],3:[-5]}
    if not isinstance(f,tuple):return leaves[f]
    if f[0]=='imp' and f[2]==1:
        inner=f[1]
        if isinstance(inner,tuple) and inner[0] in ('imp','all') and isinstance(inner[2],tuple) and inner[2][0]=='imp' and inner[2][2]==1:
            return emit(inner[1])+emit(inner[2][1])+[178 if inner[0]=='imp' else 183]
        return emit(inner)+[218]
    return emit(f[1])+emit(f[2])+[{'imp':119,'rel':181,'eq':182,'all':180}[f[0]]]

def symbolic(program):
    stack=['old_top'];b='h';u=None;events=[]
    for m in program:
        if m in (166,121,168,171,177,-1,-2,-3,-4,-5):stack.append({166:'a',121:b,168:'c',171:0,177:1,-1:'A',-2:'B',-3:'C',-4:2,-5:3}[m])
        elif m in (119,181,182,180,178,183):
            y,x=stack.pop(),stack.pop();stack.append({119:Imp,181:Rel,182:Eq,180:All,178:And,183:Ex}[m](x,y))
        elif m==218:stack[-1]=Not(stack[-1])
        elif m==176:events.append(('read_b',len(stack)));b='b'
        elif m==158:u='u';events.append(('read_u',len(stack)))
        elif m==208:assert stack[-1]==0 and u=='u';stack[-1]='u';u=None
        elif m in TAIL:events.append((MACROS[m],len(stack)))
        else:raise AssertionError(m)
    return stack,events

def build(raw,mode):
    old={int(k):tuple(map(tuple,v)) for k,v in raw['nodes'].items()}
    @lru_cache(None)
    def expansion(q):
        if q in MACROS:return (q,)
        assert all(e[0]=='N' for e in old[q]),q
        return sum((expansion(e[1]) for e in old[q]),())
    oldprogram=list(expansion(1))
    expected=['old_top']+rows()+[bundle(new_C('old'))]
    assert symbolic(oldprogram)[0]==expected
    assert oldprogram[:4]==[166,121,180,176] and oldprogram[-5:]==TAIL
    program=[166,121,180,176]+sum((emit(f) for f in rows()[1:]),[])+emit(bundle(new_C(mode)))+TAIL
    assert symbolic(program)[0]==['old_top']+rows()+[bundle(new_C(mode))]
    assert symbolic(program)[1]==symbolic(oldprogram)[1]
    if mode=='old':assert program==oldprogram
    patterns=[(list(expansion(q)),q) for q in range(2,115) if q not in MACROS]
    best=[None]*(len(program)+1);best[-1]=[]
    for i in reversed(range(len(program))):
        options=[[program[i]]+best[i+1]]
        for word,q in patterns:
            j=i+len(word)
            if program[i:j]==word:options.append([q]+best[j])
        best[i]=min(options,key=lambda x:(len(x),repr(x)))
    rebuilt=sum((list(expansion(q)) if q>=0 else [q] for q in best[0]),[])
    assert rebuilt==program
    nodes={};intern={}
    def pair(a,b):
        key=a,b
        if key not in intern:intern[key]=len(nodes);nodes[intern[key]]=key
        return ('N',intern[key])
    @lru_cache(None)
    def rawclone(e):
        if e[0]!='N':return e
        return pair(*(rawclone(x) for x in old[e[1]]))
    lifted={-1:pair(rawclone(('N',166)),('I',1)),-2:pair(rawclone(('N',121)),('I',1)),-3:pair(rawclone(('N',168)),('I',1))}
    lifted[-4]=pair(rawclone(('N',177)),('I',1))
    lifted[-5]=pair(lifted[-4],('I',1))
    tokens=[lifted[q] if q<0 else rawclone(('N',q)) for q in best[0]]
    AX=tokens[-1]
    for token in reversed(tokens[:-1]):AX=pair(token,AX)
    @lru_cache(None)
    def clone(e):
        if e==('N',1):return AX
        if e[0]!='N':return e
        return pair(*(clone(x) for x in old[e[1]]))
    root=clone(('N',raw['root']))
    seen=set();leaves=[]
    def walk(e,p):
        if e[0]!='N':leaves.append((p,e));return
        seen.add(e[1]);walk(nodes[e[1]][0],p+'0');walk(nodes[e[1]][1],p+'1')
    walk(root,'')
    if mode=='old':
        assert canonical(raw['nodes'],raw['root'])==canonical({str(k):v for k,v in nodes.items()},root[1])
    d={'variant':'cp_'+mode,'root':root[1],'nodes':{i:nodes[i] for i in sorted(seen)},
       'scope':'Equivalent CP presentation and exact AX stack contract; no new full proof-search calibration or binary simulation proof.',
       'metrics':{'register_dag_nodes':len(seen),'instruction_occurrences':len(leaves),'max_depth':max(len(p) for p,e in leaves),'max_zero_run':max(max(map(len,p.split('1'))) for p,e in leaves),
                  'AX_macro_tokens':len(program),'AX_reused_tokens':len(tokens)},'AX_program':program,'symbolic_AX_contract':True,'read_and_gate_events':symbolic(program)[1]}
    cases=0
    if mode in ('old_shift','absorbed','fused','fused_reverse'):
        for macro,reg in [(-1,4),(-2,5),(-3,3)]:
            m=Macro(nodes,lifted[macro][1])
            for value in range(12):
                for top in (0,1,7):
                    for tail in (0,1,5):
                        initial=[11,top,tail,13,17,19,0,0,23];initial[reg]=value
                        wanted=initial[:];wanted[1]=value+1;wanted[2]=P(top,tail)
                        result,_=m.execute(initial);assert result==wanted,(macro,initial,result,wanted)
                        cases+=1
    if mode.startswith('fixed_'):
        for macro,value in [(-4,2),(-5,3)]:
            m=Macro(nodes,lifted[macro][1])
            for top in (0,1,7):
                for tail in (0,1,5):
                    initial=[11,top,tail,13,17,19,0,0,23]
                    wanted=initial[:];wanted[1]=value;wanted[2]=P(top,tail)
                    result,_=m.execute(initial);assert result==wanted
                    cases+=1
    d['lifted_variable_macro_contract_cases']=cases
    return d

def finite_equivalence():
    """Compare local CP bodies on all relations with at most three objects.

    Here 1 is logical falsity, not a variable-dependent relation atom. Hence
    arbitrary (including reflexive) relations are permitted. This complements
    the unbounded ordinary logical proof; it is not proof-search calibration.
    """
    def body(mode):
        f=new_C(mode)
        inner=f[1][2][1]  # remove existential V, represented by Not All Not
        universal_x=inner[1][1]  # first argument of the outer And
        return universal_x[2][2]
    forms=[body(m) for m in ('old_shift','absorbed','fused','fused_reverse')]
    counts=[]
    for n in (1,2,3):
        cases=0
        for bits in range(1<<(n*n)):
            def label(x):return {'A':1,'B':2,'C':3}.get(x,x)
            @lru_cache(None)
            def ev(f,env):
                if isinstance(f,int):assert f==1;return False
                op,a,b=f
                if op=='imp':return not ev(a,env) or ev(b,env)
                if op=='rel':return bool(bits>>(env[label(a)]*n+env[label(b)])&1)
                if op=='eq':return env[label(a)]==env[label(b)]
                assert op=='all'
                j=label(a)
                return all(ev(b,env[:j]+(z,)+env[j+1:]) for z in range(n))
            for x,v in itertools.product(range(n),repeat=2):
                values=[ev(f,(0,x,v,0)) for f in forms]
                assert len(set(values))==1,(n,bits,x,v,values)
                cases+=1
        counts.append({'domain_size':n,'relations':1<<(n*n),'local_assignments':cases})
    return {'status':'PASS','forms':['old_shift','absorbed','fused','fused_reverse'],'cases':sum(x['local_assignments'] for x in counts),'by_domain':counts,'scope':'Exhaustive finite ordinary-logic diagnostic; falsity is a logical constant.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=DEFAULT);p.add_argument('--backend',type=Path)
    p.add_argument('--output-dir',type=Path,default=HERE/'cp-fusion-results');a=p.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    raw=json.loads(a.source.read_text());results=[]
    for mode in ('old','scope_lift','old_shift','absorbed','fused','fused_reverse','fixed_old','fixed_scope_lift','fixed_absorbed','fixed_fused','fixed_fused_reverse'):
        d=build(raw,mode);r={'variant':d['variant'],**d['metrics'],'symbolic_AX_contract':True,'lifted_variable_macro_contract_cases':d['lifted_variable_macro_contract_cases']}
        (a.output_dir/(d['variant']+'.json')).write_text(json.dumps(d,indent=2)+'\n')
        if a.backend:r['compiler_control']=compile_wade(d,a.backend,a.output_dir)
        results.append(r)
    r={'status':'PASS_EXACT_SYMBOLIC_AX_AND_LOCAL_MACRO_CONTROLS','scope':'Raw complete-logic source/compiler cost experiment; no newly calibrated machine.','finite_CP_equivalence':finite_equivalence(),'results':results}
    (a.output_dir/'summary.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

if __name__=='__main__':main()
