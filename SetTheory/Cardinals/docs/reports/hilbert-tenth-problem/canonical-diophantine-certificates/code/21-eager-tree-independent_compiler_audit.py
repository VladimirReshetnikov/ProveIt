#!/usr/bin/env python3
"""Independent lambda substitution semantics and tree-expression context reduction."""
import hashlib, importlib.util, json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('comp',HERE/'eager_compiler.py');comp=importlib.util.module_from_spec(spec);spec.loader.exec_module(comp)

# Standard de Bruijn substitution and weak call-by-value reduction.
def shift(t,d,c=0):
    if t[0]=='v': return ('v',t[1]+d if t[1]>=c else t[1])
    if t[0]=='l': return ('l',shift(t[1],d,c+1))
    return ('a',shift(t[1],d,c),shift(t[2],d,c))
def subst(t,j,s):
    if t[0]=='v':return s if t[1]==j else t
    if t[0]=='l':return ('l',subst(t[1],j+1,shift(s,1)))
    return ('a',subst(t[1],j,s),subst(t[2],j,s))
def beta(body,arg):return shift(subst(body,0,shift(arg,1)),-1)
def lstep(t):
    assert t[0]=='a'
    if t[1][0]!='l':return ('a',lstep(t[1]),t[2])
    if t[2][0]!='l':return ('a',t[1],lstep(t[2]))
    return beta(t[1][1],t[2])
def leval(t,budget=10000):
    seen=set();steps=0
    while t[0]!='l':
        if t in seen:return None,'cycle',steps
        if steps>=budget:return None,'fuel',steps
        seen.add(t);t=lstep(t);steps+=1
    return t,'value',steps
def named(t,env=()):
    if t[0]=='v':return comp.V(env[t[1]])
    if t[0]=='l':
        x=f'b{len(env)}';return comp.Lam([x],named(t[1],(x,)+env))
    return comp.A(named(t[1],env),named(t[2],env))

# Tree values are atom IDs in an independent hash-consing arena. Applications
# are explicit expression nodes, reduced only in deterministic CBV contexts.
@dataclass(frozen=True)
class App:
    f:object
    a:object
class Ref:
    def __init__(self):self.nodes=[];self.ids={}
    def value(self,*v):
        if v not in self.ids:self.ids[v]=len(self.nodes);self.nodes.append(v)
        return self.ids[v]
    def convert(self,alg,i,cache):
        if i not in cache:
            n=alg.nodes[i]
            if n[0]=='A':cache[i]=App(self.convert(alg,n[1],cache),self.convert(alg,n[2],cache))
            else:
                assert n[0] in ('L','S','F'),n
                cache[i]=self.value(n[0],*(self.convert(alg,j,cache) for j in n[1:]))
        return cache[i]
    def step(self,e):
        if isinstance(e.f,App):return App(self.step(e.f),e.a)
        if isinstance(e.a,App):return App(e.f,self.step(e.a))
        n=self.nodes[e.f];a=e.a
        if n[0]=='L':return self.value('S',a)
        if n[0]=='S':return self.value('F',n[1],a)
        m=self.nodes[n[1]]
        if m[0]=='L':return n[2]
        if m[0]=='S':return App(App(n[2],a),App(m[1],a))
        return App(App(a,m[1]),m[2])
    def run(self,e,budget=100000,cycle=True):
        seen=set();count=0
        while isinstance(e,App):
            if cycle and e in seen:return None,'cycle',count
            if count>=budget:return None,'fuel',count
            if cycle:seen.add(e)
            e=self.step(e);count+=1
        return e,'value',count

@lru_cache(None)
def terms(size,depth):
    if size==1:return tuple(('v',i) for i in range(depth))
    out=[('l',t) for t in terms(size-1,depth+1)]
    for a in range(1,size-1):
        for x in terms(a,depth):
            for y in terms(size-1-a,depth):out.append(('a',x,y))
    return tuple(out)

def main():
    alg=comp.Algebra();ref=Ref();cache={};tested=0;cycles=0;maxcost=0;universal=[]
    for size in range(2,9):
      for t in terms(size,0):
        lv,status,lsteps=leval(t)
        compiled=alg.compile(named(t));expr=ref.convert(alg,compiled,cache)
        got,stat,cost=ref.run(expr)
        if status=='cycle':
            assert stat in ('cycle','fuel');cycles+=1;continue
        assert status=='value' and stat=='value',(t,status,stat)
        expected=ref.convert(alg,alg.compile(named(lv)),cache)
        assert not isinstance(expected,App)
        # Exact equality holds here for compilation of the closed substitution result.
        assert got==expected,(t,lv,got,expected)
        direct,dcost=alg.eval(compiled)
        assert ref.convert(alg,direct,cache)==got and dcost==cost
        tested+=1;maxcost=max(maxcost,cost)
        if len(universal)<24 and t[0]=='a':universal.append(t)
    # Selected tests of lexical shadowing and captured higher-order values.
    I=('l',('v',0));dup=('l',('a',('v',0),('v',0)));omega=('a',dup,dup)
    special=[('l',omega),('a',I,I),('a',('l',('l',('v',1))),I),('a',dup,I),('a',('l',I),omega)]
    # Build and independently reduce the literal fixed universal tree.
    literal=json.loads((HERE/'literal_universal_tree.json').read_text());loaded=[]
    for i,n in enumerate(literal['nodes']):
        assert n[0] in ('L','S','F') and all(type(j)==int and 0<=j<i for j in n[1:])
        loaded.append(ref.value(n[0],*(loaded[j] for j in n[1:])))
    U=loaded[literal['root']]
    assert U==ref.convert(alg,alg.compile(comp.UNIVERSAL),cache)
    utests=[]
    for t in universal+special:
        quoted=alg.compile(comp.quote_debruijn(t));qv=ref.convert(alg,quoted,cache)
        assert isinstance(qv,int)
        lv,status,_=leval(t)
        got,stat,cost=ref.run(App(U,qv),budget=40000,cycle=False)
        assert (stat=='value')==(status=='value'),(t,status,stat)
        utests.append({'source_status':status,'target_status':stat,'target_kernel_calls':cost})
    # Church boolean observations distinguish exact results using opaque target sentinels.
    # For true/false, applying the interpreted result to two distinct target values
    # must select the corresponding value; this is stronger than one termination test.
    left=ref.value('L');right=ref.value('S',left)
    booltests=[]
    for name,t,want in [('true',('l',('l',('v',1))),left),('false',('l',('l',('v',0))),right)]:
        q=ref.convert(alg,alg.compile(comp.quote_debruijn(t)),cache)
        out,status,cost=ref.run(App(App(App(U,q),left),right),cycle=False)
        assert status=='value' and out==want
        booltests.append({'name':name,'selects': 'left' if out==left else 'right','kernel_calls':cost})
    # Constant abstraction must never eagerly normalize an unused x-free computation.
    suspended=comp.Lam('unused',comp.OMEGA)
    suspended_tree=ref.convert(alg,alg.compile(suspended),cache)
    assert isinstance(suspended_tree,int)
    forced=ref.run(App(suspended_tree,left),budget=10000)
    assert forced[1]=='cycle'
    ans={'closed_debruijn_terms_checked':tested,'exact_compiled_normal_form_equalities':tested,'cyclic_sources_checked':cycles,'max_direct_target_kernel_calls':maxcost,'universal_interpreter_tests':utests,'exact_boolean_observations':booltests,'suspended_omega_compiles_as_value':True,'forced_suspended_omega_exact_cycle':True,'compiler_sha256':hashlib.sha256((HERE/'eager_compiler.py').read_bytes()).hexdigest()}
    (HERE/'independent_compiler_receipt.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
if __name__=='__main__':main()
