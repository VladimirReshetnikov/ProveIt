"""Exhaustive small-instance and seeded property checks; not a formal proof."""
from compiler import *
from itertools import product, combinations
from pathlib import Path
import random, json, time

COUNTS={}
def check(name,condition):
    if not condition: raise AssertionError(name)
    COUNTS[name]=COUNTS.get(name,0)+1

def word_sig(w,labels,I):
    s=identity_signature(len(labels))
    for a in w: s=signature_compose(s,atom_signature(a,labels,I))
    return s

def direct_dfa(w,labels,I):
    F={a:0 for a in labels};ok=True
    for b in w:
        ok=ok and not F[b]
        F={a:int((a,b) in I and (F[a] or b>a)) for a in labels}
    return int(ok)

def test_resource():
    for u,v,a,b in product(range(5),repeat=4):
        x=((u,),(v,));y=((a,),(b,));z=compose(x,y)
        net={'a':Transition(*x),'b':Transition(*y)}
        check('commutation criterion', independent(net['a'],net['b'])==(z==compose(y,x)))
        for m in range(11):
            actual=run('ab',net,(m,))
            expected=None if m<z[0][0] else (m-z[0][0]+z[1][0],)
            check('exact resource product',actual==expected)
    for u,v,k in product(range(8),range(8),range(10)):
        x=((u,),(v,));s=((0,),(0,))
        for _ in range(k):s=compose(s,x)
        check('exact resource power',s==power(x,k))

def test_traces():
    labels=('a','b','c');pairs=list(combinations(labels,2))
    for mask in range(8):
        I=frozenset((a,b) for j,(x,y) in enumerate(pairs) if mask>>j&1
                    for a,b in [(x,y),(y,x)])
        for T in range(7):
            words=list(product(labels,repeat=T));parent={w:w for w in words}
            def root(w):
                while parent[w]!=w:
                    parent[w]=parent[parent[w]];w=parent[w]
                return w
            def union(w,v):
                a,b=root(w),root(v)
                if a!=b: parent[max(a,b)]=min(a,b)
            for w in words:
                for i in range(T-1):
                    if (w[i],w[i+1]) in I:
                        union(w,w[:i]+(w[i+1],w[i])+w[i+2:])
            for w in words:
                s=word_sig(w,labels,I)
                check('lexicographic cross-section',s[0]==int(w==root(w)))
                check('DFA versus signature',s[0]==direct_dfa(w,labels,I))
                check('signature square saturation',signature_compose(s,s)==signature_compose(signature_compose(s,s),s))
        short=[w for T in range(4) for w in product(labels,repeat=T)]
        for u in short:
            for v in short:
                check('signature composition',word_sig(u+v,labels,I)==signature_compose(word_sig(u,labels,I),word_sig(v,labels,I)))

def random_expr(rng,depth=4):
    if not depth or rng.random()<.3: return Atom(rng.choice('abc'))
    if rng.random()<.5: return Concat(random_expr(rng,depth-1),random_expr(rng,depth-1))
    return Repeat(random_expr(rng,depth-1),rng.choice(('x','y','z')))

def test_compilation():
    rng=random.Random(20260930)
    net={'a':Transition((1,0),(0,1)),
         'b':Transition((2,0),(0,2)),
         'c':Transition((0,1),(1,0))}
    I=independence(net);labels=tuple(sorted(net))
    for _ in range(160):
        e=random_expr(rng)
        vals={k:rng.randrange(6) for k in sorted(parameters(e))}
        word=expanded(e,vals)
        res,sig=evaluate(e,net,vals,I)
        check('compressed resource evaluation',run(word,net,res[0])==res[1])
        check('compressed signature evaluation',sig==word_sig(word,labels,I))
        cap={k:min(v,2) for k,v in vals.items()}
        check('cap-at-two theorem',sig==evaluate(e,net,cap,I)[1])
        for canonical in (False,True):
            b=Compiler(net,canonical=canonical).compile(e)
            inputs={f'k:{k}':v for k,v in vals.items()}
            inputs.update({f'm:{j}':res[0][j]+1 for j in range(2)})
            inputs.update({f'n:{j}':res[1][j]+1 for j in range(2)})
            env=b.construct(inputs)
            check('compiled acceptance', (b.energy(env)==0)==(not canonical or sig[0]==1))
            check('quadratic residual degree', all(r.degree<=2 for r in b.residuals))
            wrong=dict(inputs);wrong['n:0']+=1
            check('wrong endpoint rejected',b.energy(b.construct(wrong))>0)
            if res[0][0]>0:
                bad=dict(inputs);bad['m:0']=res[0][0]-1
                check('insufficient input rejected',b.energy(b.construct(bad))>0)
    # Every zero exponent must annihilate even a resource-demanding body.
    net2={'+':Transition((0,),(1,)),'-':Transition((1,),(0,))}
    e=Repeat(word_expression('-+'),'k')
    for k in range(6):
        b=Compiler(net2,canonical=True).compile(e)
        for m in range(3):
            env=b.construct({'k:k':k,'m:0':m,'n:0':m})
            check('zero-repeat catalyst edge case',(b.energy(env)==0)==(k==0 or m>=1))
    # One-letter corruption of a unique valid witness is always rejected.
    examples=[multiplication_example(),
              ({'a':Transition((0,),(1,)),'b':Transition((0,),(2,))},
               Concat(Repeat(Atom('a'),'x'),Repeat(Atom('b'),'y')))]
    for idx,(net,e) in enumerate(examples):
        values={'x':2,'y':3,'z':15} if idx==0 else {'x':2,'y':3}
        res,sig=evaluate(e,net,values)
        b=Compiler(net,canonical=True).compile(e)
        inp={f'k:{k}':v for k,v in values.items()};inp.update({'m:0':res[0][0],'n:0':res[1][0]})
        env=b.construct(inp);check('mutation baseline',b.energy(env)==0)
        for name,_,_ in b.recipes:
            for d in (-1,1):
                if env[name]+d<0:continue
                bad=dict(env);bad[name]+=d
                check('single-coordinate mutation rejected',b.energy(bad)>0)
    # An enormous execution is handled without expansion.
    net,e=multiplication_example();b=Compiler(net,canonical=True).compile(e)
    x=10**100;y=10**120;z=2*x*y+3
    env=b.construct({'k:x':x,'k:y':y,'k:z':z,'m:0':0,'n:0':0})
    check('huge exponent certificate',b.energy(env)==0)
    return {'example_witnesses':len(b.recipes),'example_equations':len(b.residuals),
            'huge_execution_length_decimal_digits':len(str(2*z)),
            'max_witness_decimal_digits':len(str(max(env.values())))}

def main():
    start=time.perf_counter();test_resource();test_traces();info=test_compilation()
    report={'status':'PASS','seed':20260930,'counts':COUNTS,'total_checks':sum(COUNTS.values()),
            'illustration':info,'elapsed_seconds':round(time.perf_counter()-start,3),
            'scope':'Finite exhaustive/seeded checks of the supplied executable compiler; not kernel verification.'}
    print(json.dumps(report,indent=2))
    dest=Path(__file__).resolve().parents[1]/'verification'/'test_results.json'
    dest.write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
