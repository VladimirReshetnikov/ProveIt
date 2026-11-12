"""Untrusted zero-base clausal -> inherited zero-normal seven-rule compiler.

The destination checker uses separate case DI and equation QI, explicit
successor computation, crossed transport, and de Bruijn indices. Thus it
does not share the new source guard, arithmetic rule, or variable codec.
"""
import copy
import zero_base as source
from validate import load, native_formula, native_term, ROOT

target=load('zero_seven_target', ROOT/'reference/native_zero_seven.py')
Z=['z']
V=['v',0]


def map_proof(p,at,hyp=lambda i,local:['hyp',i],local=0):
    """Inherited structural proof map from reflexive_base/proof_translations.py."""
    tag=p[0]
    if tag=='hyp':return hyp(p[1],local)
    if tag=='succ':return [tag,at(p[1],local),at(p[2],local),at(p[3],local+1)]
    if tag=='tr':return [tag,at(p[1],local+1),map_proof(p[2],at,hyp,local),map_proof(p[3],at,hyp,local)]
    if tag in ('qe','de'):
        return [tag,at(p[1],local),map_proof(p[2],at,hyp,local),map_proof(p[3],at,hyp,local+(tag=='de'))]
    if tag=='di':return [tag,at(p[1],local+2),at(p[2],local),map_proof(p[3],at,hyp,local+1)]
    if tag=='qi':return [tag,at(p[1],local+1),map_proof(p[2],at,hyp,local+1)]
    raise ValueError('unknown target proof node')


def lift(p):
    def at(a,protected):
        return target.walk(a,lambda i,d:['v',i+1 if i>=d+protected else i])
    return map_proof(p,at)


def weaken(p):
    return map_proof(p,lambda a,_:copy.deepcopy(a),lambda i,local:['hyp',i+1 if i>=local else i])


def refl(t):
    computation=['succ',Z,Z,target.shift(t)]
    return ['tr',V,computation,computation]


def translate_tree(p,context=(),kinds=(),scope=0):
    tag=p[0]
    if tag=='r':return refl(native_term(p[1],scope))
    if tag=='v':
        b,r=source.derive(p[2],list(context),scope)
        c,a,h=b
        major=translate_tree(p[1],context,kinds,scope)
        minor=translate_tree(p[2],context,kinds,scope)
        computation=['succ',native_term(c[1],scope),native_term(a,scope),native_term(h,scope,1)]
        return ['tr',native_term(h,scope,1),major,['tr',V,minor,computation]]
    if tag=='u':
        i,t,premise=p[1:]
        hyp=['hyp',len(context)-1-i]
        if kinds[i]=='ordinary':return hyp
        return ['qe',native_term(t,scope),hyp,translate_tree(premise,context,kinds,scope)]
    goal,data,branch=p[1:]
    fresh=-scope-1
    if tag=='e':
        paired=source.derive(data,list(context),scope)
        body=source.opening(paired[0],fresh,1)
        clause=(source.opening(body,0),body)
        return ['de',native_formula(goal,scope),translate_tree(data,context,kinds,scope),
                translate_tree(branch,context+(clause,),kinds+('closure',),scope+1)]
    body=source.opening(goal[0],data,1)
    base=source.opening(body,0)
    clause=([0,0],source.opening(body,fresh) if base==[0,0] else base)
    premise=translate_tree(branch,context+(clause,),kinds+('ordinary',),scope+1)
    if base==[0,0]:
        closure=['qi',native_formula(body,scope,1),premise]
        premise=['qe',['s',V],weaken(lift(closure)),['hyp',0]]
    return ['di',native_formula(goal[0],scope,2),native_term(data,scope),premise]


def translate(c):
    source.verify(c)
    out={'variables':0,'context':[],'goal':native_formula(c['goal'],0),'proof':translate_tree(c['proof'])}
    target.check(out)
    return out
