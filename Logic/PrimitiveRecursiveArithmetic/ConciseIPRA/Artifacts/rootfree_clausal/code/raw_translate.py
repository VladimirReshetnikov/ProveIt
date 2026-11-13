"""Eliminate only root Eval from the raw clausal calculus.

Input and output have exactly the same numerical terms and formulas.
This untrusted compiler is verified on finite examples by two complete checkers.
"""
import copy
import raw_control as source
import raw_two_case as target


def compile_tree(p, context=(), scope=0):
    tag=p[0]
    if tag=='r':
        return copy.deepcopy(p)
    if tag=='u':
        return ['u',p[1],copy.deepcopy(p[2]),compile_tree(p[3],context,scope)]
    if tag=='v':
        s,t=source.derive(p[1],list(context),scope)
        b,r=source.derive(p[2],list(context),scope)
        first=compile_tree(p[1],context,scope)
        second=compile_tree(p[2],context,scope)
        if b==s:
            frame=[0,s,0]
            return ['v',first,['v',second,['r',frame]]]
        return ['v',first,second]
    goal,data,branch=p[1:]
    fresh=-scope-1
    if tag=='e':
        paired=source.derive(data,list(context),scope)
        body=source.opening(paired[0],fresh,1)
        clause=(source.opening(body,0),body)
        data=compile_tree(data,context,scope)
    else:
        body=source.opening(goal[0],data,1)
        eta=fresh if len(goal[0])==2 and data==0 else 0
        clause=([0,0],source.opening(body,eta))
    return [tag,copy.deepcopy(goal),data,compile_tree(branch,context+(clause,),scope+1)]


def compile_certificate(c):
    source.verify(c)
    result={'goal':copy.deepcopy(c['goal']),'proof':compile_tree(c['proof'])}
    target.verify(result)
    return result


def count_nodes(p):
    tag=p[0]
    if tag=='r':return 1
    if tag in ('u','i'):return 1+count_nodes(p[3])
    if tag=='e':return 1+count_nodes(p[2])+count_nodes(p[3])
    return 1+count_nodes(p[1])+count_nodes(p[2])


def count_roots(p,context=(),scope=0):
    tag=p[0]
    if tag=='r':return 0
    if tag=='u':return count_roots(p[3],context,scope)
    if tag=='v':
        s,t=source.derive(p[1],list(context),scope)
        b,r=source.derive(p[2],list(context),scope)
        return int(b==s)+count_roots(p[1],context,scope)+count_roots(p[2],context,scope)
    goal,data,branch=p[1:]
    fresh=-scope-1
    if tag=='e':
        paired=source.derive(data,list(context),scope)
        body=source.opening(paired[0],fresh,1)
        clause=(source.opening(body,0),body)
        extra=count_roots(data,context,scope)
    else:
        body=source.opening(goal[0],data,1)
        eta=fresh if len(goal[0])==2 and data==0 else 0
        clause=([0,0],source.opening(body,eta))
        extra=0
    return extra+count_roots(branch,context+(clause,),scope+1)
