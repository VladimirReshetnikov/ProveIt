#!/usr/bin/env python3
"""Finite controls for the two infinite label-dependent countermodels.

The mathematical model and full-schema proof are in logic_section.tex.
These checks exhaust a stated finite range of parameters and all property
restrictions on the finite candidate set. They are not the proof that every
formula instance is valid in the infinite model.
"""
import json
from itertools import product


def perm(label,n):
    return 1-n if label==1 and n in (0,1) else n


def bits(n):
    return {i for i in range(n.bit_length()) if (n>>i)&1}


def code(xs):
    return sum(1<<x for x in xs)


def mem_left(a,b,env):
    return env[b] in bits(perm(a,env[a]))


def mem_right(a,b,env):
    return perm(b,env[b]) in bits(env[a])


def diagonal(which,label):
    # Outside the finite permutation support, membership is Bit(n,n), false.
    return {n for n in (0,1) if
        (n in bits(perm(label,n)) if which=='omit_head3' else
         perm(label,n) in bits(n))}


def control(which,mem):
    cases=0
    for a,b,c in product(range(5),repeat=3):
        if c in (a,b):continue
        for va,vb in product(range(8),repeat=2):
            if a==b and va!=vb:continue
            env={i:0 for i in range(5)}
            env[a],env[b]=va,vb
            if a==b: candidates=diagonal(which,a)
            elif which=='omit_head3': candidates=bits(perm(a,va))
            else: candidates={perm(b,z) for z in bits(va)}
            support=sorted(candidates|{vb})
            # Every subset represents an arbitrary property's restriction to
            # the only values that can enter the constructed separator.
            for mask in range(1<<len(support)):
                prop={x for i,x in enumerate(support) if mask>>i&1}
                if which=='omit_head3':
                    separator=perm(c,code(prop)) # inverse = itself
                else:
                    separator=code({perm(b,x) for x in prop})
                out=dict(env);out[c]=separator
                check_values=set(support)|set(range(8))|{max(support+[0])+1}
                for x in check_values:
                    e=dict(out);e[b]=x
                    assert not (mem(a,b,e) and x in prop) or mem(c,b,e)
                    assert not mem(c,b,e) or x in prop
                assert vb not in prop or mem(c,b,out)
                cases+=1
    return cases

# Refute omitted first-coordinate rewrite, while code1 stays false.
e={0:0,1:0,2:0,3:0}
assert e[1]==e[2] and mem_left(1,3,e) and not mem_left(2,3,e)
# Refute omitted second-coordinate rewrite.
f={0:0,1:0,2:0,3:2}
assert f[1]==f[2] and mem_right(3,1,f) and not mem_right(3,2,f)
# Retained-coordinate rewrite and designated bottom over an explicit range.
rewrite_checks=0
for a,b,c in product(range(5),repeat=3):
    for va,vc in product(range(8),repeat=2):
        env={i:0 for i in range(5)}
        env[c]=vc;env[a]=va;env[b]=va
        if env[a]!=env[b]:continue
        assert not mem_left(c,a,env) or mem_left(c,b,env)
        assert not mem_right(a,c,env) or mem_right(b,c,env)
        rewrite_checks+=1
for v in range(64):
    env={0:v}
    assert not mem_left(0,0,env) and not mem_right(0,0,env)

if __name__=='__main__':
    print(json.dumps({
        'kind':'finite controls, not a full-schema proof',
        'labels':list(range(5)), 'parameter_values':list(range(8)),
        'retained_rewrite_controls':rewrite_checks,
        'omit_head3_separator_controls':control('omit_head3',mem_left),
        'omit_head4_separator_controls':control('omit_head4',mem_right),
        'explicit_head3_counterexample':{'x1':0,'x2':0,'x3':0},
        'explicit_head4_counterexample':{'x1':0,'x2':0,'x3':2}
    },indent=2))
