"""Untrusted compiler for the packaged canonical four-field terminal fixtures.

Input convention: top-level packets [m,s,u,t], goal last. Output convention:
three-field packets [s,u,t], goal last, global return-reservation floors.
This executable supports the pinned canonical proof trees, not arbitrary
accepted aliased bytecode. It never participates in the trusted checker.
"""
from dataclasses import dataclass
from recode import recode_tree
import json
import sys

sys.setrecursionlimit(20000)
MISSING = object()

@dataclass
class Node:
    goal: object
    floor: int
    packet: object
    terminal: str
    match: bool = False
    progress: bool = False
    major: object = None
    continuation: object = None


def scan_old(document):
    stack = document[:-1].copy()
    def check(g, a, k=0, v=0):
        m, s, u, t = packet = stack.pop()
        r = [s,u,t,m]
        def op(a, t=MISSING, d=0):
            if type(a) is list and len(a)**v in (1,2+d%2):
                return [op(b,t,d+5-len(a)) for b in a]
            if k <= a < d and v <= (d & (a%2)):
                return a or 1
            return (d%2|v) and op(t,d=3)
        checked = op(a)
        v = 0
        frame = [[s and [s] or 1,u,t],op(t,r[:3],3) if s else u]
        if checked in (0,*g):
            return Node(a,k,packet,'hypothesis')
        if checked == frame:
            return Node(a,k,packet,'computation')
        node = Node(a,k,packet,'')
        node.major = check(g,m,k)
        h = m*3 or (a := op(*a,t,2))
        node.progress = bool(m or len(a)==2==u)
        k -= 1
        hyp = op(h,k if node.progress else 0)
        node.match = (m,a) == ([s,u] if s else [t]*3,op(t,u))
        goal = op(op(t,s) if node.match else a,[k])
        node.continuation = check(g+[hyp],goal,k)
        return node
    tree = check([],document[-1],v=1)
    return tree


def compile_tree(tree, reservation="return"):
    records=[]
    floor=0
    first=True
    stats={'nodes':0,'early_terminals':0,'old_computations':0,'old_hypotheses':0}
    def rename(a,env):
        if type(a) is list:
            return [rename(b,env) for b in a]
        if a<0:
            return env[a]
        return a
    def build(node,g,goal,env):
        nonlocal floor,first
        stats['nodes']+=1
        assert goal == rename(node.goal,env), (goal,rename(node.goal,env))
        m,s,u,t=node.packet
        if node.terminal=='hypothesis':
            record=[0,1,1]
            stats['old_hypotheses']+=1
        elif node.terminal=='computation':
            record=rename([s,u,t],env)
            stats['old_computations']+=1
        elif node.match:
            record=rename([s,u,t],env)
        elif m:
            record=[rename(m,env),0,1]
        else:
            record=[0,2 if node.progress else [],rename(t,env)]
        records.append(record)
        s,u,t=record
        def op(a,t=MISSING,d=0,validate=False):
            if type(a) is list and (not validate or len(a) in (1,2+d%2)):
                return [op(b,t,d+(2*(j==2) if d%2 else 5-len(a)),validate) for j,b in enumerate(a)]
            if floor <= a < d and (not validate or (d & (a%2))):
                return a or 1
            return (d%2 or validate) and op(t,d=3,validate=validate)
        checked=op(goal,validate=first)
        first=False
        if reservation == "entry":
            floor-=1
        frame=[[s and [s] or 1,u,t],op(t,record,3) if s else u]
        if checked in (0,*g,frame):
            if not node.terminal:
                stats['early_terminals']+=1
            if reservation == 'return':
                floor-=1
            return
        if node.terminal:
            raise ValueError(('lost terminal',node.terminal,goal,frame))
        a=goal
        endpoint=op(t,u)==a
        if endpoint:
            a=op(t,s)
            s=record[:2] if s else [t]*3
        assert endpoint==node.match, ('endpoint changed',endpoint,node.match)
        h=s*3 or (a:=op(*a,t,2))
        if s:
            build(node.major,g,s,env)
        else:
            # The control's administrative-major branch is a hypothesis leaf;
            # a fresh neutral packet safely reserves the next global name.
            records.append([0,1,1])
            stats['nodes']+=1
            stats['old_hypotheses']+=1
            floor-=1
        eigen=floor
        image=eigen if s or len(a)==2==u else 0
        hypothesis=op(h,image)
        next_goal=op(a,[eigen])
        newenv={**env,node.floor-1:eigen}
        build(node.continuation,[*g,hypothesis],next_goal,newenv)
        if reservation == 'return':
            floor-=1
    build(tree,[],tree.goal,{})
    return list(reversed(records))+[tree.goal],stats


def translate(document, reservation="return"):
    return compile_tree(recode_tree(scan_old(document)), reservation)

