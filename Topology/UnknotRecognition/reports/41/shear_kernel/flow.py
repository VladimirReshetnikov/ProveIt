"""Bit-capacity-scaling min-cost circulation and integer tension duality.

No iteration count depends on the numeric value of a capacity. Potentials are
recalibrated by Bellman--Ford after each imbalance repair to keep their bit
length bounded. All calculations are integers.
"""
from __future__ import annotations
from dataclasses import dataclass
from heapq import heappush,heappop
from collections import defaultdict,deque

class WorkLimit(RuntimeError):
    """Inconclusive resource stop, never a mathematical verdict."""

@dataclass
class Budget:
    remaining: int=100_000_000
    used: int=0
    def tick(self,k: int=1) -> None:
        self.remaining-=k; self.used+=k
        if self.remaining<0: raise WorkLimit('integer-flow work budget exhausted')

@dataclass(frozen=True)
class Arc:
    u: int
    v: int
    capacity: int
    cost: int

@dataclass
class Circulation:
    flows: list[int]
    potentials: list[int]
    phases: int
    repairs: int
    work: int

def min_cost_circulation(n: int, arcs: list[Arc], budget: Budget|None=None) -> Circulation:
    b=budget or Budget(); initial=b.used
    if type(n) is not int or n<0: raise ValueError('invalid vertex count')
    for a in arcs:
        if any(type(x) is not int for x in (a.u,a.v,a.capacity,a.cost)):
            raise ValueError('integer arc data required')
        if not (0<=a.u<n and 0<=a.v<n) or a.capacity<0: raise ValueError('invalid arc')
    count=len(arcs); cap=[0]*count; flow=[0]*count; pi=[0]*n
    phases=max((a.capacity.bit_length() for a in arcs),default=0); repairs=0
    def residual():
        adj=[[] for _ in range(n)]
        for i,a in enumerate(arcs):
            b.tick()
            if cap[i]>flow[i]: adj[a.u].append((a.v,a.cost,cap[i]-flow[i],i,1))
            if flow[i]>0: adj[a.v].append((a.u,-a.cost,flow[i],i,-1))
        return adj
    def recalibrate(adj):
        # Distances from an added source having a zero-cost arc to every vertex.
        d=[0]*n
        for step in range(n):
            changed=False
            for u,row in enumerate(adj):
                for v,c,_,_,_ in row:
                    b.tick()
                    if d[v]>d[u]+c:
                        d[v]=d[u]+c; changed=True
            if not changed: return d
        raise AssertionError('negative residual cycle after shortest-path repair')
    for bit in reversed(range(phases)):
        excess=[0]*n
        for i,a in enumerate(arcs):
            b.tick(); cap[i]=2*cap[i]+((a.capacity>>bit)&1); flow[i]*=2
        # A negative reduced-cost arc opened by the new bit has capacity <= 1.
        for i,a in enumerate(arcs):
            b.tick()
            if a.cost+pi[a.u]-pi[a.v]<0 and cap[i]>flow[i]:
                delta=cap[i]-flow[i]
                if delta>1: raise AssertionError('capacity scaling invariant')
                flow[i]+=delta; excess[a.u]-=delta; excess[a.v]+=delta
        while any(x>0 for x in excess):
            adj=residual(); dist=[None]*n; parent=[None]*n; heap=[]
            for v,e in enumerate(excess):
                if e>0: dist[v]=0; heappush(heap,(0,v))
            while heap:
                d,u=heappop(heap)
                if dist[u]!=d: continue
                for v,c,room,i,sign in adj[u]:
                    b.tick(); rc=c+pi[u]-pi[v]
                    if rc<0: raise AssertionError('negative reduced cost before Dijkstra')
                    nd=d+rc
                    if dist[v] is None or nd<dist[v]:
                        dist[v]=nd; parent[v]=(u,i,sign,room); heappush(heap,(nd,v))
            choices=[(dist[v],v) for v in range(n) if excess[v]<0 and dist[v] is not None]
            if not choices: raise AssertionError('feasible circulation cannot be repaired')
            distance,t=min(choices)
            # Truncation updates even vertices unreachable from the surplus set.
            pi=[p+(distance if d is None else min(d,distance)) for p,d in zip(pi,dist)]
            v=t; path=[]
            while parent[v] is not None:
                u,i,sign,room=parent[v]; path.append((i,sign,room)); v=u
            s=v
            if excess[s]<=0: raise AssertionError('augmenting path has no surplus source')
            delta=min(excess[s],-excess[t],*(room for _,_,room in path))
            for i,sign,_ in path: flow[i]+=sign*delta
            excess[s]-=delta; excess[t]+=delta; repairs+=1
            pi=recalibrate(residual())
        if any(excess): raise AssertionError('nonzero residual imbalance')
    return Circulation(flow,pi,phases,repairs,b.used-initial)

@dataclass
class TensionSolution:
    potentials: dict[int,int]
    dual: dict[tuple[int,int,int],int]
    value: int
    balanced: bool
    phases: int=0
    repairs: int=0
    work: int=0
    method: str="flow"

def balanced_potentials(gaps: dict[tuple[int,int,int],int]) -> dict[int,int]|None:
    adj=defaultdict(list)
    for (u,v,e),w in gaps.items():
        if type(w) is not int or w<=0: raise ValueError('positive integer weight required')
        adj[u].append((v,e)); adj[v].append((u,-e))
    z={}
    for root in sorted(adj):
        if root in z: continue
        z[root]=0; todo=[root]
        while todo:
            u=todo.pop()
            for v,e in adj[u]:
                target=z[u]+e
                if v in z:
                    if z[v]!=target: return None
                else: z[v]=target; todo.append(v)
    return z

def solve_tension(gaps: dict[tuple[int,int,int],int], *,
                  balanced_fast_path: bool=True, forest_fast_path: bool=True,
                  budget: Budget|None=None) -> TensionSolution:
    for key,w in gaps.items():
        if (not isinstance(key,tuple) or len(key)!=3 or
            any(type(x) is not int for x in key) or type(w) is not int or w<=0):
            raise ValueError('invalid gap record')
    if balanced_fast_path:
        z=balanced_potentials(gaps)
        if z is not None:
            return TensionSolution(z,{e:0 for e in gaps},0,True,method="balanced")
    if forest_fast_path:
        from .forest import forest_solution
        solved=forest_solution(gaps)
        if solved is not None:
            z,f,value=solved
            verify_tension(gaps,z,f,value)
            return TensionSolution(z,f,value,False,method="forest")
    vertices=sorted({x for u,v,_ in gaps for x in (u,v)}); index={v:i for i,v in enumerate(vertices)}
    keys=sorted(gaps); arcs=[]
    for u,v,e in keys:
        w=gaps[(u,v,e)]
        arcs.extend((Arc(index[u],index[v],w,-e),Arc(index[v],index[u],w,e)))
    result=min_cost_circulation(len(vertices),arcs,budget)
    z={v:-result.potentials[index[v]] for v in vertices}
    f={key:result.flows[2*i]-result.flows[2*i+1] for i,key in enumerate(keys)}
    val=sum(gaps[k]*abs(k[2]+z[k[0]]-z[k[1]]) for k in keys)
    verify_tension(gaps,z,f,val)
    return TensionSolution(z,f,val,False,result.phases,result.repairs,result.work)

def verify_tension(gaps: dict, z: dict, f: dict, value: int) -> bool:
    """Small exact primal/dual verifier; no optimization is performed."""
    vertices={x for u,v,_ in gaps for x in (u,v)}
    if set(z)!=vertices or set(f)!=set(gaps) or type(value) is not int or value<0:
        raise ValueError('certificate support/value mismatch')
    if any(type(v) is not int for v in z.values()) or any(type(v) is not int for v in f.values()):
        raise ValueError('non-integer certificate entry')
    divergence=CounterLike(vertices); primal=0; dual=0
    for (u,v,e),w in gaps.items():
        a=f[(u,v,e)]
        if abs(a)>w: raise ValueError('dual capacity violation')
        divergence[u]+=a; divergence[v]-=a
        primal+=w*abs(e+z[u]-z[v]); dual+=e*a
    if any(divergence.values()): raise ValueError('dual flow not conserved')
    if primal!=dual or primal!=value: raise ValueError('primal-dual gap or wrong value')
    return True

def CounterLike(vertices):
    return {v:0 for v in vertices}
