#!/usr/bin/env python3
"""Arithmetic DAG primitives adapted from ProveIt package176 build_pool.py.

Only the shared DAG builder and metric calculation are retained here.
"""
class DAG:
    def __init__(self):
        self.nodes=[]; self.index={}
    def node(self,*entry):
        if entry not in self.index:
            self.index[entry]=len(self.nodes); self.nodes.append(list(entry))
        return self.index[entry]
    def c(self,n): return self.node('const',n)
    def v(self,i): return self.node('var',i)
    def add(self,a,b):
        if a==self.c(0): return b
        if b==self.c(0): return a
        return self.node('add',*sorted([a,b]))
    def sub(self,a,b):
        if b==self.c(0): return a
        if a==b:return self.c(0)
        return self.node('sub',a,b)
    def mul(self,a,b):
        if self.c(0) in (a,b):return self.c(0)
        if a==self.c(1):return b
        if b==self.c(1):return a
        return self.node('mul',*sorted([a,b]))
    def sum(self,values):
        z=self.c(0)
        for value in values:z=self.add(z,value)
        return z
    def product(self,values):
        z=self.c(1)
        for value in values:z=self.mul(z,value)
        return z
    def square(self,a):return self.mul(a,a)
    def polynomial(self,terms,mapping):
        return self.sum(self.mul(self.c(c),self.product(self.v(mapping[i]) for i in ids))
                        for c,ids in terms)

def analyze(data):
    nodes=data['nodes'];degree=[];norm=[];active=set()
    def walk(n):
        if n in active:return
        active.add(n)
        if nodes[n][0] in ('add','sub','mul'):
            walk(nodes[n][1]);walk(nodes[n][2])
    walk(data['root'])
    for n in nodes:
        if n[0]=='const':degree.append(0);norm.append(abs(n[1]))
        elif n[0]=='var':degree.append(1);norm.append(1)
        elif n[0]=='mul':degree.append(degree[n[1]]+degree[n[2]]);norm.append(norm[n[1]]*norm[n[2]])
        else:degree.append(max(degree[n[1]],degree[n[2]]));norm.append(norm[n[1]]+norm[n[2]])
    return dict(variables=len(data['variables']),residuals=len(data['residual_nodes']),
                degree_upper_bound=degree[data['root']],
                binary_operations=sum(nodes[n][0] in ('add','sub','mul') for n in active),
                coefficient_l1_bound_bit_length=norm[data['root']].bit_length(),
                largest_literal_constant=max(abs(nodes[n][1]) for n in active if nodes[n][0]=='const'),
                live_nodes=len(active),stored_nodes=len(nodes))

