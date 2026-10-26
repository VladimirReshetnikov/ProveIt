#!/usr/bin/env python3
"""Emit a fully literal ordinary polynomial in 207 unrestricted integers.

No symbolic exponent, mathematical oracle, or unspecified constant occurs.
The JSON DAG uses only integer constants, variables, +, -, and *.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
REMOVED_VARIABLES = [141,142,143,144,145,146,212,213,214,215]
REMOVED_ROWS = [97,98,99,100,101,102,149,150,151,152]

def affine(*terms):
    return [[c, [] if i is None else [i]] for c,i in terms if c]

def ports():
    J=affine((-4,None),(-3,8),(-7,9),(4,19),(2,22),(2,26),(2,28),
             (2,30),(2,32),(4,34),(2,35),(2,38),(2,41),(4,60),(2,61))
    req=[]
    def add(number,group,m,k,d,y,z):
        req.append(dict(number=number,group=group,m=m,k=k,D=d,Y=y,Z=z))
    v=lambda i:affine((1,i))
    a=lambda i,c:affine((c,None),(1,i))
    add(0,0,v(3),v(0),v(138),v(139),v(140))
    add(1,1,v(17),v(1),v(174),v(175),a(176,1))
    add(2,2,a(94,-1),v(1),v(174),v(175),a(176,1))
    add(3,4,v(95),affine((1,0),(1,3)),v(147),v(148),v(149))
    add(4,3,v(96),v(0),v(138),v(139),v(140))
    add(5,4,v(100),a(8,-1),v(150),a(151,-1),v(152))
    for number,m,k,d in [(7,103,9,153),(8,106,10,156),(9,109,11,159),
                           (10,112,12,162),(11,113,2,165),(12,116,13,168),
                           (13,119,14,171),(15,124,15,177)]:
        add(number,3 if number==11 else 4,v(m),v(k),v(d),v(d+1),v(d+2))
    add(14,3,v(120),v(1),v(174),v(175),a(176,1))
    add(16,4,v(127),affine((2,16)),v(180),v(181),v(182))
    add(17,4,v(130),J,v(183),v(184),v(185))
    req.sort(key=lambda r:r['number'])
    return dict(A=a(134,1),bases=[v(0),v(4),v(186),a(94,-1),v(94)],
                requests=req,old_variable_count=216)

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

def build(partition=None,unweighted_groups=None):
    source_path=ROOT/'source/equation216.json'
    raw=source_path.read_bytes();source=json.loads(raw)
    keep=[i for i in range(216) if i not in REMOVED_VARIABLES]
    mapping={old:new for new,old in enumerate(keep)}
    d=DAG(); ps=ports()
    poly=lambda terms:d.polynomial(terms,mapping)
    rows=[]; row_info=[]; literal=[]
    for i,r in enumerate(source['residuals']):
        if i in REMOVED_ROWS:continue
        if any(v in REMOVED_VARIABLES for c,ids in r['terms'] for v in ids):
            raise ValueError('Private-coordinate check failed')
        rows.append(poly(r['terms']));row_info.append(dict(parent_row=i,label=r['label']))
        literal.append(dict(parent_row=i,label=r['label'],
                            terms=[[c,[mapping[v] for v in ids]] for c,ids in r['terms']]))
    A=poly(ps['A']);base=[poly(b) for b in ps['bases']]
    T=[d.sub(d.sub(d.mul(d.c(2),d.mul(A,n)),d.square(n)),d.c(1)) for n in base]
    H=[];S=[];E=[]
    for j,n in enumerate(base):
        hs=[];ss=[]
        for r in ps['requests']:
            if r['group']!=j:continue
            m,Q,Y,Z=[poly(r[key]) for key in ['m','D','Y','Z']]
            delta=d.sub(m,Q)
            hs.append(d.mul(Y,d.sub(delta,Z)))
            ss.append(d.sub(d.square(delta),d.square(Y)))
        H.append(d.sum(hs));S.append(d.sum(ss))
        E.append(d.sub(S[-1],d.mul(d.c(2),d.mul(n,H[-1]))))
    groups=[list(range(5))] if partition is None else partition
    unweighted_groups=[] if unweighted_groups is None else unweighted_groups
    if sorted(j for group in groups for j in group)!=list(range(5)):
        raise ValueError('Must be a partition of the five bases')
    pool_rows=[]
    for a,group in enumerate(groups):
        z=d.v(len(keep)+a)
        if len(group)==1:
            j=group[0]
            R=d.sub(E[j],d.mul(z,T[j]))
        else:
            numerator=d.sum(d.product(([E[j]] if group in unweighted_groups else [base[j],E[j]])+[T[k] for k in group if k!=j]) for j in group)
            R=d.sub(numerator,d.mul(z,d.product(T[j] for j in group)))
        rows.append(R);pool_rows.append(R)
        row_info.append(dict(parent_row=None,label='all_five_oriented_reciprocal' if partition is None else 'partition_pool_'+str(a)))
    root=d.sum(d.square(r) for r in rows)
    data=dict(schema='conzfc.integer-polynomial-dag.v1',domain='unrestricted integers',
              variables=[dict(v,source_index=i) for i,v in enumerate(source['variables']) if i in mapping]
                         +[dict(kind='oriented_pool',name='all_five.z' if partition is None else 'partition.z'+str(i),source_index=None) for i in range(len(groups))],
              nodes=d.nodes,residual_nodes=rows,residual_info=row_info,root=root,
              source_sha256=hashlib.sha256(raw).hexdigest(),
              source_commit='315154b670d7bdb1679554734e417410c9b8187b',
              ports_node_ids=dict(A=A,bases=base,T=T,H=H,S=S,E=E,reciprocal=R),
              exact_degree_certificate=dict(residual_degree=12,degree=24,
                 source_monomial=[[0,2],[4,2],[94,4],[130,1],[184,1],[186,2]],
                 monomial=[[mapping[v],e] for v,e in [(0,2),(4,2),(94,4),(130,1),(184,1),(186,2)]],
                 coefficient=-2))
    if partition is not None:
        data.pop('exact_degree_certificate')
        data['partition']=partition
        if unweighted_groups:data['unweighted_groups']=unweighted_groups
        data['ports_node_ids']['reciprocal']=pool_rows
    certificate=dict(schema='conzfc.oriented-pooling-certificate.v1',
                     removed_variables=REMOVED_VARIABLES,removed_rows=REMOVED_ROWS,
                     retained_source_indices=keep,old_to_new=[[a,b] for a,b in mapping.items()],
                     ports=ps,source_sha256=data['source_sha256'])
    if partition is not None:
        certificate['partition']=partition
        if unweighted_groups:certificate['unweighted_groups']=unweighted_groups
    return data,certificate,literal

def save(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def main():
    data,certificate,literal=build()
    save(ROOT/'equations/P207.json',data)
    save(ROOT/'equations/P207_certificate.json',certificate)
    save(ROOT/'equations/P207_quadratic_rows.json',literal)
    metrics=analyze(data);metrics['degree']=24
    save(ROOT/'equations/P207_metrics.json',metrics)
    print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
