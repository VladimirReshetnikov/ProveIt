#!/usr/bin/env python3
"""Exact equality check between the factored evaluator and frozen D83.

Only the Python standard library is used. No producer is imported. Sparse
expansion checks the two source-coordinate identities, and independent
expression reflection checks every restoration, retained residual, and sum
of squares in BOTH complete DAGs. Optional byte rebuilding is additional.
"""
import argparse,hashlib,json,subprocess,sys
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
ORIGINAL_SHA='b4c0637db413899337d66a10859dcd2e10dcc52feb283e398075b15d9e947c38'
def need(x,message):
    if not x:raise ValueError(message)
def read(path):return json.loads(path.read_text())
def sparse(terms):
    r={}
    for c,m in terms:
        m=tuple(sorted(m));r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items() if c}
def plus(a,b):
    d=a.copy()
    for m,c in b.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def product(a,b):
    d={}
    for m,c in a.items():
        for n,e in b.items():
            t=tuple(sorted(m+n));d[t]=d.get(t,0)+c*e
    return {m:c for m,c in d.items() if c}
def expand(ast):
    if ast[0]=='c':return {():ast[1]} if ast[1] else {}
    if ast[0]=='v':return {(ast[1],):1}
    need(ast[0] in ('+','*'),'Nonpolynomial factor expression')
    a,b=expand(ast[1]),expand(ast[2])
    return plus(a,b) if ast[0]=='+' else product(a,b)

class Reflection:
    def __init__(self):self.forms=[];self.index={}
    def intern(self,x):
        if x not in self.index:self.index[x]=len(self.forms);self.forms.append(x)
        return self.index[x]
    def c(self,n):return self.intern(('c',n))
    def x(self,n):return self.intern(('x',n))
    def op(self,op,a,b):
        count=Counter();constant=0 if op=='add' else 1
        for v in (a,b):
            f=self.forms[v];children=f[1] if f[0]==op else ((v,1),)
            for w,multiplicity in children:
                g=self.forms[w]
                if g[0]=='c':
                    constant=(constant+g[1]*multiplicity if op=='add'
                              else constant*pow(g[1],multiplicity))
                else:count[w]+=multiplicity
        if op=='mul' and constant==0:return self.c(0)
        if constant!=(0 if op=='add' else 1) or not count:count[self.c(constant)]+=1
        if len(count)==1:
            w,n=next(iter(count.items()))
            if n==1:return w
        return self.intern((op,tuple(sorted(count.items()))))

def reflect_diagram(diagram,source,projection,factorizations=None):
    free=projection['free'];retained=projection['retained_rows'];nodes=diagram['nodes']
    need(diagram['variables']==[source['variables'][j]['name'] for j in free], 'Variable order changed')
    need(diagram['domain']=='unrestricted integers','Domain changed')
    ref=Reflection();values=[];degrees=[];norms=[]
    for j,node in enumerate(nodes):
        op=node[0]
        if op=='input':
            need(len(node)==2 and 0<=node[1]<len(free),'Bad input')
            values.append(ref.x(node[1]));degrees.append(1);norms.append(1)
        elif op=='const':
            need(isinstance(node[1],int),'Noninteger literal')
            values.append(ref.c(node[1]));degrees.append(0);norms.append(abs(node[1]))
        else:
            need(op in ('add','mul') and all(0<=n<j for n in node[1:]),'Nontopological gate')
            a,b=node[1:];values.append(ref.op(op,values[a],values[b]))
            degrees.append(max(degrees[a],degrees[b]) if op=='add' else degrees[a]+degrees[b])
            norms.append(norms[a]+norms[b] if op=='add' else norms[a]*norms[b])
    coordinate_roots=diagram['source_coordinate_roots']
    need(len(coordinate_roots)==len(source['variables']),'Missing coordinate restoration')
    coordinates=[values[j] for j in coordinate_roots]
    for j,v in enumerate(free):need(coordinates[v]==ref.x(j),'Free coordinate altered')
    def from_sparse(terms):
        out=ref.c(0)
        for coefficient,monomial in terms:
            term=ref.c(coefficient)
            for v in monomial:term=ref.op('mul',term,coordinates[v])
            out=ref.op('add',out,term)
        return out
    def from_ast(ast):
        if ast[0]=='c':return ref.c(ast[1])
        if ast[0]=='v':return coordinates[ast[1]]
        return ref.op('add' if ast[0]=='+' else 'mul',from_ast(ast[1]),from_ast(ast[2]))
    definitions={};used=set()
    for p in projection['pivots']:
        v=p['variable'];r=p['row'];literal=sparse(source['residuals'][r]['terms'])
        need(v not in definitions and r not in used,'Repeated pivot')
        coefficient=literal.get((v,),0);need(coefficient in (-1,1),'Nonunit pivot')
        need(all(v not in m for m in literal if m!=(v,)),'Nonlinear pivot')
        rest={m:-coefficient*c for m,c in literal.items() if m!=(v,)}
        need(rest==sparse(p['restoration']),'False source restoration')
        definitions[v]=rest;used.add(r)
        wanted=(from_ast(factorizations['restoration'])
                if factorizations and v==139 else from_sparse(p['restoration']))
        need(coordinates[v]==wanted,'Evaluator changes a restoration')
    need(free==[j for j in range(len(source['variables'])) if j not in definitions], 'False free complement')
    need(retained==[j for j in range(len(source['residuals'])) if j not in used], 'False residual complement')
    active=set();done=set()
    def visit(v):
        need(v not in active,'Cyclic coordinate definitions')
        if v not in definitions or v in done:return
        active.add(v)
        for j in {j for m in definitions[v] for j in m}:visit(j)
        active.remove(v);done.add(v)
    for v in definitions:visit(v)
    residuals=diagram['residual_roots'];need(len(residuals)==len(retained),'Wrong residual count')
    total=ref.c(0)
    for row,node in zip(retained,residuals):
        wanted=(from_ast(factorizations['residual']) if factorizations and row==170
                else from_sparse(source['residuals'][row]['terms']))
        need(values[node]==wanted,'Evaluator changes a residual')
        total=ref.op('add',total,ref.op('mul',values[node],values[node]))
    need(values[diagram['output']]==total,'Output changes the sum of squares')
    return degrees,norms

def finite_certificates(diagram,certificate,degrees):
    nodes=diagram['nodes'];dc=certificate['degree'];mod=dc['modulus'];leading=[]
    for j,node in enumerate(nodes):
        if node[0]=='const':leading.append(node[1]%mod)
        elif node[0]=='input':leading.append(dc['ray'][node[1]]%mod)
        else:
            a,b=node[1:]
            leading.append((leading[a]*leading[b] if node[0]=='mul' else
                            (leading[a] if degrees[a]==degrees[j] else 0)
                            +(leading[b] if degrees[b]==degrees[j] else 0))%mod)
    root=diagram['residual_roots'][dc['residual_number']]
    need(degrees[root]==max(degrees[r] for r in diagram['residual_roots'])==312,'Wrong residual degree bound')
    need(leading[root]==dc['leading_coefficient']!=0,'Changed top homogeneous polynomial')
    oc=certificate['occurrence'];mod=oc['modulus'];n=len(oc['point']);values=[];derivatives=[]
    for node in nodes:
        if node[0]=='const':values.append(node[1]%mod);derivatives.append([0]*n)
        elif node[0]=='input':
            values.append(oc['point'][node[1]]%mod);v=[0]*n;v[node[1]]=1;derivatives.append(v)
        else:
            a,b=node[1:]
            if node[0]=='add':
                values.append((values[a]+values[b])%mod)
                derivatives.append([(x+y)%mod for x,y in zip(derivatives[a],derivatives[b])])
            else:
                values.append(values[a]*values[b]%mod)
                derivatives.append([(x*values[b]+values[a]*y)%mod for x,y in zip(derivatives[a],derivatives[b])])
    need(derivatives[diagram['output']]==oc['gradient'] and all(oc['gradient']), 'Changed occurrence certificate')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--canonical-dir',type=Path,default=HERE.parent)
    parser.add_argument('--rebuild',action='store_true');parser.add_argument('--receipt',type=Path);args=parser.parse_args();canonical=args.canonical_dir
    original_bytes=(canonical/'P83/circuit.json').read_bytes()
    need(hashlib.sha256(original_bytes).hexdigest()==ORIGINAL_SHA,'Wrong frozen original circuit')
    original=json.loads(original_bytes);source=read(canonical/'source227.json');projection=read(canonical/'P83/projection.json')
    factors=read(HERE/'factorizations.json');alternate=read(HERE/'circuit.json')
    need(factors['restored_coordinate']==139 and factors['source_residual_row']==170,'Unapproved extra factorization')
    original_restoration=next(p['restoration'] for p in projection['pivots'] if p['variable']==139)
    need(expand(factors['restoration'])==sparse(original_restoration),'False z139 factorization')
    need(expand(factors['residual'])==sparse(source['residuals'][170]['terms']),'False row170 factorization')
    reflect_diagram(original,source,projection)
    degrees,norms=reflect_diagram(alternate,source,projection,factors)
    finite_certificates(alternate,read(canonical/'P83/certificates.json'),degrees)
    nodes=alternate['nodes'];live={alternate['output']}
    for j in range(len(nodes)-1,-1,-1):
        if j in live and nodes[j][0] in ('add','mul'):live.update(nodes[j][1:])
    metrics={'variables':len(alternate['variables']),'residuals':len(alternate['residual_roots']),
             'live_binary_gates':sum(nodes[j][0] in ('add','mul') for j in live),
             'live_nodes':len(live),'total_nodes_with_restorations':len(nodes),
             'largest_absolute_literal':max(abs(nodes[j][1]) for j in live if nodes[j][0]=='const'),
             'operation_breakdown':dict(Counter(nodes[j][0] for j in live if nodes[j][0] in ('add','mul')))}
    need(metrics==read(HERE/'METRICS.json'),'False operation metrics')
    if args.rebuild:
        subprocess.run([sys.executable,'-B',str(HERE/'build_factored.py'),'--canonical-dir',str(canonical),'--check'],
                       check=True,stdout=subprocess.PIPE,text=True)
    bound=norms[alternate['output']]
    receipt={'exact_polynomial_equality':'verified at every integer tuple',
             'sparse_factor_identities':{'z139_terms':len(expand(factors['restoration'])),
                                       'source_row170_terms':len(expand(factors['residual']))},
             'original_circuit_sha256':ORIGINAL_SHA,
             'alternate_circuit_sha256':hashlib.sha256((HERE/'circuit.json').read_bytes()).hexdigest(),
             'exact_degree':624,'coefficient_height_strictly_below_power_of_two':bound.bit_length(),
             'exact_coefficient_norm_majorant':str(bound),'byte_exact_rebuild':args.rebuild,**metrics}
    if args.receipt:args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='exact_coefficient_norm_majorant'},indent=2))

if __name__=='__main__':main()
