#!/usr/bin/env python3
"""Create explicit polynomial circuits from acyclic monic eliminations."""
from pathlib import Path
import json, hashlib, math, shutil
from collections import Counter

HERE=Path(__file__).resolve().parent
ROOT=HERE
SOURCE=ROOT/'source/equation248.json'

def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')

def build(source,profile):
    rows=source['residuals']; n=len(source['variables'])
    defs={};removed=set()
    for step in profile['steps']:
        r,v=step['row'],step['variable']
        if r in removed or v in defs:raise ValueError('Duplicate pivot')
        row=rows[r]['terms']
        cs=[c for c,m in row if m==[v]]
        if len(cs)!=1 or abs(cs[0])!=1 or any(v in m for c,m in row if m!=[v]):raise ValueError('Not monic')
        defs[v]=(r,[[-cs[0]*c,m] for c,m in row if m!=[v]])
        removed.add(r)
    inputs=[v for v in range(n) if v not in defs]
    nodes=[['var',i] for i in range(len(inputs))]
    roots=dict(zip(inputs,range(len(inputs))))
    blocks=[];visiting=set();degrees={v:1 for v in inputs};norms={v:1 for v in inputs}
    prime=1000000007;leading={v:v+3 for v in inputs}
    def node(op,*args):
        nodes.append([op,*args]);return len(nodes)-1
    def expression(terms):
        start=len(nodes)
        def term(c,m):
            if not m:return node('const',abs(c))
            value=roots[m[0]]
            for v in m[1:]:value=node('*',value,roots[v])
            if abs(c)!=1:value=node('*',node('const',abs(c)),value)
            return value
        def addall(ns):
            if not ns:return None
            value=ns[0]
            for z in ns[1:]:value=node('+',value,z)
            return value
        pos=addall([term(c,m) for c,m in terms if c>0])
        neg=addall([term(c,m) for c,m in terms if c<0])
        if pos is None:out=node('-',node('const',0),neg) if neg is not None else node('const',0)
        elif neg is None:out=pos
        else:out=node('-',pos,neg)
        if out<start:out=node('+',out,node('const',0))
        return start,out
    def define(v):
        if v in roots:return
        if v in visiting:raise ValueError('Cyclic assignments')
        visiting.add(v);r,terms=defs[v]
        for _,m in terms:
            for j in m:define(j)
        start,out=expression(terms)
        degrees[v]=max((sum(degrees[j] for j in m) for _,m in terms),default=0)
        norms[v]=sum(abs(c)*math.prod(norms[j] for j in m) for c,m in terms)
        leading[v]=sum(c*math.prod(leading[j] for j in m) for c,m in terms if sum(degrees[j] for j in m)==degrees[v])%prime
        roots[v]=out
        blocks.append({'kind':'definition','source_row':r,'variable':v,'start':start,'root':out})
        visiting.remove(v)
    for v in sorted(defs):define(v)
    residual_roots=[];rd=[];rn=[];rl=[];kept=[]
    for r,row in enumerate(rows):
        if r in removed:continue
        terms=row['terms'];start,out=expression(terms)
        blocks.append({'kind':'residual','source_row':r,'start':start,'root':out})
        kept.append(r);residual_roots.append(out)
        d=max((sum(degrees[j] for j in m) for _,m in terms),default=0);rd.append(d)
        rn.append(sum(abs(c)*math.prod(norms[j] for j in m) for c,m in terms))
        rl.append(sum(c*math.prod(leading[j] for j in m) for c,m in terms if sum(degrees[j] for j in m)==d)%prime)
    start=len(nodes);squares=[node('*',r,r) for r in residual_roots];out=squares[0]
    for q in squares[1:]:out=node('+',out,q)
    blocks.append({'kind':'sum_of_squares','start':start,'root':out})
    md=max(rd);w=next(i for i,d in enumerate(rd) if d==md and rl[i]!=0)
    live=set()
    def walk(i):
        if i in live:return
        live.add(i)
        if nodes[i][0] in ('+','-','*'):
            walk(nodes[i][1]);walk(nodes[i][2])
    walk(out)
    live_vars={nodes[i][1] for i in live if nodes[i][0]=='var'}
    if live_vars!=set(range(len(inputs))):raise ValueError('Unused quantified variable')
    metrics={'variables':len(inputs),'residuals':len(kept),'eliminated_variables':len(defs),
        'degree':2*md,'coefficient_height_strict_power_of_two':sum(x*x for x in rn).bit_length(),
        'live_binary_operations':sum(nodes[i][0] in ('+','-','*') for i in live),
        'stored_nodes':len(nodes),'maximum_literal_constant':max(abs(z[1]) for z in nodes if z[0]=='const')}
    program={'schema':'acyclic-monic-polynomial-v1','domain':'unrestricted integers',
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'variables':[{'source_index':v,**source['variables'][v]} for v in inputs],
        'retained_source_indices':inputs,'nodes':nodes,'output':out,'blocks':blocks,
        'residual_roots':residual_roots,'metrics':metrics,
        'degree_certificate':{'source_variable_degrees':[degrees[i] for i in range(n)],
            'retained_source_rows':kept,'residual_degrees':rd,'modulus':prime,
            'input_direction':'source_index + 3','witness_source_row':kept[w],
            'witness_top_residue':rl[w]}}
    return program

def main():
    import argparse
    pa=argparse.ArgumentParser(description=__doc__)
    pa.add_argument('--output',type=Path)
    pa.add_argument('--check',action='store_true')
    a=pa.parse_args()
    if a.output is None and not a.check:pa.error('Specify --output DIR or --check')
    source=json.loads(SOURCE.read_text())
    reports=[]
    for file in sorted((ROOT/'certificates').glob('*.json')):
        cert=json.loads(file.read_text())
        program=build(source,cert)
        name=f"integer{program['metrics']['variables']}_degree{program['metrics']['degree']}"
        if name!=file.stem:raise ValueError('Wrong profile name')
        serialized=json.dumps(program,sort_keys=True,separators=(',',':'))+'\n'
        if a.check and serialized!=(ROOT/'equations'/file.name).read_text():
            raise ValueError('Reconstruction mismatch: '+name)
        if a.output:
            a.output.mkdir(parents=True,exist_ok=True)
            (a.output/file.name).write_text(serialized)
        reports.append(name)
    print(json.dumps({'status':'PASS','byte_exact_profiles':reports}))

if __name__=='__main__':main()
