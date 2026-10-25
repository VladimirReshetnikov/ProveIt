#!/usr/bin/env python3
"""Independent exact proof-certificate checker for polynomial elimination.

No producer is imported. Every circuit block is expanded as a polynomial in
its *previous* source-coordinate registers. These expansions have degree at
most two; the huge final polynomial need not be expanded.
"""
import argparse,copy,hashlib,json,math,subprocess,sys
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:raise ValueError(message)

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        q=out.get(m,0)+sign*c
        if q:out[m]=q
        else:out.pop(m,None)
    return out

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            t=tuple(sorted(m+n));q=out.get(t,0)+c*d
            if q:out[t]=q
            else:out.pop(t,None)
    return out

def rowpoly(terms):
    out={}
    for c,m in terms:
        require(type(c) is int and c!=0,'invalid source coefficient')
        t=tuple(m);require(list(t)==sorted(t),'unsorted source monomial')
        require(t not in out,'uncollected source row');out[t]=c
    return out

def check(source,source_hash,program):
    require(program['schema']=='acyclic-monic-polynomial-v1','program schema')
    require(program['domain']=='unrestricted integers','domain changed')
    require(program['source_sha256']==source_hash,'source hash mismatch')
    rows=source['residuals'];n=len(source['variables'])
    inputs=program['retained_source_indices']; nodes=program['nodes'];blocks=program['blocks']
    require(inputs==sorted(set(inputs)) and all(0<=v<n for v in inputs),'bad inputs')
    require(program['variables']==[{'source_index':v,**source['variables'][v]} for v in inputs],'variable map')
    require(nodes[:len(inputs)]==[['var',i] for i in range(len(inputs))],'input leaves')
    registers={j:v for j,v in enumerate(inputs)}
    degrees={v:1 for v in inputs};norms={v:1 for v in inputs};tops={v:v+3 for v in inputs}
    used_rows=set();assigned=set(inputs);residual_nodes=[];residual_rows=[];residual_degrees=[];residual_norms=[];residual_tops=[]
    cursor=len(inputs);phase='definition';modulus=1000000007
    def local_expand(start,end,leaves):
        local={}
        def get(i):
            require(type(i) is int and 0<=i<current,'bad circuit topology')
            if i<start:
                require(i in leaves,'unauthorized external wire')
                return {(leaves[i],):1}
            return local[i]
        for current in range(start,end+1):
            z=nodes[current];op=z[0]
            if op=='const':
                require(len(z)==2 and type(z[1]) is int,'bad literal')
                poly={} if z[1]==0 else {():z[1]}
            else:
                require(op in ('+','-','*') and len(z)==3,'non-polynomial operation')
                a,b=get(z[1]),get(z[2])
                poly=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
            local[current]=poly
        return local[end]
    for k,block in enumerate(blocks):
        require(block['start']==cursor,'noncontiguous circuit block')
        end=block['root'];require(cursor<=end<len(nodes),'bad block root')
        kind=block['kind']
        if kind=='sum_of_squares':
            require(k==len(blocks)-1 and phase=='residual','bad SOS position')
            actual=local_expand(cursor,end,{r:j for j,r in enumerate(residual_nodes)})
            require(actual=={(j,j):1 for j in range(len(residual_nodes))},'not the declared sum of squares')
            require(end==program['output'] and end==len(nodes)-1,'output binding')
            cursor=end+1;continue
        require(kind in ('definition','residual'),'invalid block kind')
        r=block['source_row'];require(type(r) is int and 0<=r<len(rows) and r not in used_rows,'source row partition')
        used_rows.add(r);expected=rowpoly(rows[r]['terms'])
        if kind=='definition':
            require(phase=='definition','definition after residual')
            v=block['variable'];require(type(v) is int and 0<=v<n and v not in assigned,'duplicate or invalid assignment')
            epsilon=expected.pop((v,),None)
            require(epsilon in (-1,1) and not any(v in m for m in expected),'nonmonic or recursive pivot')
            expected={m:-epsilon*c for m,c in expected.items()}
        else:phase='residual'
        require(all(j in assigned for m in expected for j in m),'forward source dependency')
        actual=local_expand(cursor,end,registers)
        require(actual==expected,'circuit block does not equal its source polynomial')
        degree=max((sum(degrees[j] for j in m) for m in expected),default=0)
        norm=sum(abs(c)*math.prod(norms[j] for j in m) for m,c in expected.items())
        top=sum(c*math.prod(tops[j] for j in m) for m,c in expected.items() if sum(degrees[j] for j in m)==degree)%modulus
        if kind=='definition':
            assigned.add(v);registers[end]=v;degrees[v]=degree;norms[v]=norm;tops[v]=top
        else:
            residual_nodes.append(end);residual_rows.append(r);residual_degrees.append(degree);residual_norms.append(norm);residual_tops.append(top)
        cursor=end+1
    require(cursor==len(nodes),'unparsed nodes')
    require(assigned==set(range(n)),'missing source coordinates')
    require(used_rows==set(range(len(rows))),'missing source residuals')
    require(residual_nodes==program['residual_roots'],'residual roots mismatch')
    cert=program['degree_certificate'];d=max(residual_degrees)
    require(cert['source_variable_degrees']==[degrees[i] for i in range(n)],'degree recursion mismatch')
    require(cert['retained_source_rows']==residual_rows and cert['residual_degrees']==residual_degrees,'residual degree data mismatch')
    require(cert['modulus']==modulus and cert['input_direction']=='source_index + 3','leading certificate conventions')
    wr=cert['witness_source_row'];require(wr in residual_rows,'missing degree witness row');j=residual_rows.index(wr)
    require(residual_degrees[j]==d and residual_tops[j]!=0 and residual_tops[j]==cert['witness_top_residue'],'no nonzero leading witness')
    live=set();todo=[program['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('+','-','*'):todo.extend(nodes[i][1:])
    require({nodes[i][1] for i in live if nodes[i][0]=='var'}==set(range(len(inputs))),'unused quantified variable')
    metrics={'variables':len(inputs),'residuals':len(residual_rows),'eliminated_variables':n-len(inputs),
        'degree':2*d,'coefficient_height_strict_power_of_two':sum(v*v for v in residual_norms).bit_length(),
        'live_binary_operations':sum(nodes[i][0] in ('+','-','*') for i in live),
        'stored_nodes':len(nodes),'maximum_literal_constant':max(abs(z[1]) for z in nodes if z[0]=='const')}
    require(metrics==program['metrics'],'claimed metrics differ from exact checks')
    return metrics

def mutation_controls(source,sha,program):
    cases=[]
    q=copy.deepcopy(program);q['domain']='nonnegative integers';cases.append(q)
    q=copy.deepcopy(program);q['degree_certificate']['witness_top_residue']^=1;cases.append(q)
    q=copy.deepcopy(program);q['metrics']['coefficient_height_strict_power_of_two']-=1;cases.append(q)
    q=copy.deepcopy(program);b=next(b for b in q['blocks'] if b['kind']=='definition');b['variable']=q['retained_source_indices'][0];cases.append(q)
    q=copy.deepcopy(program);b=next(b for b in q['blocks'] if b['kind']=='residual');b['source_row']=0;cases.append(q)
    q=copy.deepcopy(program);j=next(j for j,z in enumerate(q['nodes']) if z[0]=='*');q['nodes'][j][0]='+';cases.append(q)
    q=copy.deepcopy(program);q['nodes'][q['output']][0]='-';cases.append(q)
    rejected=0
    for q in cases:
        try:check(source,sha,q)
        except (ValueError,KeyError,IndexError,TypeError):rejected+=1
        else:raise ValueError('A corrupted polynomial/certificate was accepted')
    return rejected

def main():
    pa=argparse.ArgumentParser(description=__doc__);pa.add_argument('--output',type=Path);a=pa.parse_args()
    raw=(ROOT/'source/equation248.json').read_bytes();source=json.loads(raw);sha=hashlib.sha256(raw).hexdigest()
    require(json.loads((ROOT/'SOURCE.json').read_text())['source_sha256']==sha,'source provenance mismatch')
    results=[]
    for file in sorted((ROOT/'equations').glob('*.json')):
        p=json.loads(file.read_text());metrics=check(source,sha,p)
        results.append({'name':file.stem,**metrics})
    selected=json.loads((ROOT/'equations/integer125_degree16.json').read_text())
    # A separate sparse engine expands the octic completely and checks exact
    # nonzero partial-derivative witnesses for every input of every circuit.
    expansion=subprocess.run([sys.executable,str(ROOT/'expand_octic.py'),'--check'],
        capture_output=True,text=True)
    require(expansion.returncode==0,'Independent expansion/dependency check failed: '+expansion.stderr)
    tables=subprocess.run([sys.executable,str(ROOT/'render_appendix.py'),'--check'],
        capture_output=True,text=True)
    require(tables.returncode==0,'Printed pivot-table check failed: '+tables.stderr)
    receipt={'status':'PASS','source_sha256':sha,'profiles':results,
             'negative_controls_rejected':mutation_controls(source,sha,selected),
             'all_variable_dependencies':'PASS: exact nonzero modular derivatives',
             'complete_printed_pivot_tables':8,
             'complete_octic_expansion':json.loads((ROOT/'expanded/octic_expansion_metrics.json').read_text()),
             'scope':'Exact finite algebra, integer polynomial maps, degree and coefficient-height bounds; inherited unbounded source theorem is not re-proved by this checker.'}
    if a.output:a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
