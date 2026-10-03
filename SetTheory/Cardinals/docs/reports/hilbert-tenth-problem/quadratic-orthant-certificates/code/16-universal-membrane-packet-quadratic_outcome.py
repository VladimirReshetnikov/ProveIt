#!/usr/bin/env python3
"""Explicit degree-two fixed-time outcome polynomials using affine branch domains.
A legal branch is parametrized by natural bases: positive SUB old=x+e,new=x;
zero SUB omits its tested base; ADD old=x,new=x+e. No guard/slack variables.
The file export lists every affine square and product, with fully listed shared
linear forms. T is an external compiler parameter, not an existential witness.
"""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent

def semantic_table(program):
    rows=program['rows'];labels=list(rows)+['HALT'];code={s:i for i,s in enumerate(labels)}
    d=len(program.get('registers',['A','B']));branches=[];subidx=0
    for l,row in rows.items():
        op,r,*dst=row;assert 0<=r<d
        if op=='ADD':
            branches.append({'source':code[l],'target':code[dst[0]],'delta':[int(r==i) for i in range(d)],'guard':None,'register':r})
        else:
            assert op=='SUB'
            branches.append({'source':code[l],'target':code[dst[0]],'delta':[-int(r==i) for i in range(d)],'guard':'positive','register':r,'sub_index':subidx})
            branches.append({'source':code[l],'target':code[dst[1]],'delta':[0]*d,'guard':'zero','register':r,'sub_index':subidx})
            subidx+=1
    return {'labels':labels,'entry':code[program['entry']],'halt':code['HALT'],'register_count':d,'branches':branches,'sub_count':subidx}

def affine(*,forms=(),variables=(),parameters=(),constant=0):
    return {'forms':[list(x) for x in forms],'variables':[list(x) for x in variables],
            'parameters':[list(x) for x in parameters],'constant':constant}

def base_layout(table):
    result=[];n=0
    for branch in table['branches']:
        row=[]
        for i in range(table['register_count']):
            if branch['guard']=='zero' and i==branch['register']:row.append(None)
            else:row.append(n);n+=1
        result.append(row)
    assert n==table['register_count']*len(table['branches'])-table['sub_count']
    return result,n

def compile_schema(table,T,*,entry=None,target=None,initial=None):
    if type(T) is not int or T<0:raise ValueError('T must be a natural external integer')
    entry=table['entry'] if entry is None else entry;target=table['halt'] if target is None else target
    d=table['register_count'];B=len(table['branches']);S=table['sub_count'];layout,nb=base_layout(table);stride=B+nb
    if initial is None:initial=['raw_A',0] if d==2 else [f'input_{i}' for i in range(d)]
    assert len(initial)==d and all(type(x) is str or (type(x) is int and x>=0) for x in initial)
    parameters={s:('positive integer' if s=='raw_A' else 'natural integer') for s in initial if type(s) is str}
    groups={};squares=[];products=[]
    def selector(j,r):return j*stride+r
    def base(j,r,i):
        k=layout[r][i];return None if k is None else j*stride+B+k
    def f(j,n):return f'{n}:{j}'
    for j in range(T):
        groups[f(j,'E')]=[[selector(j,r),1] for r in range(B)]
        for name,field in [('Q','source'),('D','target')]:
            groups[f(j,name)]=[[selector(j,r),b[field]] for r,b in enumerate(table['branches']) if b[field]]
        for i in range(d):
            old=[];new=[]
            for r,b in enumerate(table['branches']):
                k=base(j,r,i)
                if k is not None:old.append([k,1]);new.append([k,1])
                if i==b['register']:
                    if b['guard']=='positive':old.append([selector(j,r),1])
                    elif b['guard'] is None:new.append([selector(j,r),1])
            groups[f(j,f'OLD{i}')]=old;groups[f(j,f'NEW{i}')]=new
        squares.append({'name':f'onehot:{j}','affine':affine(forms=[(f(j,'E'),1)],constant=-1)})
        squares.append({'name':f'control:{j}','affine':affine(forms=[(f(j,'Q'),1)]+([] if j==0 else [(f(j-1,'D'),-1)]),constant=-entry if j==0 else 0)})
        for i in range(d):
            init=initial[i]
            squares.append({'name':f'counter{i}:{j}','affine':affine(
                forms=[(f(j,f'OLD{i}'),1)]+([] if j==0 else [(f(j-1,f'NEW{i}'),-1)]),
                parameters=[(init,-1)] if j==0 and type(init) is str else [],
                constant=-init if j==0 and type(init) is int else 0)})
        for r,b in enumerate(table['branches']):
            # The first factor equals the sum of all *other* natural selectors.
            products.append({'name':f'inactive:{j}:{r}',
                'left':affine(forms=[(f(j,'E'),1)],variables=[(selector(j,r),-1)]),
                'right':affine(variables=[(selector(j,r),1)]+[(base(j,r,i),1) for i in range(d) if base(j,r,i) is not None])})
    final=affine(forms=[(f(T-1,'D'),1)],constant=-target) if T else affine(constant=entry-target)
    squares.append({'name':'terminal','affine':final})
    out={'format':'explicit-affine-squares-and-products-v3','domain':'natural witnesses, including zero; for natural input the strengthened gates give exactly the same zero set over nonnegative real witnesses',
      'parameters':parameters,'initial_counters':initial,'external_time':T,'entry_code':entry,'terminal_code':target,'halt_code':table['halt'],
      'variables':{'count':stride*T,'per_step':stride,'branch_count':B,'sub_count':S,'register_count':d,
                  'base_count_per_step':nb,'base_offsets_by_branch':layout,
                  'indexing':'at step j: selectors j*stride+[0,B); base for branch r and register i is j*stride+B+base_offsets_by_branch[r][i]; null means omitted zero-branch tested base'},
      'linear_forms':groups,'affine_squares':squares,'quadratic_products':products,
      'polynomial':'sum(affine_squares.affine^2)+sum(quadratic_products.left*right)',
      'ledger':{'natural_witnesses':stride*T,'affine_squares':(d+2)*T+1,'quadratic_products':B*T,'degree_at_most':2},
      'scope':'Exact endpoint existence at this fixed register-instruction count. HALT has no outgoing row, so terminal HALT is first halt. Not an arbitrary membrane-trace verifier or fixed-arity unbounded-time polynomial.'}
    assert len(squares)==out['ledger']['affine_squares'] and len(products)==B*T
    return out

def evaluate(packet,witness,parameters,*,details=False):
    if type(parameters) is int:parameters={'raw_A':parameters}
    if set(parameters)!=set(packet['parameters']):raise ValueError('wrong polynomial parameters')
    for name,value in parameters.items():
        if type(value) is not int or value<(1 if packet['parameters'][name]=='positive integer' else 0):raise ValueError('parameter outside natural domain')
    V=packet['variables']['count']
    if any(type(k) is not int or not 0<=k<V or type(v) is not int or v<0 for k,v in witness.items()):raise ValueError('invalid natural witness coordinate')
    forms={f:sum(c*witness.get(i,0) for i,c in terms) for f,terms in packet['linear_forms'].items()}
    def val(x):
        if any(p not in parameters for p,c in x['parameters']):raise ValueError('unknown polynomial parameter')
        return x['constant']+sum(c*forms[f] for f,c in x['forms'])+sum(c*witness.get(i,0) for i,c in x['variables'])+sum(c*parameters[p] for p,c in x['parameters'])
    violations=[];total=0
    for z in packet['affine_squares']:
        v=val(z['affine']);total+=v*v
        if v:violations.append([z['name'],v])
    for z in packet['quadratic_products']:
        a=val(z['left']);b=val(z['right']);assert a>=0 and b>=0,(z['name'],a,b)
        total+=a*b
        if a*b:violations.append([z['name'],a*b])
    return (total,violations) if details else total

def witness_for_trace(table,T,initial,*,entry=None):
    if type(T) is not int or T<0:raise ValueError('T must be natural')
    d=table['register_count']
    if type(initial) is int:
        if d!=2 or initial<1:raise ValueError('integer shorthand is positive A with B=0')
        initial=[initial,0]
    if len(initial)!=d or any(type(x) is not int or x<0 for x in initial):raise ValueError('natural initial registers required')
    B=len(table['branches']);layout,nb=base_layout(table);stride=B+nb
    control=table['entry'] if entry is None else entry;regs=list(initial);w={};trace=[]
    bysource={}
    for r,z in enumerate(table['branches']):bysource.setdefault(z['source'],[]).append((r,z))
    for j in range(T):
        if control==table['halt']:raise ValueError('halted before requested exact time')
        possible=[]
        for r,z in bysource[control]:
            n=regs[z['register']]
            if z['guard'] is None or (z['guard']=='positive' and n>0) or (z['guard']=='zero' and n==0):possible.append((r,z))
        assert len(possible)==1;r,z=possible[0];offset=j*stride;w[offset+r]=1
        for i,value in enumerate(regs):
            k=layout[r][i]
            if k is None:assert value==0;continue
            value-=int(z['guard']=='positive' and i==z['register'])
            assert value>=0
            if value:w[offset+B+k]=value
        trace.append({'source':control,'registers':regs.copy(),'branch':r})
        regs=[a+b for a,b in zip(regs,z['delta'])];assert min(regs)>=0;control=z['target']
    return w,control,tuple(regs),trace

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--steps',type=int,default=1);ap.add_argument('--output',type=Path)
    args=ap.parse_args();program=json.loads((ROOT/'literal2.json').read_text());table=semantic_table(program)
    schema=compile_schema(table,args.steps);out=args.output or ROOT/f'quadratic_schema_T{args.steps}.json'
    out.write_text(json.dumps(schema,separators=(',',':'))+'\n')
    (ROOT/'semantic_branches.json').write_text(json.dumps(table,separators=(',',':'))+'\n')
    print(json.dumps({'output':str(out),'branches':len(table['branches']),**schema['ledger']},indent=2))
if __name__=='__main__':main()
