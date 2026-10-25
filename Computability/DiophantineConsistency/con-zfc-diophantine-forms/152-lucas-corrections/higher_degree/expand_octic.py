#!/usr/bin/env python3
"""Independent literal expansion of the octic and dependency certificates."""
import json, hashlib, pathlib, sys, time
ROOT=pathlib.Path(__file__).resolve().parent
OUT=ROOT/'expanded'

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            t=tuple(sorted(m+n));out[t]=out.get(t,0)+c*d
    return {m:c for m,c in out.items() if c}

def combine(terms,registers):
    out={}
    for c,m in terms:
        p={():c}
        for j in m:p=mul(p,registers[j])
        for n,d in p.items():out[n]=out.get(n,0)+d
    return {m:c for m,c in out.items() if c}

def gradient(program,shift,mod=1000000007):
    nodes=program['nodes'];vals=[]
    point=[i+shift for i in range(len(program['variables']))]
    for node in nodes:
        op=node[0]
        if op=='var':v=point[node[1]]
        elif op=='const':v=node[1]
        elif op=='+':v=vals[node[1]]+vals[node[2]]
        elif op=='-':v=vals[node[1]]-vals[node[2]]
        elif op=='*':v=vals[node[1]]*vals[node[2]]
        else:raise ValueError(op)
        vals.append(v%mod)
    derivatives=[0]*len(nodes);derivatives[program['output']]=1
    for j in range(len(nodes)-1,-1,-1):
        node=nodes[j];op=node[0];d=derivatives[j]
        if op in ('+','-','*'):
            a,b=node[1:]
            da=d*vals[b] if op=='*' else d
            db=d*vals[a] if op=='*' else -d if op=='-' else d
            derivatives[a]=(derivatives[a]+da)%mod
            derivatives[b]=(derivatives[b]+db)%mod
    return [derivatives[j] for j,node in enumerate(nodes) if node[0]=='var']

def main():
    import argparse
    pa=argparse.ArgumentParser(description=__doc__);pa.add_argument('--check',action='store_true');args=pa.parse_args()
    OUT.mkdir(exist_ok=True)
    def emit(path,data):
        raw=json.dumps(data,separators=(',',':'))+'\n'
        if args.check:
            if path.read_text()!=raw:raise ValueError('Reconstruction mismatch: '+str(path))
        else:path.write_text(raw)
    dep=[]
    for f in sorted((ROOT/'equations').glob('*.json')):
        program=json.loads(f.read_text());n=len(program['variables'])
        missing=set(range(n));witnesses=[]
        for shift in (3,5,17,61):
            g=gradient(program,shift)
            got=sorted(i for i in missing if g[i])
            if got:witnesses.append({'input_direction':f'index + {shift}','derivatives':[[i,g[i]] for i in got]})
            missing.difference_update(got)
            if not missing:break
        if missing:raise ValueError((f.name,missing))
        dep.append({'equation':f.name,'variables':n,'all_variables_essential':True,'modulus':1000000007,'witnesses':witnesses})
    emit(ROOT/'DEPENDENCY_CERTIFICATES.json',dep)
    f=ROOT/'equations/integer153_degree8.json';program=json.loads(f.read_text())
    source=json.loads((ROOT/'source/equation248.json').read_text())
    registers={v:{(i,):1} for i,v in enumerate(program['retained_source_indices'])}
    residuals=[];polynomial={};start=time.monotonic()
    for b in program['blocks']:
        kind=b['kind']
        if kind=='sum_of_squares':continue
        terms=source['residuals'][b['source_row']]['terms']
        if kind=='definition':
            v=b['variable'];e=next(c for c,m in terms if m==[v])
            terms=[[-e*c,m] for c,m in terms if m!=[v]]
            registers[v]=combine(terms,registers)
        else:
            p=combine(terms,registers);residuals.append({'source_row':b['source_row'],'terms':[[c,list(m)] for m,c in sorted(p.items())]})
            p2=mul(p,p)
            for m,c in p2.items():polynomial[m]=polynomial.get(m,0)+c
    polynomial={m:c for m,c in polynomial.items() if c}
    result={'variables':len(program['variables']),'residuals':len(residuals),'degree':max(map(len,polynomial)),
            'monomials':len(polynomial),'coefficient_height':max(map(abs,polynomial.values())),
            'residual_monomials':sum(len(r['terms']) for r in residuals),
            'source_equation_sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
    emit(OUT/'octic_expanded.json',{'metrics':result,'polynomial':[[c,list(m)] for m,c in sorted(polynomial.items())]})
    emit(OUT/'octic_residuals.json',{'metrics':result,'residuals':residuals})
    emit(OUT/'octic_expansion_metrics.json',result)
    print(result,'seconds',round(time.monotonic()-start,2))

if __name__=='__main__':main()
