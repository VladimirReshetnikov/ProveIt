#!/usr/bin/env python3
"""Independent exact audit of the final 247-variable quartic.

Imports only the standard library. It uses sparse exponent-vector monomials
and the binomial formula for shears, independently of build_final.py and the
earlier compiler. It also parses the printed TeX back into polynomials.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse, ast, copy, hashlib, json, math, re

ROOT=Path(__file__).resolve().parents[1]
RAW_SHA='14b814894521add09fb6847e59de2d802f2e466f6f9fc724f346a21461125a6b'
OLD_EQ_SHA='500cb73f06e880bfa8585a28985219229464d7f097156219c80e2032ce28539e'
OLD_SHEAR_SHA='8b018b77dc0b1748318a7e0f8c0de4dac65d41260ba36800db4d981df9b1ec4f'

def require(ok,reason):
    if not ok:raise ValueError(reason)

def canonical(obj):
    return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def digest(data):return hashlib.sha256(data).hexdigest()

def exponent_monomial(indices):
    require(all(type(i) is int and i>=0 for i in indices),'invalid variable index')
    return tuple(sorted(Counter(indices).items()))

def read_polynomial(terms):
    result=defaultdict(int)
    for coefficient,indices in terms:
        require(type(coefficient) is int,'coefficient is not an integer')
        result[exponent_monomial(indices)]+=coefficient
    return {m:c for m,c in result.items() if c}

def add_scaled(p,q,k):
    out=dict(p)
    for mon,c in q.items():
        out[mon]=out.get(mon,0)+k*c
        if not out[mon]:del out[mon]
    return out

def multiply(p,q):
    out=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():
            mon=dict(a)
            for i,e in b:mon[i]=mon.get(i,0)+e
            out[tuple(sorted(mon.items()))]+=c*d
    return {m:c for m,c in out.items() if c}

def degree(p):return max((sum(e for i,e in m) for m in p),default=0)

def shear(p,i,j,k):
    # (x_j+k*x_i)^e is expanded directly by the binomial theorem.
    out=defaultdict(int)
    for mon,c in p.items():
        powers=dict(mon);e=powers.get(j,0)
        for t in range(e+1):
            new=dict(powers);new[j]=e-t
            if not new[j]:new.pop(j,None)
            if t:new[i]=new.get(i,0)+t
            out[tuple(sorted(new.items()))]+=c*math.comb(e,t)*(k**t)
    return {m:c for m,c in out.items() if c}

def identity(n):return [{i:1} for i in range(n)]

def coordinate_matrix(history,n):
    mat=identity(n)
    for step in history:
        i,j,k=(step[a] for a in ('i','j','k'))
        for row in mat:
            value=row.get(i,0)+k*row.get(j,0)
            if value:row[i]=value
            else:row.pop(i,None)
    return mat

def row_matrix(operations,n):
    mat=identity(n)
    for i,j,k in operations:
        out=dict(mat[i])
        for a,c in mat[j].items():
            value=out.get(a,0)+k*c
            if value:out[a]=value
            else:out.pop(a,None)
        mat[i]=out
    return mat

def compose_matrices(a,b):
    out=[]
    for row in a:
        r=defaultdict(int)
        for j,c in row.items():
            for k,d in b[j].items():r[k]+=c*d
        out.append({i:c for i,c in r.items() if c})
    return out

def parse_tex(text):
    pattern=re.compile(r'\\begin\{equation\*\}\\begin\{aligned\}\s*R_\{(\d+)\}&=(.*?)\\end\{aligned\}\\end\{equation\*\}',re.S)
    blocks=list(pattern.finditer(text));rows=[]
    leftovers=pattern.sub('',text)
    leftovers=re.sub(r'%[^\n]*','',leftovers)
    require(not leftovers.strip(),'unparsed residual TeX content')
    for want,match in enumerate(blocks,1):
        require(int(match.group(1))==want,'printed residual order')
        body=match.group(2).replace(r'\quad','').replace(r'\,','').replace('\\\\','').replace('&','')
        body=''.join(body.split());result={}
        for term in re.findall(r'[+-]?[^+-]+',body):
            m=re.fullmatch(r'([+-]?)(\d*)(.*)',term)
            sign,number,tail=m.groups();coefficient=(-1 if sign=='-' else 1)*(int(number) if number else 1)
            var_pattern=re.compile(r'z_\{(\d+)\}(?:\^\{(\d+)\})?')
            variables=list(var_pattern.finditer(tail))
            require(''.join(v.group(0) for v in variables)==tail,'unsupported printed polynomial term')
            require(number or variables,'empty printed polynomial term')
            powers=Counter()
            for v in variables:
                idx=int(v.group(1))-1;power=int(v.group(2) or 1)
                require(idx>=0 and power>=1,'invalid printed coordinate or exponent');powers[idx]+=power
            mon=tuple(sorted(powers.items()));result[mon]=result.get(mon,0)+coefficient
            if not result[mon]:del result[mon]
        require(body and rows is not None,'empty printed residual')
        rows.append(result)
    return rows

def bundle(root):
    paths={
      'raw':'source/equation247_weak/equation.json',
      'shears':'certificates/coordinate_shears.json',
      'row_ops':'certificates/row_operations.json',
      'old_equation':'certificates/inherited_shear_equation.json',
      'old_shears':'certificates/inherited_shears.json',
      'provenance':'certificates/shear_transfer_provenance.json',
      'equation':'equations/quartic247/equation.json',
      'polynomial':'equations/quartic247/expanded_polynomial.json',
      'metrics':'equations/quartic247/metrics.json',
      'coordinate_map':'equations/quartic247/coordinate_map.json',
    }
    data={key:json.loads((root/path).read_text()) for key,path in paths.items()}
    data['tex']=(root/'report_inputs/residuals.tex').read_text()
    data['text']=(root/'equations/quartic247/residuals.txt').read_text()
    data['metric_tex']=(root/'report_inputs/metrics.tex').read_text()
    return data

def verify_provenance(d):
    require(digest(canonical(d['raw']))==RAW_SHA,'raw quartic is not the audited weak-product source')
    require(digest(canonical(d['old_equation']))==OLD_EQ_SHA,'historical equation pin')
    require(digest(canonical(d['old_shears']))==OLD_SHEAR_SHA,'historical shear pin')
    old=d['old_shears']['history'];new=d['shears']['history'];p=d['provenance']
    require(len(old)==len(new)==76,'76 historical shears required')
    require(p['original_equation_sha256']==OLD_EQ_SHA and p['original_shears_sha256']==OLD_SHEAR_SHA and p['new_raw_equation_sha256']==RAW_SHA,'provenance file bindings')
    names={v['name']:i for i,v in enumerate(d['raw']['variables'])}
    require(len(names)==len(d['raw']['variables']),'raw coordinate names not unique')
    entries=[]
    for a,b in zip(old,new):
        ni=d['old_equation']['variables'][a['i']]['pre_shear_origin']['name']
        nj=d['old_equation']['variables'][a['j']]['pre_shear_origin']['name']
        require(ni in names and nj in names,'historical shear coordinate missing')
        require(b=={'i':names[ni],'j':names[nj],'k':a['k']},'shear transfer disagrees with historical names')
        entries.append({'original':a,'transferred':b,'i_name':ni,'j_name':nj})
    require(entries==p['entries'],'provenance literal name mapping')
    return len(entries)

def verify(d):
    transferred=verify_provenance(d)
    raw=d['raw'];eq=d['equation'];n=len(raw['variables']);r=len(raw['residuals'])
    require(n==247 and r==182,'raw size mismatch')
    require(raw['domain']==eq['domain']==d['polynomial']['domain']=='unrestricted integers','wrong variable domain')
    original=[read_polynomial(x['terms']) for x in raw['residuals']];rows=copy.deepcopy(original)
    history=d['shears']['history'];ops=d['row_ops']
    require(d['shears']['step_meaning']=='old x_j=new x_j+k new x_i','coordinate map convention')
    # Check every coordinate step in both directions, not just the endpoint.
    for step in history:
        i,j,k=(step[v] for v in ('i','j','k'))
        require(all(type(v)is int for v in [i,j,k]) and 0<=i<n and 0<=j<n and i!=j,'invalid shear')
        before=rows;rows=[shear(p,i,j,k) for p in rows]
        require([shear(p,i,j,-k) for p in rows]==before,'a coordinate step has no claimed inverse')
        require(all(degree(p)<=2 for p in rows),'shear changed residual degree')
    after_coordinates=copy.deepcopy(rows)
    require(len(ops)==4,'four frozen row operations required')
    for i,j,k in ops:
        require(all(type(v)is int for v in [i,j,k]) and 0<=i<r and 0<=j<r and i!=j,'invalid row operation')
        before=rows[i];rows[i]=add_scaled(rows[i],rows[j],k)
        require(add_scaled(rows[i],rows[j],-k)==before,'a row operation has no claimed inverse')
    require(all(degree(p)<=2 for p in rows),'final residual not quadratic')
    published=[read_polynomial(x['terms']) for x in eq['residuals']]
    require(published==rows,'final residual coefficients disagree with reconstructed maps')
    require([x['label'] for x in eq['residuals']]==['R_'+str(i+1) for i in range(r)],'residual labels differ')
    require(len(eq['variables'])==n,'final coordinate census')
    for i,(a,b) in enumerate(zip(raw['variables'],eq['variables'])):
        require(b=={'name':'z_'+str(i+1),'kind':'unrestricted_integer','pre_shear_origin':a},'final coordinate origin mismatch')
    reverse=copy.deepcopy(published)
    for i,j,k in reversed(ops):reverse[i]=add_scaled(reverse[i],reverse[j],-k)
    require(reverse==after_coordinates,'whole reverse row map failed')
    for step in reversed(history):reverse=[shear(p,step['i'],step['j'],-step['k']) for p in reverse]
    require(reverse==original,'whole reverse coordinate map failed')
    # Independently compute the full integer coordinate and row matrices.
    matrix=coordinate_matrix(history,n)
    inverse=coordinate_matrix([dict(s,k=-s['k']) for s in reversed(history)],n)
    require(compose_matrices(matrix,inverse)==identity(n) and compose_matrices(inverse,matrix)==identity(n),'coordinate matrices not inverse over Z')
    rowmat=row_matrix(ops,r);rowinv=row_matrix([(i,j,-k) for i,j,k in reversed(ops)],r)
    require(compose_matrices(rowmat,rowinv)==identity(r) and compose_matrices(rowinv,rowmat)==identity(r),'row matrices not inverse over Z')
    cmap=d['coordinate_map'];require(cmap['determinant']==1,'coordinate determinant claim')
    map_polys=[read_polynomial(t) for t in cmap['old_coordinates']]
    expected_maps=[{((j,1),):c for j,c in a.items()} for a in matrix]
    require(map_polys==expected_maps,'published complete coordinate map differs')
    # Ordered Cartesian multiplication is deliberately independent of the
    # producer's half-triangle sum-of-squares accumulator.
    polynomial={}
    for p in rows:polynomial=add_scaled(polynomial,multiply(p,p),1)
    require(read_polynomial(d['polynomial']['terms'])==polynomial,'expanded quartic coefficient mismatch')
    require(len(d['polynomial']['terms'])==len(polynomial),'expanded list is not collected')
    require(d['polynomial']['variables']==n,'expanded coordinate census')
    used={i for m in polynomial for i,e in m}
    require(used==set(range(n)),'final quartic has an unused advertised variable')
    require(parse_tex(d['tex'])==rows,'printed TeX residual differs from JSON')
    textrows=[]
    for index,line in enumerate(d['text'].splitlines(),1):
        prefix='R_'+str(index)+' = ';require(line.startswith(prefix),'readable row label mismatch')
        textrows.append(read_polynomial(ast.literal_eval(line[len(prefix):])))
    require(textrows==rows,'readable residuals differ from JSON')
    metrics={'variables':n,'domain':'unrestricted integers','quadratic_residuals':r,
             'degree':degree(polynomial),'collected_monomials':len(polynomial),
             'coefficient_height':max(abs(c) for c in polynomial.values()),
             'residual_height':max(abs(c) for p in rows for c in p.values()),
             'residual_monomials':sum(len(p) for p in rows),
             'coordinate_shears':len(history),'residual_row_operations':len(ops)}
    require(metrics==d['metrics'],'metrics disagree with literal collected polynomial')
    macros=dict(re.findall(r'\\newcommand\{\\(FinalTerms|FinalHeight|FinalRows)\}\{([0-9,]+)\}',d['metric_tex']))
    require(macros=={'FinalTerms':format(len(polynomial),','),'FinalHeight':format(metrics['coefficient_height'],','),'FinalRows':str(r)},'printed metric macros differ')
    require(metrics['degree']==4,'degree is not exactly four')
    return {'status':'PASS','metrics':metrics,'named_historical_transfers':transferred,
            'coordinate_step_inverse_checks':len(history),'row_step_inverse_checks':len(ops),
            'full_coordinate_matrix_left_and_right_inverse':True,
            'full_residual_matrix_left_and_right_inverse':True,
            'whole_polynomial_reverse_map':True,'parsed_printed_residuals':len(rows),
            'equation_sha256':digest(canonical(eq)),'polynomial_sha256':digest(canonical(d['polynomial']))}

def corruption_controls(d):
    results=[]
    def trial(label,change):
        other=copy.deepcopy(d);change(other)
        try:verify(other)
        except (ValueError,TypeError,KeyError,IndexError) as exc:
            results.append({'name':label,'rejected':True,'reason':str(exc)})
        else:raise ValueError('Uncaught corrupted artifact: '+label)
    trial('shear_coefficient',lambda x:x['shears']['history'][0].__setitem__('k',1))
    trial('historical_coordinate_name',lambda x:x['provenance']['entries'][0].__setitem__('i_name','wrong_coordinate'))
    trial('row_operation_coefficient',lambda x:x['row_ops'][0].__setitem__(2,-21))
    trial('final_residual_coefficient',lambda x:x['equation']['residuals'][0]['terms'][0].__setitem__(0,-2))
    trial('collected_coefficient',lambda x:x['polynomial']['terms'][0].__setitem__(0,x['polynomial']['terms'][0][0]+1))
    trial('published_coordinate_map',lambda x:x['coordinate_map']['old_coordinates'][0][0].__setitem__(0,2))
    trial('printed_tex_coefficient',lambda x:x.__setitem__('tex',x['tex'].replace('-z_{4}^{2}','-2z_{4}^{2}',1)))
    trial('incorrect_domain',lambda x:x['equation'].__setitem__('domain','nonnegative integers'))
    return results

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--receipt',type=Path);p.add_argument('--skip-controls',action='store_true')
    args=p.parse_args();data=bundle(args.root);answer=verify(data)
    if not args.skip_controls:answer['corruption_controls']=corruption_controls(data)
    answer['scope']='Independent finite algebra and printed-specification audit. This does not replace the unbounded arithmetic proof or certify consistency.'
    text=json.dumps(answer,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
