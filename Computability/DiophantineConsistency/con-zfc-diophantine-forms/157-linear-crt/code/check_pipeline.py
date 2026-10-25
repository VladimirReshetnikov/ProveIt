#!/usr/bin/env python3
"""Independent finite replay of the minimal-growth Diophantine arithmetic pipeline.

Usage:
  python3 -B check_pipeline.py PARENT_RAW_JSON NEW_STAGE_DIR [AFFINE_ENDPOINT_DIR ...]

The parent file is authenticated to the inspected upstream literal source.
This script imports only the separately written checker arithmetic, never a
producer, optimizer, or inherited source compiler. It authenticates finite
identities; it does not prove the unbounded number-theory/calibration lemmas.
"""
from pathlib import Path
import argparse, collections, copy, hashlib, json
from check_affine import require, decode, encode, add, multiply, substitute, check as check_affine

PARENT_SHA256='7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855'

def read(path):
    return json.loads(path.read_bytes())

def canonical(o):
    return (json.dumps(o,sort_keys=True,indent=2)+'\n').encode()

def digest_object(o):
    return hashlib.sha256((json.dumps(o,sort_keys=True,separators=(",", ":"))+"\n").encode()).hexdigest()

def variable(i):
    return {(i,):1}

def negative(p):
    return {m:-c for m,c in p.items()}

def degree(p):
    return max(map(len,p),default=0)

def row_polynomials(e):
    return [decode(r['terms']) for r in e['residuals']]

def linear_solution(p,i):
    co=p.get((i,),0)
    if co not in (-1,1) or any(i in m for m in p if m!=(i,)):
        return None
    return {m:-co*c for m,c in p.items() if m!=(i,)}

def metrics(rows,n):
    out={}
    for row in rows:
        out=add(out,multiply(row,row))
    m={'variables':n,'rows':len(rows),'degree':degree(out),'monomials':len(out),
       'height':max(map(abs,out.values())),'row_height':max(abs(c) for r in rows for c in r.values())}
    return m,out

def check_mutation(parent,new,mutation):
    require(all(mutation[k] is True for k in ['linear_radius','free_radix','linear_beta']),'the three advertised source mutations')
    minimal=mutation.get('minimal_growth',False)
    require(minimal in (True,False),'minimal growth flag')
    n={v['name']:i for i,v in enumerate(parent['variables'])}
    require(len(n)==len(parent['variables']),'unique parent names')
    fv=n['crt.growth_majorant_F'];rv=n['mul.1'];cv=n['crt.encoded_index_minus_one']
    bv=n['choose0.output'];hv=n['self_radix.BH']
    sb=n['beta.odd_square_multiplier'];vb=n['beta.odd_square_root_half']
    t0=n['t0'];d=n['growth.power_base'];hh=n['cofinal.horizon_root'] if 'cofinal.horizon_root' in n else None
    if hh is None:
        horizons=[decode(r['terms']) for r in parent['residuals'] if r['label']=='cofinal.horizon']
        require(len(horizons)==1,'one horizon row')
        squares=[m[0] for m,c in horizons[0].items() if len(m)==2 and m[0]==m[1] and c==-1]
        require(len(squares)==1,'one original horizon square')
        hh=squares[0]
    reps=[n['crt.encoded.'+s] for s in ['a','b','c','d','S','Sp','u','vq']]
    rows=[];edits=[];deletions=[]
    for index,row in enumerate(parent['residuals']):
        p=decode(row['terms'])
        if p==add(variable(rv),multiply(variable(fv),variable(fv)),-1):
            deletions.append((index,row));continue
        if row['label'] in ('radix.odd_square','beta.odd_square_multiplier'):
            deletions.append((index,row));continue
        if row['label']=='self_radix.base_definition':
            # New actual representatives are eight stored+1 values and C=2c.
            H={():34,(cv,):8}
            for j in reps:
                H=add(H,{(j,):4})
            p=add(variable(hv),multiply(variable(bv),H),-1)
            # C has already been rewritten in this independently formed row.
            rewrite_c=False
        else:
            rewrite_c=True
        p=substitute(p,rv,variable(fv))
        if rewrite_c:
            p=substitute(p,cv,{(cv,):2,():-1})
        p=substitute(p,sb,{(vb,):2,():1})
        if minimal:
            p=substitute(p,hh,{(hh,):2})
            if row['label']=='growth.base_definition':
                p=add(variable(d),{():16,(t0,):1},-1)
        require(degree(p)<=2,'mutation keeps rows quadratic')
        newrow=dict(row,terms=encode(p))
        rows.append(newrow)
        if newrow!=row:
            edits.append({'index':index,'old':row,'new':newrow})
    require(len(deletions)==3,'three and only three removed rows')
    require(new['residuals']==rows,'every mutated raw coefficient and row order')
    require(mutation['edits']==edits,'complete literal edit census')
    require([(d['index'],d['row']) for d in mutation['deletions']]==deletions,'complete literal deletion census')
    variables=copy.deepcopy(parent['variables'])
    variables[cv]['name']='crt.even_index_half'
    variables[vb]['name']='beta.odd_multiplier_half'
    require(new['variables']==variables,'only the advertised witness renames')
    require(new['domain']==parent['domain']=='unrestricted integers','integer domain')
    power_labels=[r['label'] for r in new['residuals'] if r['label'].endswith('.power_congruence')]
    require(power_labels==['pow'+str(i)+'.power_congruence' for i in range(18)],'all eighteen power requests retained')
    return {'minimal_growth':minimal,'source_edits':len(edits),'deleted_source_rows':len(deletions),'power_requests':len(power_labels)}

def check_factorization(raw,factored,cert):
    require(digest_object(raw)==cert['input_sha256'],'Horn input hash')
    require(digest_object(factored)==cert['output_sha256'],'Horn output hash')
    rows=row_polynomials(raw)
    original=[dict(r) for r in rows]
    names={v['name']:i for i,v in enumerate(raw['variables'])}
    sq=[names['sqd.'+str(i)] for i in range(17)]
    require(sq==cert['square_variables'],'seventeen literal square wires')
    roots={int(i):decode(v) for i,v in cert['square_roots'].items()}
    require(set(roots)==set(sq),'exact square-root coverage')
    defs={}
    for s in sq:
        hits=[i for i,p in enumerate(original) if raw['residuals'][i]['label']=='nonnegative_square_difference' and linear_solution(p,s) is not None]
        require(len(hits)==1,'unique square definition')
        defs[s]=hits[0]
        require(degree(roots[s])<=1,'affine square root')
        require(linear_solution(original[hits[0]],s)==multiply(roots[s],roots[s]),'exact root-square identity')
    chain=cert['product_chain']
    require(len(chain)==11 and len({i for i,v in chain})==11,'eleven distinct product rows')
    previous=sq[0]
    factors=sq[1:9]+['bundle',sq[13],sq[14]]
    for (ri,out),factor in zip(chain,factors):
        right=add(variable(sq[11]),variable(sq[12])) if factor=='bundle' else variable(factor)
        require(original[ri]==add(variable(out),multiply(variable(previous),right),-1),'literal old factor chain')
        previous=out
    oldroot=chain[-1][1]
    protected=set(sq[:9]+sq[13:15]+[v for _,v in chain[:-1]])
    allowed={defs[s] for s in sq[:9]+sq[13:15]}|{i for i,_ in chain}
    for ri,p in enumerate(original):
        if ri not in allowed:
            require(not any(i in protected for m in p for i in m),'factor privacy')
    changes=[]
    variables=copy.deepcopy(raw['variables'])
    def change(ri,p):
        changes.append({'row':ri,'old':encode(rows[ri]),'new':encode(p)})
        rows[ri]=p
    for s in sq[:9]+sq[13:15]:
        change(defs[s],add(variable(s),roots[s],-1))
        variables[s]['kind']='gate'
    (r9,o9),(r10,o10),(r11,o11)=chain[8:]
    change(r9,add(variable(o9),multiply(variable(chain[7][1]),variable(sq[13])),-1))
    change(r10,add(variable(o10),multiply(variable(o9),variable(sq[14])),-1))
    change(r11,add(variable(o11),multiply(variable(o10),variable(o10)),-1))
    newroot=len(variables)
    require(cert['new_root']==newroot,'new Horn root position')
    newrow=add(variable(newroot),multiply(variable(oldroot),add(variable(sq[11]),variable(sq[12]))),-1)
    require(decode(cert['new_row'])==newrow,'new Horn root definition')
    variables.append({'name':'factored.horn','kind':'gate'})
    for ri,p in enumerate(rows):
        if ri not in {i for i,_ in chain} and any(oldroot in m for m in p):
            change(ri,substitute(p,oldroot,variable(newroot)))
    rows.append(newrow)
    # Exact bundle refactoring uses only its private difference wires.
    gv=cert['guard_variables'];h=sq[9];unused=sq[10];g=gv['g'];dv=gv['old_D_square']
    require(gv['h']==h and gv['old_second_square']==unused,'guard wire identification')
    products=[ri for ri,p in enumerate(rows) if linear_solution(p,g)==multiply(variable(h),variable(unused))]
    ds=[ri for ri,p in enumerate(rows) if linear_solution(p,dv) is not None]
    require(len(products)==len(ds)==1,'unique guard product and square companion')
    pr,dr=products[0],ds[0];D2=linear_solution(rows[dr],dv)
    require(degree(D2)<=2,'quadratic companion')
    require(multiply(roots[sq[11]],roots[sq[11]])==multiply(add(variable(g),variable(dv),-1),add(variable(g),variable(dv),-1)),'guard difference root')
    guard_allowed={defs[h],defs[unused],pr,dr,defs[sq[11]]}
    for ri,p in enumerate(rows):
        if ri not in guard_allowed:
            require(not any(i in {h,unused,g,dv} for m in p for i in m),'guard privacy')
    change(defs[h],add(variable(h),multiply(roots[h],roots[unused]),-1))
    change(pr,add(add(variable(g),multiply(variable(h),variable(h)),-1),D2))
    change(defs[sq[11]],add(variable(sq[11]),multiply(variable(g),variable(g)),-1))
    variables[h]['kind']='gate'
    deleted=sorted([defs[unused],dr])
    require(deleted==cert['deleted_rows'],'guard row deletions')
    require(changes==cert['changes'],'complete Horn rewrite census')
    expected=[p for i,p in enumerate(rows) if i not in deleted]
    require(expected==row_polynomials(factored),'all factored coefficients')
    labels=[r['label'] for r in raw['residuals']]+['factored.horn']
    require([label for i,label in enumerate(labels) if i not in deleted]==[r['label'] for r in factored['residuals']],'factored row order')
    require(variables==factored['variables'],'factored variables and metadata')
    return {'affine_square_identities':len(sq),'Horn_local_rewrites':len(changes),'Horn_private_chain_products':len(chain),'Horn_deleted_rows':len(deleted)}

def check_projection(source,projected,certificate):
    require(digest_object(source)==certificate['input_sha256'],'projection source hash')
    require(digest_object(projected)==certificate['output_sha256'],'projection output hash')
    rows=row_polynomials(source)
    eliminated=set();removed_rows=set();by_kind=collections.Counter();by_degree=collections.Counter()
    for step in certificate['steps']:
        i=step['variable'];ri=step['row_id'];q=decode(step['restoration'])
        require(i not in eliminated and ri not in removed_rows,'fresh monic elimination')
        require(source['variables'][i]['name']==step['name'],'elimination variable binding')
        require(linear_solution(rows[ri],i)==q,'exact unit monic restoration')
        require(not any(j in eliminated or j==i for m in q for j in m),'acyclic integral restoration')
        require(degree(q)==step['restoration_degree'],'restoration degree')
        require(source['variables'][i]['kind']==step['kind'],'restoration kind')
        rows=[substitute(r,i,q) for r in rows]
        require(not rows[ri],'removed pivot vanishes')
        require(all(degree(r)<=2 for r in rows),'all intermediate residuals stay quadratic')
        eliminated.add(i);removed_rows.add(ri);by_kind[step['kind']]+=1;by_degree[str(degree(q))]+=1
    live={i for r in rows for m in r for i in m}
    unconstrained=set(range(len(source['variables'])))-eliminated-live
    require(sorted(unconstrained)==certificate['unconstrained_removed'],'only unconstrained leftovers discarded')
    keep=sorted(live);kept_rows=[i for i in range(len(rows)) if i not in removed_rows]
    require(keep==certificate['retained_original_variables'],'ordered retained coordinates')
    require(kept_rows==certificate['retained_original_rows'],'ordered retained rows')
    ren={i:j for j,i in enumerate(keep)}
    rr=[{tuple(ren[j] for j in m):c for m,c in rows[i].items()} for i in kept_rows]
    require(rr==row_polynomials(projected),'all projected coefficients')
    require([source['variables'][i] for i in keep]==projected['variables'],'projected variable metadata')
    require([source['residuals'][i]['label'] for i in kept_rows]==[r['label'] for r in projected['residuals']],'projected labels')
    m,p=metrics(rr,len(keep));cm=certificate['metrics']
    expected={'input_variables':len(source['variables']),'input_rows':len(source['residuals']),
              'output_variables':len(keep),'output_rows':len(rr),'eliminated_coordinates':len(eliminated),
              'unconstrained_removed':len(unconstrained),'exact_degree':m['degree'],'expanded_monomials':m['monomials'],
              'max_abs_expanded_coefficient':m['height'],'max_abs_row_coefficient':m['row_height'],
              'max_output_row_terms':max(map(len,rr)),'by_kind':dict(by_kind),'by_restoration_degree':dict(by_degree)}
    for key,value in expected.items():
        require(cm[key]==value,'projection metric '+key)
    return {'monic_eliminations':len(eliminated),'discarded_unconstrained_coordinates':len(unconstrained),'projected_variables':len(keep),'projected_rows':len(rr)}

def check_translation(projected,equation,translation,expansion,stated):
    require(translation['convention']=='old=new+shift','translation convention')
    shifts=translation['shifts'];require(len({i for i,d in shifts})==len(shifts),'distinct translation coordinates')
    rr=row_polynomials(projected)
    for i,d in shifts:
        require(isinstance(d,int) and 0<=i<len(projected['variables']),'integral translation')
        rr=[substitute(r,i,{(i,):1,():d}) for r in rr]
    require(rr==row_polynomials(equation),'all translated coefficients')
    require(projected['variables']==equation['variables'],'translation retains variable order')
    require([r['label'] for r in projected['residuals']]==[r['label'] for r in equation['residuals']],'translation retains row order')
    m,p=metrics(rr,len(equation['variables']))
    require(m==stated,'base metrics')
    require(p==decode(expansion['terms']),'entire base expansion')
    require({i for monomial in p for i in monomial}==set(range(m['variables'])),'base polynomial liveness')
    return {'translations':len(shifts),'result':m}

def check(parent_path,stage,endpoint_paths=()):
    require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==PARENT_SHA256,'pinned inherited raw source bytes')
    parent=read(parent_path);raw=read(stage/'raw_source.json');factored=read(stage/'factored_source.json');projected=read(stage/'projected.json');equation=read(stage/'equation.json')
    output={'parent_sha256':PARENT_SHA256,'raw_source_sha256':hashlib.sha256((stage/'raw_source.json').read_bytes()).hexdigest(),
            'equation_sha256':hashlib.sha256((stage/'equation.json').read_bytes()).hexdigest()}
    output['mutation']=check_mutation(parent,raw,read(stage/'mutation.json'))
    output['factorization']=check_factorization(raw,factored,read(stage/'factorization_certificate.json'))
    output['projection']=check_projection(factored,projected,read(stage/'projection_certificate.json'))
    output['translation']=check_translation(projected,equation,read(stage/'translation_certificate.json'),read(stage/'expanded_polynomial.json'),read(stage/'METRICS.json'))
    output['affine_endpoints']=[check_affine(stage/'equation.json',ep) for ep in endpoint_paths]
    output['status']='all finite checks passed'
    return output

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent',type=Path);parser.add_argument('stage',type=Path);parser.add_argument('endpoints',type=Path,nargs='*')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args();result=check(args.parent,args.stage,args.endpoints)
    data=canonical(result)
    if args.receipt:
        args.receipt.write_bytes(data)
    print(data.decode(),end='')
