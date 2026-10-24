import json, pathlib, sys, argparse, hashlib, copy

def collect(terms):
    out={}
    for c,m in terms:
        key=tuple(sorted(m));out[key]=out.get(key,0)+c
    return {m:c for m,c in out.items() if c}

def pack(poly):return [[c,list(m)] for m,c in sorted(poly.items()) if c]

def mul(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(sorted(ma+mb));out[m]=out.get(m,0)+ca*cb
    return {m:c for m,c in out.items() if c}

def substitute(poly,v,definition):
    out={}
    for m,c in poly.items():
        term={():c}
        for u in m:term=mul(term,definition if u==v else {(u,):1})
        for n,d in term.items():out[n]=out.get(n,0)+d
    return {m:c for m,c in out.items() if c}

def contract(eq,cap=64,order='first'):
    rows={i:collect(r['terms']) for i,r in enumerate(eq['residuals'])};live=set(range(len(eq['variables'])));steps=[]
    while True:
        nonlinear={v for r in rows.values() for m in r if len(m)>1 for v in m}
        possible=[]
        for rid,row in sorted(rows.items()):
            for m,c in row.items():
                if len(m)!=1 or abs(c)!=1:continue
                v=m[0]
                if any(v in n for n in row if n!=m):continue
                definition={n:-d*c for n,d in row.items() if n!=m}
                if len(definition)>cap:continue
                degree=max(map(len,definition),default=0)
                if degree>1 and v in nonlinear:continue
                possible.append((rid,v,c,definition))
        if not possible:break
        if order=='short':
            choice=min(possible,key=lambda p:(len(p[3]),max(map(len,p[3]),default=0),p[1],p[0]))
        elif order=='terminal':choice=min(possible,key=lambda p:(-max(map(len,p[3]),default=0),len(p[3]),p[1],p[0]))
        else:choice=possible[0]
        rid,v,c,d=choice
        steps.append({'row_id':rid,'variable':v,'sign':c,'row':pack(rows[rid]),'definition':pack(d)})
        del rows[rid];live.remove(v)
        for i in rows:rows[i]=substitute(rows[i],v,d)
    used=sorted({v for r in rows.values() for m in r for v in m});idx={v:i for i,v in enumerate(used)}
    ids=[i for i in sorted(rows) if rows[i]]
    out=copy.deepcopy(eq);out['variables']=[eq['variables'][v] for v in used]
    out['residuals']=[{'label':eq['residuals'][i]['label'],'terms':pack({tuple(idx[v] for v in m):c for m,c in rows[i].items()})} for i in ids]
    cert={'steps':steps,'retained':used,'unused':sorted(live-set(used)),'row_ids':ids}
    return out,cert

def metrics(eq):
    poly={}
    for row in eq['residuals']:
        r=collect(row['terms'])
        for m,c in mul(r,r).items():poly[m]=poly.get(m,0)+c
    poly={m:c for m,c in poly.items() if c}
    met={'variables':len(eq['variables']),'residuals':len(eq['residuals']),'degree':max(map(len,poly)),'monomials':len(poly),'coefficient_height':max(map(abs,poly.values()))}
    return met,{'schema':'sparse_integer_polynomial_v1','domain':'integers','variables':len(eq['variables']),'terms':pack(poly)}

def lift(source,guards,monic=True):
    eq=copy.deepcopy(source);eq['domain']='integers'
    for v in guards:
        vs=list(range(len(eq['variables']),len(eq['variables'])+3))
        eq['variables'] += [{'name':'guard.'+str(v)+'.'+s,'kind':'guard'} for s in 'abc']
        if monic:
            terms={(v,):1,(vs[2],):-1,**{(w,w):-1 for w in vs}}
        else:
            terms={():1,(v,):8,**{(w,w):-1 for w in vs}}
        eq['residuals'].append({'label':'nonnegative.'+str(v),'terms':pack(terms)})
    return eq

