#!/usr/bin/env python3
"""Builder-free verification of sign certificates, projection, and coefficients.

The checker uses only exact integer polynomial arithmetic. Its mathematical
rules are proved in PROOF.md. It imports no compiler or optimizer.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import argparse, copy, json

def need(ok, message):
    if not ok:
        raise ValueError(message)

def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(',', ':'))+'\n').encode()

def polynomial(terms):
    d=defaultdict(int)
    for c,m in terms:
        need(type(c) is int and all(type(v) is int and v>=0 for v in m),'integer term')
        d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}

def terms(p):
    return [[c,list(m)] for m,c in sorted(p.items())]

def add(a,b,k=1):
    p=dict(a)
    for m,c in b.items():p[m]=p.get(m,0)+k*c
    return {m:c for m,c in p.items() if c}

def mul(a,b):
    p=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():p[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in p.items() if c}

def dep(p):
    return {v for m in p for v,k in Counter(m).items() if k%2}

def degree(p):
    return max(map(len,p),default=0)

def substitute(p,v,f):
    out={}
    for m,c in p.items():
        q={():c}
        for w in m:q=mul(q,f if w==v else {(w,):1})
        out=add(out,q)
    return out

def plus_or_minus(a,b):
    return a==b or a=={m:-c for m,c in b.items()}

class LiteralRows:
    def __init__(self,parent):
        self.parent=parent
        self.rows=[polynomial(r['terms']) for r in parent['residuals']]
        self.names={v['name']:i for i,v in enumerate(parent['variables'])}
        self.defs={}
        for ri,r in enumerate(parent['residuals']):
            if r['label'] not in ('addition','multiplication'):continue
            p=self.rows[ri]
            for m,c in p.items():
                if len(m)!=1 or c!=1:continue
                v=m[0]
                if parent['variables'][v]['kind']!='gate':continue
                f={n:-d for n,d in p.items() if n!=(v,)}
                if all(d>0 and all(w<v for w in n) for n,d in f.items()):
                    need(v not in self.defs,'unique gate definition')
                    self.defs[v]=(ri,f)

    @lru_cache(None)
    def atom(self,v,mode='all',stop=frozenset()):
        if v not in self.defs or v in stop:return {(v,):1}
        f=self.defs[v][1]
        if mode=='affine' and degree(f)>1:return {(v,):1}
        return self.unfold(f,mode,stop)

    def unfold(self,p,mode='all',stop=frozenset()):
        out={}
        for m,c in p.items():
            q={():c}
            for v in m:q=mul(q,self.atom(v,mode,stop))
            out=add(out,q)
            need(len(out)<=25000,'unexpected expansion size')
        return out

def check_rule(lit,r,registered_pairs):
    rows=lit.rows
    kind=r['kind'];outputs=r['out']
    need(outputs and len(set(outputs))==len(outputs),'nonempty distinct outputs')
    if kind=='nonnegative_polynomial':
        need(len(outputs)==1,'single polynomial output')
        x=outputs[0];f=polynomial(r['polynomial'])
        need(all(c>0 for c in f.values()),'nonnegative polynomial coefficients')
        need(all(x not in m for m in f),'no self definition')
        need(plus_or_minus(rows[r['row']],add({(x,):1},f,-1)),'literal sign-defining row')
        dependencies=dep(f)
    elif kind=='centered_pair':
        need(r in registered_pairs and len(outputs)==2,'registered pair guard')
        x,y=outputs;f=polynomial(r['sum_polynomial'])
        need(all(c>0 for m,c in f.items() if m) and f.get((),0)>=-1,'pair sum lower bound')
        need(all(x not in m and y not in m for m in f),'pair does not define itself')
        need(plus_or_minus(rows[r['row']],add({(x,):1,(y,):1},f,-1)),'literal pair-sum row')
        dependencies=dep(f)
    elif kind=='positive_shifted_product':
        need(len(outputs)==1,'single quotient output')
        x=outputs[0];A=polynomial(r['A']);B=polynomial(r['B'])
        need(all(c>0 for c in A.values()) and all(c>0 for c in B.values()) and B.get((),0)>=1,'positive shifted-product polynomials')
        need(all(x not in m for m in A) and all(x not in m for m in B),'quotient independence')
        if r['subkind']=='binomial_high':
            ri,rd,rb=r['rows']
            tag=lit.parent['variables'][x]['name'].split('.')[0]
            need(lit.parent['variables'][x]['name']==tag+'.high','binomial high identity')
            rem,slack=[lit.names[tag+'.'+s] for s in ('remainder','rslack')]
            D=add(lit.unfold(rows[rd]),{(rem,):1,(slack,):1,():1})
            combination=add(add({m:-c for m,c in lit.unfold(rows[ri]).items()},
                                mul(D,lit.unfold(rows[rb]))),lit.unfold(rows[rd]))
        elif r['subkind']=='division_quotient':
            ri,rb=r['rows']
            combination=add({m:-c for m,c in lit.unfold(rows[ri]).items()},lit.unfold(rows[rb]))
        else:raise ValueError('unknown quotient lemma')
        need(add(mul(A,{(x,):1,():1}),B,-1)==combination,'exact shifted-product consequence')
        dependencies=dep(A)|dep(B)
    elif kind=='frame_root_orientation':
        need(len(outputs)==1,'one oriented root')
        X=outputs[0]
        A,W,z,Y,m,T,h=[r[k] for k in ('A_index','W_index','z_index','Y_index','m_index','T_index','quotient_index')]
        rn,rf,rt,rp=r['rows'];n=polynomial(r['base']);f=polynomial(r['frame_rhs'])
        margin=polynomial(r['frame_margin']);stop=frozenset(r['unfold_allowed'])
        need(all(c>0 for c in n.values()) and all(c>0 for c in f.values()) and f.get((),0)>=2,'nonnegative frame expressions')
        need(add(f,n,-1)==margin and all(c>0 for c in margin.values()),'frame dominates base')
        need(W not in {v for mm in f for v in mm},'frame RHS independent of W')
        norm=add({(A,A):1,():-1},mul({(W,W,W,W):1,(W,W,W):2},mul({(z,):1,():1},{(z,):1,():1})),-1)
        need(lit.unfold(rows[rn])==norm,'literal dominating Pell norm')
        need(lit.unfold(rows[rf],'affine')==add({(W,):1},f,-1),'literal frame sum')
        base_eq=add(add(mul({(A,):2},n),{(T,):1,():1},-1),mul(n,n),-1)
        need(lit.unfold(rows[rt],stop=stop)==base_eq,'literal base-modulus equation')
        power_eq=add(add(add({(X,):1},mul({(Y,):1},n)),
                         {tuple(sorted((Y,A))):1,(m,):1},-1),{tuple(sorted((T,h))):1},-1)
        need(lit.unfold(rows[rp],stop=stop)==power_eq,'literal oriented-root equation')
        dependencies=dep(f)|dep(n)|{A,z,Y,m,T,h}
    else:raise ValueError('unknown sign rule '+kind)
    need(dependencies==set(r['dependencies']),'exact dependency census')
    need(not set(outputs)&dependencies,'sign rule cannot depend on its new output')
    return dependencies

def check_signs(parent,guarded,cert):
    need(parent['domain']=='nonnegative integers' and guarded['domain']=='unrestricted integers','domain boundary')
    nv=len(parent['variables']);seeds=cert['seeds'];pairs=cert['pairs']
    need(seeds==sorted(set(seeds)) and all(0<=v<nv for v in seeds),'distinct seed guards')
    variables=copy.deepcopy(parent['variables']);rows=copy.deepcopy(parent['residuals'])
    for v in seeds:
        a,b,c=range(len(variables),len(variables)+3)
        variables.extend({'name':f'sign.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c'))
        rows.append({'label':f'nonnegative.{v}','terms':terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    for p in pairs:
        x,y=p['out'];need(0<=x<nv and 0<=y<nv and x!=y,'pair indices')
        a,b,c=range(len(variables),len(variables)+3)
        variables.extend({'name':f'pair.{x}.{y}.{s}','kind':'integer_guard'} for s in ('a','b','c'))
        rows.append({'label':f'nonnegative_pair.{x}.{y}',
                     'terms':terms({tuple(sorted((x,y))):2,(x,):1,(y,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    need(guarded['variables']==variables and guarded['residuals']==rows,'exact guard coverage and original prefix')
    lit=LiteralRows(parent);known=set(seeds);census=Counter()
    for r in cert['proof']:
        dd=check_rule(lit,r,pairs)
        need(dd<=known,'sign proof uses an unproved sign')
        need(all(0<=v<nv for v in r['out']),'sign output in parent')
        known.update(r['out']);census[r['kind']]+=1
    need(known==set(range(nv)),'complete original sign coverage')
    return {'single_guards':len(seeds),'pair_guards':len(pairs),'proved_coordinates':len(known),
            'sign_rules':dict(census),'guarded_variables':len(variables),'guarded_rows':len(rows)}

def check_projection(source,target,cert):
    need(sha256(canonical(source)).hexdigest()==cert['input_sha256'],'projection source hash')
    need(sha256(canonical(target)).hexdigest()==cert['output_sha256'],'projection target hash')
    rows={i:polynomial(r['terms']) for i,r in enumerate(source['residuals'])};dead=set()
    for s in cert['steps']:
        ri,v=s['row_id'],s['variable'];f=polynomial(s['restoration'])
        need(ri in rows and v not in dead,'live projection pivot')
        need(degree(f)<=2 and not any(v in m for m in f),'integral independent restoration')
        need(not any(w in dead for m in f for w in m),'restoration uses live coordinates')
        need(plus_or_minus(rows[ri],add({(v,):1},f,-1)),'exact monic pivot identity')
        new={}
        for j,p in rows.items():
            if j==ri:continue
            q=substitute(p,v,f)
            need(degree(q)<=2,'quartic preservation')
            if q:new[j]=q
        rows=new;dead.add(v)
    used=sorted({v for p in rows.values() for m in p for v in m})
    need(used==cert['retained_original_variables'],'projection coordinate map')
    need(sorted(rows)==cert['retained_original_rows'],'projection residual map')
    need(sorted(set(range(len(source['variables'])))-dead-set(used))==cert['unconstrained_removed'],'unconstrained-coordinate proof')
    rename={v:i for i,v in enumerate(used)}
    target_rows=[{'label':source['residuals'][j]['label'],
                  'terms':[[c,[rename[v] for v in m]] for m,c in sorted(p.items())]}
                 for j,p in sorted(rows.items())]
    need(target['residuals']==target_rows,'all final residual coefficients')
    need(target['variables']==[source['variables'][v] for v in used],'all final variable names')
    need(target['domain']=='unrestricted integers','unrestricted final domain')
    return {'restorations':len(dead),'final_variables':len(used),'final_rows':len(rows)}

def check_expansion(eq,expanded):
    p={}
    for row in eq['residuals']:
        q=polynomial(row['terms']);need(degree(q)<=2,'quadratic residual')
        p=add(p,mul(q,q))
    need(expanded['domain']==eq['domain'] and expanded['variables']==len(eq['variables']),'expanded schema/domain')
    need(expanded['terms']==terms(p),'complete expanded polynomial')
    need({v for m in p for v in m}==set(range(len(eq['variables']))),'all variables live')
    metrics={'variables':len(eq['variables']),'quadratic_rows':len(eq['residuals']),
             'degree':degree(p),'monomials':len(p),'height':max(map(abs,p.values()))}
    need(metrics['degree']==4,'attained quartic degree')
    return metrics

def verify(directory,parent,negative_controls=True):
    root=Path(directory)
    load=lambda name:json.loads((root/name).read_text())
    guarded=load('guarded.json');signs=load('sign_certificate.json');target=load('equation.json')
    projection=load('projection.json');expanded=load('polynomial.json')
    receipt={'status':'PASS','signs':check_signs(parent,guarded,signs),
             'projection':check_projection(guarded,target,projection),
             'metrics':check_expansion(target,expanded)}
    if negative_controls:
        rejected=[]
        def reject(name,call):
            try:call()
            except ValueError:rejected.append(name)
            else:raise ValueError('negative control was accepted: '+name)
        damaged=copy.deepcopy(guarded);damaged['residuals'].pop()
        reject('missing_pair_guard',lambda:check_signs(parent,damaged,signs))
        damaged_signs=copy.deepcopy(signs)
        r=next(r for r in damaged_signs['proof'] if r['kind']=='frame_root_orientation')
        r['frame_margin'][0][0]+=1
        reject('false_frame_margin',lambda:check_signs(parent,guarded,damaged_signs))
        damaged_projection=copy.deepcopy(projection);damaged_projection['steps'][0]['restoration'][0][0]+=1
        reject('altered_restoration',lambda:check_projection(guarded,target,damaged_projection))
        damaged_expansion=copy.deepcopy(expanded);damaged_expansion['terms'][0][0]+=1
        reject('altered_coefficient',lambda:check_expansion(target,damaged_expansion))
        receipt['negative_controls_rejected']=rejected
    return receipt

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--equations',type=Path,default=Path(__file__).resolve().parent/'equations')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();parent=json.loads(args.parent.read_text())
    receipt=verify(args.equations,parent)
    if args.receipt:args.receipt.write_bytes(canonical(receipt))
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
