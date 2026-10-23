#!/usr/bin/env python3
"""Calibrated two-block/positivity-first compiler. Standard library only.

Adapted from package59 with compact tuple and optimized targets. The source
evaluation is reconstructed from its 60-gate arithmetic JSON specification.
"""
from pathlib import Path
from collections import Counter, defaultdict
from functools import lru_cache
import ast, json, hashlib
from circuit import DAG

ROOT=Path(__file__).resolve().parent
PORTS=('beta','K0','MC','MF')
BITS=(590069,592884,590069,590070)
VARIABLES=['b','g','h','s','w','C','i','j','n']

def padd(a,b,sign=1):
    z=a.copy()
    for e,v in b.items():z[e]=z.get(e,0)+sign*v
    return {e:v for e,v in z.items() if v}

def pmul(a,b):
    z={}
    for e,v in a.items():
        for f,w in b.items():
            g=tuple(x+y for x,y in zip(e,f));z[g]=z.get(g,0)+v*w
    return {e:v for e,v in z.items() if v}

def parse_recipe(expr):
    """Parse only integer polynomial syntax in the four named ports."""
    def visit(t):
        if isinstance(t,ast.Constant) and type(t.value) is int:return {(0,)*4:t.value} if t.value else {}
        if isinstance(t,ast.Name) and t.id in PORTS:return {tuple(int(i==PORTS.index(t.id)) for i in range(4)):1}
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {e:-v for e,v in visit(t.operand).items()}
        if isinstance(t,ast.BinOp):
            a=visit(t.left)
            if isinstance(t.op,ast.Pow):
                if not isinstance(t.right,ast.Constant) or type(t.right.value) is not int or t.right.value<0:raise ValueError('bad fixed exponent')
                z={(0,)*4:1}
                for _ in range(t.right.value):z=pmul(z,a)
                return z
            b=visit(t.right)
            if isinstance(t.op,ast.Add):return padd(a,b)
            if isinstance(t.op,ast.Sub):return padd(a,b,-1)
            if isinstance(t.op,ast.Mult):return pmul(a,b)
        raise ValueError('unsupported coefficient recipe')
    return visit(ast.parse(str(expr),mode='eval').body)

def recipe_list(poly):return [{'powers':list(e),'coefficient':v} for e,v in sorted(poly.items())]

def build(layout,positive=True,certificate=False,encoding='shared',power_method='binary'):
    split=layout=='split_116'
    path=ROOT/'data'/('split_code.json' if split else 'CERTIFICATE_'+layout+'.json');data=json.loads(path.read_text())
    rawpath=ROOT/'data'/('parent_source.json' if split else 'source_system60.json');raw=json.loads(rawpath.read_text())
    if split:
        kernels=json.loads((ROOT/'data/split_kernels.json').read_text())
        data.update(source_sha256=kernels['source_sha256'],Kcode=data['convolution_height'],Dmax=max(data['kernel_degrees']))
    if hashlib.sha256(rawpath.read_bytes()).hexdigest()!=data['source_sha256']:raise ValueError('source hash')
    bits=BITS
    d=DAG();c=d.const;add=d.plus;mul=d.times;sub=d.minus;pw=d.power;save=d.save
    v={n:d.var(n) for n in VARIABLES}
    for n in (('j',) if positive else ('b','g','h','s','w','C','i','n')):v[n]=sub(v[n],c(1)) if positive else add(v[n],c(1))
    recipes={};coefs={};bound=0
    def coefficient(expr):
        nonlocal bound
        poly=expr if isinstance(expr,dict) else parse_recipe(expr);rec=recipe_list(poly);key=json.dumps(rec,sort_keys=True)
        if key not in recipes:recipes[key]=(f'c{len(recipes):03}',rec)
        name=recipes[key][0]
        if name not in coefs:
            coefs[name]=c(0) if not rec else c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.fixed(name)
        bnd=sum(abs(t['coefficient'])*(1<<sum(e*b for e,b in zip(t['powers'],bits))) for t in rec)
        bound=max(bound,bnd)
        return coefs[name]
    if split:rowterms=[(r,[(dict(t,encoding_exponent=t['exponent']),coefficient({tuple(x['powers']):x['coefficient'] for x in t['coefficient']})) for t in r['terms']]) for r in kernels['kernels']]
    else:rowterms=[(r,[(t,coefficient(t['weighted_coefficient'])) for t in r['terms']]) for r in data['rows']]
    mexp=(bound-1).bit_length();kap=mexp+12
    b=save('b',v['b']);B=save('B',mul(d.fixed('base_scale'),pw(b,2)))
    @lru_cache(None)
    def chunk(pos,digit):
        if not digit:return c(1)
        if digit==1:return B if pos==0 else pw(chunk(pos-1,1),16)
        return mul(chunk(pos,digit-1),chunk(pos,1))
    knownpowers={0:c(1),1:B}
    @lru_cache(None)
    def bp(e):
        if e<0:raise ValueError('negative encoding exponent')
        if power_method=='binary':return pw(B,e)
        if power_method=='additive':
            if e in knownpowers:return knownpowers[e]
            pairs=[(i,e-i) for i in knownpowers if i>0 and e-i>0 and e-i in knownpowers]
            if pairs:
                i,j=min(pairs,key=lambda ij:(abs(ij[0]-ij[1]),ij[0]));out=mul(knownpowers[i],knownpowers[j])
            else:
                h=bp(e//2);out=mul(h,h)
                if e%2:out=mul(out,B)
            knownpowers[e]=out
            return out
        out=[];pos=0
        while e:
            if e%16:out.append(chunk(pos,e%16))
            e//=16;pos+=1
        return mul(*out)
    def sparse(pairs):
        merged=defaultdict(list)
        for e,a in pairs:merged[e].append(a)
        terms=sorted((e,add(*aa)) for e,aa in merged.items())
        e,r=terms.pop()
        while terms:
            e2,a=terms.pop();r=add(mul(r,bp(e-e2)),a);e=e2
        return mul(r,bp(e))
    @lru_cache(None)
    def geom_stride(stride,count):
        if count==0:return c(0)
        if count==1:return c(1)
        half=count//2;r=mul(geom_stride(stride,half),add(c(1),bp(stride*half)))
        return add(r,bp(stride*(count-1))) if count%2 else r
    W=max(data['weights']);pad=data.get('padding_exponent',0);Kcode=data['Kcode'];Ecode=Kcode+W+2
    if split:
        kn=[]
        for row,terms in rowterms:
            pairs=[(t['encoding_exponent'],node) for t,node in terms]
            kn.append(save('D'+str(row['degree']),add(*(mul(node,bp(e)) for e,node in pairs)) if encoding=='sum' else sparse(pairs)))
        DC=None
    elif encoding=='shared':
        u0=bp(W-pad);coords=[bp(W-w) for w in data['weights']]
        env={n:(add(z,u0),1) for n,z in zip(raw['variables'],coords)}
        env.update({n:(coefficient(n),0) for n in raw['constants']})
        def get(x):return (c(x),0) if type(x) is int else env[x]
        def align(z,t):return mul(z[0],pw(u0,t-z[1]))
        for name,op,a,z in raw['source']:
            a,z=get(a),get(z)
            if op=='*':env[name]=(mul(a[0],z[0]),a[1]+z[1])
            else:
                deg=max(a[1],z[1]);env[name]=((add if op=='+' else sub)(align(a,deg),align(z,deg)),deg)
        vals={j:sub(align(get(a),2),align(get(z),2)) for j,(a,z) in enumerate(raw['comparisons'],1)}
        blocks=[]
        for row,terms in rowterms:
            correction=[]
            for t,node in terms:
                aa=t['alpha']
                if sum(aa)==0 or 2 in aa:
                    coord=u0 if sum(aa)==0 else coords[aa.index(2)]
                    correction.append(mul(coefficient(t['coefficient']),pw(coord,2)))
            off=row['target_exponent']-2*W
            if off<0:raise ValueError('shared source requires nonnegative homogeneous shift')
            blocks.append((off,add(vals[row['original_row_one_based']],*correction)))
        DC=sparse(blocks)
    elif encoding=='rows':
        blocks=[]
        for row,terms in rowterms:
            off=min(t['encoding_exponent'] for t,node in terms)
            blocks.append(mul(bp(off),sparse([(t['encoding_exponent']-off,node) for t,node in terms])))
        DC=add(*blocks)
    elif encoding=='sum':DC=add(*(mul(node,bp(t['encoding_exponent'])) for row,terms in rowterms for t,node in terms))
    elif encoding=='horner':DC=sparse([(t['encoding_exponent'],node) for row,terms in rowterms for t,node in terms])
    else:raise ValueError('encoding')
    if not split:DC=save('Dcode',DC)
    ell=save('ell',add(*(bp(w) for w in data['weights'])))
    targets=save('targets',sparse([(q,c(1)) for q in data['targets']]) if split else mul(bp(data['target_spacing']),geom_stride(data['target_spacing'],len(rowterms))) if data.get('target_spacing') else sparse([(r['target_exponent'],c(1)) for r,ts in rowterms]))
    N0=save('N0',bp(W+1));mask=save('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
    Tc=save('Tcode',add(mask,mul(sub(B,c(2)),targets,N0)))
    if split:
        Us=save('Usource',add(ell,v['g']));Gs=save('Gsource',add(mul(add(mul(kn[2],Us),kn[1]),Us),kn[0]))
        Jc=save('Jcode',add(mul(c(2),Gs),targets))
    else:Jc=save('Jcode',add(mul(c(2),pw(add(bp(pad),v['g']),2),DC),targets))
    Sc=save('Scode',add(v['g'],mul(Jc,N0)))
    Hpop=Ecode+W+23;delta=(Hpop-15)%2;lp=(22-Hpop*kap)%2
    L=save('L',mul(c(1<<lp),b,bp(Ecode)))
    nexp=(Hpop-15-delta)//2;cexp=((15+delta)*kap+lp-22)//2
    N=save('N',mul(d.fixed('threshold_scale'),pw(b,delta),bp(nexp)))
    R=save('R',sub(sub(mul(L,add(Sc,Tc,c(1))),Sc),c(1)))
    capbase=save('capbase',mul(b,bp(W)));cap=save('Gcap',mul(c(32),capbase))
    U=save('U',mul(pw(N,2),v['w']));Y=save('Y',mul(pw(N,2),v['s']));M=save('M',mul(R,Y))
    P=save('P',mul(c(2),pw(M,2),U));K=save('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
    A=save('A',mul(M,add(U,c(1))));B1=save('B1',add(mul(c(2),R),c(1)));W1=save('W1',mul(b,v['w']))
    C=save('C',v['C'])
    J=save('J',sub(mul(c(4),A),c(5)));Q=save('Q',add(mul(W1,sub(mul(c(3),C),mul(c(2),W1))),c(2)))
    am1=sub(pw(A,2),c(1));D=save('D',add(mul(am1,pw(C,2)),c(1)))
    k=save('k',mul(v['i'],J,C));E=save('E',mul(k,D,C));F=save('F',add(mul(am1,pw(E,2)),c(1)))
    G=save('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))))
    H=save('H',add(C,mul(F,add(B1,mul(v['j'],C)))))
    GH=save('GH',mul(G,H));I=save('I',add(sub(pw(GH,2),pw(H,2)),c(1)))
    V0=save('V0',mul(P,K));a0=save('a0',add(sub(pw(V0,2),pw(K,2)),c(1)));a1=save('a1',mul(D,F,I))
    margin=save('margin',sub(mul(pw(K,2),sub(mul(c(4),capbase),v['g'])),mul(c(16),capbase,pw(sub(C,mul(K,Y)),2))))
    Tp=save('Tpair',mul(k,sub(sub(mul(c(8),pw(D,2)),mul(c(4),D)),c(1))))
    V1=save('V1',mul(Tp,GH));Om=save('Omega',mul(J,margin));E0=save('E0',add(mul(J,add(v['n'],pw(W1,2))),Q));shift=add(V0,V1)
    theta=save('Theta',sub(E0,mul(Om,shift)))
    if certificate:
        dferr=save('dferror',sub(mul(add(mul(c(8),D),c(1)),pw(k,2)),mul(c(64),D)))
        delt=save('Delta1',add(mul(dferr,pw(GH,2)),mul(c(64),D,F,sub(pw(H,2),c(1)))))
        inner=save('inner',add(sub(pw(E0,2),mul(c(2),E0,Om,shift)),mul(pw(Om,2),add(sub(pw(K,2),c(1)),delt,mul(c(2),V0,V1)))))
    else:inner=save('inner',sub(pw(theta,2),mul(pw(Om,2),add(a0,mul(c(64),a1)))))
    out=save('F9',sub(pw(inner,2),mul(c(256),pw(Om,4),a0,a1)))
    nodes,out,names=d.prune(out);counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return {'schema':'compact-shared-power-nine-v1','free_C':True,'leading_block_removed':True,'quotient_shift':'(b*w)^2','variables':VARIABLES,'domain':'positive integers' if positive else 'nonnegative integers','layout':layout,'encoding':encoding,'power_method':power_method,'degree_certificate_form':certificate,'margin_normalization_divisor':8,'nodes':nodes,'output':out,'named_nodes':names,'operation_counts':counts,'total_operations':sum(counts.values()),'source_sha256':data['source_sha256'],'layout_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'W':W,'padding_exponent':pad,'Dmax':data['Dmax'],'Kcode':Kcode,'Ecode':Ecode,'Hpop':Hpop,'block_scale_power_of_two':lp,'threshold_b_power':delta,'threshold_B_power':nexp,'threshold_scale_exponent':cexp,'base_scale_exponent':kap,'coefficient_bound_exponent':mexp,'port_bit_lengths':bits,'coherent_tuple':'compact44' if split else 'native52','coefficient_recipes':[{'name':name,'terms':rec} for name,rec in recipes.values()]}

def degree_certificate(body):
    """Exact diagonal leading forms in formal positive constants a,c."""
    rows=[];unresolved=[]
    for idx,n in enumerate(body['nodes']):
        k=n['kind']
        if k=='variable':r=(1,{(0,0):1})
        elif k=='literal':r=(0,{(0,0):n['value']})
        elif k=='fixed':r=(0,{(1,0):1} if n['name']=='base_scale' else {(0,1):1} if n['name']=='threshold_scale' else None)
        else:
            da,ca=rows[n['left']];db,cb=rows[n['right']]
            if k=='mul':r=(da+db,None if ca is None or cb is None else pmul(ca,cb))
            elif da>db:r=(da,ca)
            elif db>da:r=(db,None if cb is None else {e:(1 if k=='add' else -1)*v for e,v in cb.items()})
            elif ca is None or cb is None:r=(da,None)
            else:
                cs=padd(ca,cb,1 if k=='add' else -1)
                if not cs and da>0:unresolved.append(idx)
                r=(da,cs)
        rows.append(r)
    deg,head=rows[body['output']]
    if unresolved or not head or any(v<=0 for v in head.values()):raise ValueError('unresolved exact degree')
    def enc(poly):return None if poly is None else [{'base_scale_power':e[0],'threshold_scale_power':e[1],'scalar_odd_part':str(v//(abs(v)&-abs(v))) if v else '0','scalar_power_of_two':(abs(v)&-abs(v)).bit_length()-1 if v else 0} for e,v in poly.items()]
    return {'exact_degree':deg,'diagonal_leading_coefficient':enc(head),'named_degrees':{k:rows[i][0] for k,i in body['named_nodes'].items()},'named_leaders':{k:enc(rows[i][1]) for k,i in body['named_nodes'].items()},'unresolved_positive_degree_cancellations':unresolved}

def main():
    (ROOT/'generated').mkdir(exist_ok=True);ledger={}
    for layout in ['split_116']:
        if layout=='split_116':encodings=['horner','sum']
        else:
            data=json.loads((ROOT/'data'/('CERTIFICATE_'+layout+'.json')).read_text())
            encodings=['horner','sum','rows']+(['shared'] if min(r['target_exponent'] for r in data['rows'])>=2*max(data['weights']) else [])
        candidates=[build(layout,True,False,e,p) for e in encodings for p in ['binary','window16','additive']]
        best=min(candidates,key=lambda b:b['total_operations']);degree=None
        for positive in [True,False]:
            for cert in [False,True]:
                obj=build(layout,positive,cert,'horner' if cert else best['encoding'],'binary' if cert else best['power_method'])
                label=layout+'_'+('positive' if positive else 'natural')+('_certificate' if cert else '')
                if cert:
                    degree=degree_certificate(obj);(ROOT/f'generated/{label}_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
                (ROOT/f'generated/{label}.json').write_text(json.dumps(obj,separators=(',',':'))+'\n')
        ledger[layout]={'exact_degree':degree['exact_degree'],'positive_operations':best['total_operations'],'positive_operation_counts':best['operation_counts'],'encoding':best['encoding'],'power_method':best['power_method'],'encoding_costs':{x['encoding']+'/'+x['power_method']:x['total_operations'] for x in candidates},'W':best['W'],'Ecode':best['Ecode'],'base_scale_exponent':best['base_scale_exponent'],'threshold_scale_exponent':best['threshold_scale_exponent'],'threshold_B_power':best['threshold_B_power']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))

if __name__=='__main__':main()

