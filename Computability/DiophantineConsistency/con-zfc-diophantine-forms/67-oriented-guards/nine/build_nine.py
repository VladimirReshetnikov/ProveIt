#!/usr/bin/env python3
"""Authored calibrated two-block/positivity-first compiler. Standard library only.

Imported files are mathematical data, never executable programs. The source
evaluation is reconstructed from its 60-gate arithmetic JSON specification.
"""
from pathlib import Path
from collections import Counter, defaultdict
from functools import lru_cache
import ast, json, hashlib, math
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

def build(layout,positive=True,certificate=False,encoding='shared',power_method='binary',order=4):
    scale=[128,64,8,4,1][max(0,order)]; lam=8 if order==-1 else 2048//scale
    split=layout.startswith('split_')
    path=ROOT/'data'/(('split_code.json' if layout=='split_116' else 'split108_code.json') if split else 'CERTIFICATE_'+layout+'.json');data=json.loads(path.read_text())
    rawpath=ROOT/'data'/('parent_source.json' if split else 'source_system60.json');raw=json.loads(rawpath.read_text())
    if split:
        kernels=json.loads((ROOT/('data/split_kernels.json' if layout=='split_116' else 'data/split108_kernels.json')).read_text())
        data.update(source_sha256=kernels['source_sha256'],Kcode=data['convolution_height'],Dmax=max(data['kernel_degrees']))
    if hashlib.sha256(rawpath.read_bytes()).hexdigest()!=data['source_sha256']:raise ValueError('source hash')
    bits=(1064921,1070004,1064921,1064922) if split else BITS
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
    mexp=bound.bit_length();kap=mexp+12
    if layout=='split_108':kap+=kap%2
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
    V0=save('V0',mul(P,K));a0=save('a0',add(sub(pw(V0,2),pw(K,2)),c(1)));a1=save('a1',mul(c(lam**2),D,F,I))
    margin=save('margin',sub(mul(pw(K,2),sub(mul(c(4),capbase),v['g'])),mul(c(16),capbase,pw(sub(C,mul(K,Y)),2))))
    t0=save('t0',mul(v['i'],J,C));e2=pw(t0,2)
    Lm=save('major_L',sub(add(mul(C,D),c(1)),A))
    Ns=save('major_Nstar',add(mul(c(2),G),Lm))
    Dm1=sub(D,c(1));D2=pw(D,2)
    N2m=save('major_N2',mul(c(2),e2,Dm1,Lm))
    N1m=save('major_N1',add(mul(D,N2m),mul(c(3),C)))
    N3m=save('major_N3',mul(c(2),e2,sub(Lm,C)))
    N4m=save('major_N4',mul(c(2),e2,C))
    corr=save('major_correction',add(mul(c(256),v['i'],add(e2,c(2))),c(2048)) if order==4 else add(mul(c(512//scale),v['i']),c(lam)) if order else c(lam))
    tp=sub(sub(mul(c(1024//scale),D2),mul(c(512//scale),D)),c(128//scale))
    Nsvec=[N1m,N2m,N3m,N4m]; coeffs=[64,40,28,21]
    poly=mul(tp,Ns)
    for co,node in zip(coeffs[:order],Nsvec[:order]):poly=sub(poly,mul(c(co//scale),node))
    Tm=save('major_T',add(mul(t0,poly),corr))
    if order==-1:Tm=save('major_T',mul(t0,sub(sub(mul(c(8),D2),mul(c(4),D)),c(1)),G))
    V1=save('V1',mul(Tm,H))
    Om=save('Omega',mul(J,margin))
    E0=save('E0',add(mul(J,add(v['n'],pw(W1,2))),Q))
    root_bound=save('root_bound',add(V0,V1))
    Th=save('Theta',sub(E0,mul(Om,root_bound)))
    if certificate:
        D3,D4,D8,D16=(pw(D,z) for z in (3,4,8,16))
        r1=save('major_r1',sub(c(3),A))
        r2=save('major_r2',add(mul(c(3),C,D),r1))
        r3=save('major_r3',add(mul(c(2),e2,sub(A,c(1)),D2),r2))
        r4=save('major_r4',add(mul(c(2),e2,sub(sub(c(1),A),C),D3),r3))
        tc={6:1024//scale,5:-512//scale,4:-128//scale}
        for j,co in enumerate(coeffs[:order],1):tc[4-j]=-co//scale
        tn=save('major_tnum',add(*(mul(c(vv),pw(D,ee)) for ee,vv in sorted(tc.items()))))
        dc={}
        for e1,c1 in tc.items():
            for e2p,c2 in tc.items():dc[e1+e2p]=dc.get(e1+e2p,0)+c1*c2
        dc[12]=dc.get(12,0)-(1024//scale)**2;dc[11]=dc.get(11,0)+(1024//scale)**2
        dn=save('major_dnum',add(*(mul(c(vv),pw(D,ee)) for ee,vv in sorted(dc.items()) if vv)))
        rs=[r1,r2,r3,r4]
        rn=save('major_Rnum',add(mul(t0,add(*(mul(c(co//scale),rr,pw(D,3-j)) for j,(co,rr) in enumerate(zip(coeffs[:order],rs[:order]))))),mul(corr,D4)))
        Xm=save('major_X',mul(e2,D3,Dm1))
        deltaT8=save('deltaT8',add(mul(e2,dn,pw(Ns,2)),mul(c((1024//scale)**2),D8,sub(mul(Xm,pw(Lm,2)),mul(c(4),D,G,add(mul(C,D),c(1))))),mul(c(2),t0,tn,Ns,rn),pw(rn,2)))
        delta1_8=save('delta1_D8',add(mul(pw(H,2),deltaT8),mul(c(lam**2),D,F,D8,sub(pw(H,2),c(1)))))
        if order==-1:delta1_8=save('delta1_D8',mul(D8,add(mul(sub(mul(add(mul(c(8),D),c(1)),pw(t0,2)),mul(c(64),D)),pw(GH,2)),mul(c(64),D,F,sub(pw(H,2),c(1))))))
        delta0=save('delta0',sub(pw(K,2),c(1)))
        B8=save('B_D8',add(mul(D8,sub(pw(E0,2),mul(c(2),E0,Om,root_bound))),mul(pw(Om,2),add(mul(D8,delta0),delta1_8))))
        # Exact two-defect expansion of D^16 times the two-root norm.
        out=save('F9_D16',add(pw(B8,2),mul(c(4),pw(Om,2),V0,V1,D8,B8),mul(c(4),pw(Om,4),add(mul(D16,delta0,pw(V1,2)),mul(D8,a0,delta1_8)))))
    else:
        inner=save('inner',sub(pw(Th,2),mul(pw(Om,2),add(a0,a1))))
        out=save('F9',sub(pw(inner,2),mul(c(4),pw(Om,4),a0,a1)))
    nodes,out,names=d.prune(out);counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return {'schema':'free-carrier-higher-majorant-nine-v1','majorant_order':order,'radical_scale':lam,'free_C':True,'leading_block_removed':True,'quotient_shift':'(b*w)^2','variables':VARIABLES,'domain':'positive integers' if positive else 'nonnegative integers','layout':layout,'encoding':encoding,'power_method':power_method,'degree_certificate_form':certificate,'margin_normalization_divisor':8,'nodes':nodes,'output':out,'named_nodes':names,'operation_counts':counts,'total_operations':sum(counts.values()),'source_sha256':data['source_sha256'],'layout_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'W':W,'padding_exponent':pad,'Dmax':data['Dmax'],'Kcode':Kcode,'Ecode':Ecode,'Hpop':Hpop,'block_scale_power_of_two':lp,'threshold_b_power':delta,'threshold_B_power':nexp,'threshold_scale_exponent':cexp,'base_scale_exponent':kap,'coefficient_bound_exponent':mexp,'port_bit_lengths':bits,'coherent_tuple':'old31' if split else 'native52','coefficient_recipes':[{'name':name,'terms':rec} for name,rec in recipes.values()]}

def degree_certificate(body):
    """Exact diagonal leading forms in formal positive constants a,c."""
    rows=[];unresolved=[]
    fixed_heads={r['name']:{(0,0)+tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in body['coefficient_recipes']}
    for idx,n in enumerate(body['nodes']):
        k=n['kind']
        if k=='variable':r=(1,{(0,)*6:1})
        elif k=='literal':r=(0,{(0,)*6:n['value']})
        elif k=='fixed':r=(0,{(1,0,0,0,0,0):1} if n['name']=='base_scale' else {(0,1,0,0,0,0):1} if n['name']=='threshold_scale' else fixed_heads[n['name']])
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
    def enc(poly):return None if poly is None else [{'base_scale_power':e[0],'threshold_scale_power':e[1],'port_powers':list(e[2:]),'scalar_odd_part':str(v//(abs(v)&-abs(v))) if v else '0','scalar_power_of_two':(abs(v)&-abs(v)).bit_length()-1 if v else 0} for e,v in poly.items()]
    return {'exact_degree':deg,'diagonal_leading_coefficient':enc(head),'named_degrees':{k:rows[i][0] for k,i in body['named_nodes'].items()},'named_leaders':{k:enc(rows[i][1]) for k,i in body['named_nodes'].items()},'unresolved_positive_degree_cancellations':unresolved}

def main():
    (ROOT/'generated').mkdir(exist_ok=True);ledger={}
    for order in range(-1,5):
        layout='split_108' if (ROOT/'data/split108_code.json').exists() else 'split_116'
        candidates=[build(layout,True,False,e,p,order) for e in ['horner','sum'] for p in ['binary','window16','additive']]
        best=min(candidates,key=lambda b:b['total_operations']);degree=None
        for positive in [True,False]:
            for cert in [False,True]:
                obj=build(layout,positive,cert,'horner' if cert else best['encoding'],'binary' if cert else best['power_method'],order)
                label=layout+'_order'+str(order)+'_'+('positive' if positive else 'natural')+('_certificate' if cert else '')
                if cert:
                    degree=degree_certificate(obj);degree['certificate_degree']=degree['exact_degree'];degree['multiplier_degree']=16*degree['named_degrees']['D'];degree['exact_degree']-=degree['multiplier_degree'];degree['certificate_multiplier']='D^16'
                    degree['certificate_diagonal_leading_coefficient']=degree['diagonal_leading_coefficient']
                    hd=degree['named_leaders']['D']; hp=degree['diagonal_leading_coefficient']
                    if len(hd)!=1 or len(hp)!=1 or hd[0]['scalar_odd_part']!='1':raise ValueError('head division shape')
                    degree['diagonal_leading_coefficient']=[dict(hp[0],base_scale_power=hp[0]['base_scale_power']-16*hd[0]['base_scale_power'],threshold_scale_power=hp[0]['threshold_scale_power']-16*hd[0]['threshold_scale_power'],scalar_power_of_two=hp[0]['scalar_power_of_two']-16*hd[0]['scalar_power_of_two'],port_powers=[p-16*q for p,q in zip(hp[0]['port_powers'],hd[0]['port_powers'])])]
                    (ROOT/f'generated/{label}_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
                (ROOT/f'generated/{label}.json').write_text(json.dumps(obj,separators=(',',':'))+'\n')
        ledger['order'+str(order)]={'exact_degree':degree['exact_degree'],'positive_operations':best['total_operations'],'positive_operation_counts':best['operation_counts'],'encoding':best['encoding'],'power_method':best['power_method'],'W':best['W'],'Ecode':best['Ecode'],'base_scale_exponent':best['base_scale_exponent'],'threshold_scale_exponent':best['threshold_scale_exponent'],'threshold_B_power':best['threshold_B_power']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))

if __name__=='__main__':main()
