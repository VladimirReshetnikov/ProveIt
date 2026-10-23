#!/usr/bin/env python3
"""Independent finite-data, symbolic, modular and boundary audit.

These checks supplement the universal proof; they do not decide consistency.
No assertions, network, third-party packages, or imported upstream programs.
"""
from pathlib import Path
from collections import defaultdict,Counter
from itertools import combinations_with_replacement,product
import json,math,gzip,hashlib,random,sys
from build_nine import build,degree_certificate,parse_recipe,padd,pmul,ROOT,PORTS
from circuit import evaluate

def require(p,msg):
    if not p:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()

def expand_source(shift=True):
    """Independent expansion in 35 variables, shifting 31 by one."""
    src=json.loads((ROOT/'data/source_system60.json').read_text());dim=35;zero=(0,)*dim
    def unit(i):return tuple(int(i==j) for j in range(dim))
    env={n:({zero:1,unit(i):1} if i<31 and shift else {unit(i):1}) for i,n in enumerate(src['variables']+src['constants'])}
    def get(x):return {zero:x} if type(x) is int else env[x]
    for name,op,a,b in src['source']:
        aa,bb=get(a),get(b)
        env[name]=pmul(aa,bb) if op=='*' else padd(aa,bb,1 if op=='+' else -1)
    rows={}
    for i,(a,b) in enumerate(src['comparisons'],1):
        grouped=defaultdict(dict)
        for e,v in padd(get(a),get(b),-1).items():grouped[e[:31]][e[31:]]=v
        rows[i]=dict(grouped)
    return rows

def audit_layout(data,source):
    ws=data['weights'];pad=data.get('padding_exponent',0);positions=[pad]+ws;targets={r['target_exponent']:r['original_row_one_based'] for r in data['rows']}
    require(len(ws)==31 and len(set(positions))==32,'distinct positions including padding')
    require(len(targets)==22,'22 distinct targets')
    exponents=[];interactions=hits=0;direct={}
    pairs=list(combinations_with_replacement(range(32),2))
    for row in data['rows']:
        rid=row['original_row_one_based'];require(len(row['terms'])==len(source[rid]),'complete residual support')
        for t in row['terms']:
            aa=tuple(t['alpha']);raw=source[rid][aa];weighted={e:v*math.factorial(2-sum(aa))*math.prod(math.factorial(x) for x in aa) for e,v in raw.items()}
            require(parse_recipe(t['coefficient'])==raw,'raw coefficient exact')
            require(parse_recipe(t['weighted_coefficient'])==weighted,'factorial coefficient exact')
            exponent=row['target_exponent']-(2-sum(aa))*pad-sum(x*w for x,w in zip(aa,ws))
            require(exponent==t['encoding_exponent'] and exponent>=0,'encoding exponent')
            exponents.append(exponent)
            for e,v in weighted.items():direct[(exponent,)+e]=direct.get((exponent,)+e,0)+v
            expected=[0]*(2-sum(aa))+[i+1 for i,x in enumerate(aa) for _ in range(x)]
            for i,j in pairs:
                target=exponent+positions[i]+positions[j];actual=target in targets;intended=tuple(expected)==(i,j)
                require(actual==intended and (not actual or targets[target]==rid),'active support isolation')
                hits+=actual;interactions+=1
    require(len(set(exponents))==len(exponents)==136,'distinct 136 encoding positions')
    require(max(exponents)==data['Dmax'],'Dmax')
    require({e[1:]:v for e,v in direct.items() if e[0]==data['Dmax']}=={(0,)*4:2},'positive leading coefficient')
    require(data['Kcode']==data['Dmax']+2*max(ws),'Kcode')
    require(data['target_maximum']==max(targets)<data['Kcode'],'target range')
    return direct,{'interaction_checks':interactions,'intended_hits':hits,'source_records':len(exponents)}

def exact_source_dag(body,name='Dcode'):
    """Expand only Dcode, treating the B register as a fresh indeterminate."""
    target=body['named_nodes'][name];base=body['named_nodes']['B'];needed=set();todo=[target]
    while todo:
        i=todo.pop()
        if i in needed:continue
        needed.add(i)
        if i==base:continue
        node=body['nodes'][i]
        if 'left' in node:todo.extend([node['left'],node['right']])
    rec={r['name']:{(0,)+tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in body['coefficient_recipes']};vals={}
    for i in sorted(needed):
        node=body['nodes'][i];k=node['kind']
        if i==base:z={(1,0,0,0,0):1}
        elif k=='literal':z={(0,)*5:node['value']} if node['value'] else {}
        elif k=='fixed':z=rec[node['name']]
        else:z=pmul(vals[node['left']],vals[node['right']]) if k=='mul' else padd(vals[node['left']],vals[node['right']],1 if k=='add' else -1)
        vals[i]=z
    return vals[target]

def fixed_mod(body,ports,p):
    fixed={r['name']:sum(t['coefficient']*math.prod(pow(ports[n],e,p) for n,e in zip(PORTS,t['powers'])) for t in r['terms'])%p for r in body['coefficient_recipes']}
    fixed['base_scale']=pow(2,body['base_scale_exponent'],p);fixed['threshold_scale']=pow(2,body['threshold_scale_exponent'],p)
    return fixed

def literal(v,ports,p,data,body,source):
    """Literal formula independent of circuit construction and layout recipes."""
    b,g,h,s,w,phi,i,j,n=(v[x]+(1 if x in ('b','g','h','s','w','i') else 0) for x in body['variables'])
    B=pow(2,body['base_scale_exponent'],p)*b*b%p;bp=lambda x:pow(B,x,p)
    DC=0;pad=data.get('padding_exponent',0);W=max(data['weights']);split=body['layout']=='split_116'
    ell=sum(bp(x) for x in data['weights'])%p
    if split:
        values=[0,0,0]
        for row,q in zip(data['order'],data['targets']):
            for aa,poly in source[row].items():
                deg=sum(aa);fac=2 if deg!=2 or 2 in aa else 1
                co=fac*sum(c*math.prod(pow(ports[x],e,p) for x,e in zip(PORTS,es)) for es,c in poly.items())
                ex=q-sum(x*y for x,y in zip(aa,data['weights']));values[deg]=(values[deg]+co*bp(ex))%p
        D0,D1,D2=values;Usource=(ell+g)%p;Gsource=(D0+D1*Usource+D2*Usource*Usource)%p;targets=sum(bp(q) for q in data['targets'])%p
    else:
        for row in data['rows']:
            for aa,poly in source[row['original_row_one_based']].items():
                co=sum(c*math.prod(pow(ports[x],e,p) for x,e in zip(PORTS,es)) for es,c in poly.items())
                co*=math.factorial(2-sum(aa))*math.prod(math.factorial(e) for e in aa)
                ex=row['target_exponent']-(2-sum(aa))*pad-sum(x*y for x,y in zip(aa,data['weights']))
                DC=(DC+co*bp(ex))%p
        targets=sum(bp(r['target_exponent']) for r in data['rows'])%p
    N0=bp(W+1);mask=(N0-1-(b-1)*ell)%p;Tc=(mask+(B-2)*targets*N0)%p
    Jc=(2*Gsource+targets)%p if split else (2*(bp(pad)+g)**2*DC+targets)%p;Sc=(g+Jc*N0)%p
    L=(1<<body['block_scale_power_of_two'])*b*bp(body['Ecode'])%p
    N=pow(2,body['threshold_scale_exponent'],p)*pow(b,body['threshold_b_power'],p)*bp(body['threshold_B_power'])%p
    R=(L*L+(Sc+Tc)*L+L-1-Sc)%p;Gcap=32*b*bp(W)%p
    U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p;K=(R+1+h*(P-1))%p
    A=M*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p;C=(B1+W1+phi)%p;J=(4*A-5)%p
    Q=(3*W1*C-2*(W1*W1-1))%p;D=((A*A-1)*C*C+1)%p;k=i*J*C%p;E=k*D*C%p
    F=((A*A-1)*E*E+1)%p;G=(A+F*(C*D+1-A))%p;H=(C+F*(B1+j*C))%p;GH=G*H%p;I=((G*G-1)*H*H+1)%p
    V0=P*K%p;a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p
    margin=((K*K-4*(C-K*Y)**2)*Gcap-8*g*K*K)*pow(8,-1,p)%p;Tpair=k*(8*D*D-4*D-1)%p;V1=Tpair*GH%p
    Omega=J*margin%p;E0=(J*n+Q)%p;Theta=(E0-Omega*(V0+V1))%p
    inner=(Theta*Theta-Omega*Omega*(a0+64*a1))%p;F9=(inner*inner-256*pow(Omega,4,p)*a0*a1)%p
    loc=locals();names={'Jcode':Jc,'Scode':Sc,'Tcode':Tc}
    if split:names.update(D0=D0,D1=D1,D2=D2,Usource=Usource,Gsource=Gsource)
    else:names['Dcode']=DC
    for name in ['b','B','ell','targets','N0','mask','L','N','R','Gcap','U','Y','M','P','K','A','B1','W1','C','J','Q','D','k','E','F','G','H','GH','I','V0','a0','a1','margin','Tpair','V1','Omega','E0','Theta','inner','F9']:names[name]=loc[name]%p
    return F9,names

def split_source_and_audit(data):
    """Cross-check both source transcriptions, reversible rows, all same-degree hits."""
    src=json.loads((ROOT/'data/parent_source.json').read_text());base=expand_source(False)
    old={r['number']:{} for r in src['equations']}
    for r in src['equations']:
        for t in r['terms']:
            aa=tuple(t['powers'][:31]);pp=tuple(t['powers'][31:]);old[r['number']].setdefault(aa,{})[pp]=t['coefficient']
    # The two authenticated compiler presentations differ by exactly -beta*J.
    unit=(1,)+(0,)*30;base[15][unit]=padd(base[15].get(unit,{}),{(1,0,0,0):1})
    base[15]={aa:poly for aa,poly in base[15].items() if poly}
    require(base==old,'independent original31/60-gate transcription bridge')
    def rowadd(a,b,sign=1):
        out={aa:poly.copy() for aa,poly in a.items()}
        for aa,poly in b.items():out[aa]=padd(out.get(aa,{}),poly,sign)
        return {aa:poly for aa,poly in out.items() if poly}
    source=dict(old);source[14]=rowadd(old[14],old[2]);source[15]=rowadd(old[15],old[3])
    require(rowadd(source[14],source[2],-1)==old[14] and rowadd(source[15],source[3],-1)==old[15],'inverse row identities')
    zero=(0,)*31;monomials={0:[zero],1:[],2:[]}
    for i in range(31):aa=list(zero);aa[i]=1;monomials[1].append(tuple(aa))
    for i,j in combinations_with_replacement(range(31),2):aa=list(zero);aa[i]+=1;aa[j]+=1;monomials[2].append(tuple(aa))
    direct=[{}, {}, {}];targets=dict(zip(data['targets'],data['order']));checks=hits=records=0
    seen=[set(),set(),set()]
    for rid,q in zip(data['order'],data['targets']):
        for aa,poly in source[rid].items():
            deg=sum(aa);fac=2 if deg!=2 or 2 in aa else 1;ex=q-sum(x*w for x,w in zip(aa,data['weights']))
            require(ex>=0 and ex not in seen[deg],'distinct nonnegative split encodings');seen[deg].add(ex);records+=1
            for pp,co in poly.items():direct[deg][(ex,)+pp]=co*fac
            for bb in monomials[deg]:
                at=ex+sum(x*w for x,w in zip(bb,data['weights']));actual=at in targets
                require(actual==(aa==bb) and (not actual or targets[at]==rid),'degree-separated isolation');checks+=1;hits+=actual
    require(records==89 and checks==22544 and hits==89,'split record ledger')
    kernels=json.loads((ROOT/'data/split_kernels.json').read_text())
    for degree,kernel in enumerate(kernels['kernels']):
        stored={(t['exponent'],)+tuple(c['powers']):c['coefficient'] for t in kernel['terms'] for c in t['coefficient']}
        require(stored==direct[degree],'exact kernel certificate')
    require({e[1:]:v for e,v in direct[2].items() if e[0]==1929}=={(0,)*4:1},'positive quadratic-kernel leader')
    require([max(e[0] for e in k) for k in direct]==[1719,2027,1929],'kernel degrees')
    require(max(max(e[0] for e in k)+d*max(data['weights']) for d,k in enumerate(direct))==2161,'convolution height')
    return source,direct,{'interaction_checks':checks,'intended_hits':hits,'source_records':records,'inverse_row_identities':2}

def main():
    if sys.flags.optimize:raise RuntimeError('Run without -O/-OO so all imported audit assumptions remain visible.')
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text());pinchecks=0
    for r in pins['imported']:require(sha((ROOT/r['path']).read_bytes())==r['sha256'],'source pin '+r['path']);pinchecks+=1
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text());ports={};payloads=[]
    for r in binding['ports']:
        gz=(ROOT/'coefficients'/r['gzip_file']).read_bytes();raw=gzip.decompress(gz);z=int.from_bytes(raw,'little')
        require(sha(gz)==r['gzip_sha256'] and sha(raw)==r['sha256'] and len(raw)==r['bytes'] and z.bit_length()==r['bits'],'coherent coefficient payload')
        ports[r['port']]=z;payloads.append(r['port'])
    ports={k:ports[v] for k,v in binding['port_aliases'].items()};native_ports=ports;native_source=expand_source();rng=random.Random(20261023)
    old_binding=json.loads((ROOT/'coefficients/old_tuple/COEFFICIENT_BINDING.json').read_text());old_ports={}
    require(sha((ROOT/'coefficients/old_tuple'/old_binding['complete_interface_proof_path']).read_bytes())==old_binding['complete_interface_proof_sha256'],'complete old31 coefficient adapter binding')
    require(sha((ROOT/'coefficients/old_tuple'/old_binding['source_binding_path']).read_bytes())==old_binding['source_binding_sha256'],'original coefficient binding provenance')
    for r in old_binding['payloads']:
        gz=(ROOT/'coefficients/old_tuple'/Path(r['path']).name).read_bytes();raw=gzip.decompress(gz);z=int.from_bytes(raw,'little')
        require(sha(gz)==r['gzip_sha256'] and sha(raw)==r['sha256'] and z.bit_length()==r['bit_length'],'old coherent tuple authentication')
        old_ports[r['name']]=z;payloads.append('old31/'+r['name'])
    old_ports={k:old_ports[v] for k,v in old_binding['port_aliases'].items()}
    audit={};rebuilds=replays=registers=symbolic_sources=coefficient_checks=0
    for layout in [f.stem.removeprefix('CERTIFICATE_') for f in sorted((ROOT/'data').glob('CERTIFICATE_*.json'))]+['split_116']:
        split=layout=='split_116';file=ROOT/'data'/('split_code.json' if split else 'CERTIFICATE_'+layout+'.json');data=json.loads(file.read_text())
        if split:source,direct,layout_audit=split_source_and_audit(data);ports=old_ports
        else:source=native_source;direct,layout_audit=audit_layout(data,source);ports=native_ports
        bodies={}
        for pos,cert in product([True,False],repeat=2):
            label=layout+'_'+('positive' if pos else 'natural')+('_certificate' if cert else '')
            obj=json.loads((ROOT/f'generated/{label}.json').read_text());fresh=build(layout,pos,cert,obj['encoding'],obj['power_method'])
            fresh=json.loads(json.dumps(fresh));require(fresh==obj,'exact rebuild '+label)
            require(sum(n['kind']=='variable' for n in obj['nodes'])==9,'nine variable leaves')
            counts=Counter(n['kind'] for n in obj['nodes'] if n['kind'] in ('add','sub','mul'));require(dict(counts)==obj['operation_counts'] and sum(counts.values())==obj['total_operations'],'live operation ledger')
            if split:
                for degree,poly in enumerate(direct):require(exact_source_dag(obj,'D'+str(degree))==poly,'exact split-source identity');symbolic_sources+=1
            else:require(exact_source_dag(obj)==direct,'exact shared/explicit source identity');symbolic_sources+=1
            bodies[pos,cert]=obj;rebuilds+=1
            if cert:
                dc=degree_certificate(obj);saved=json.loads((ROOT/f'generated/{label}_degree.json').read_text());require(dc==saved,'degree replay')
                r=4*obj['Ecode']+2;t=2*obj['threshold_B_power']+obj['threshold_b_power'];expected=188*r+400*t+8*obj['W']+236
                require(dc['exact_degree']==expected,'independently derived degree formula')
                require(dc['named_degrees']['R']==r and dc['named_degrees']['N']==t,'outer source degrees')
                require(dc['diagonal_leading_coefficient']==[{'base_scale_power':376*obj['Ecode']+400*obj['threshold_B_power']+4*obj['W'],'threshold_scale_power':400,'scalar_odd_part':'1','scalar_power_of_two':166+376*obj['block_scale_power_of_two']}],'explicit diagonal leader')
        body=bodies[False,False]
        for rec in body['coefficient_recipes']:
            co=sum(t['coefficient']*math.prod(ports[n]**e for n,e in zip(PORTS,t['powers'])) for t in rec['terms'])
            require(abs(co)<1<<body['coefficient_bound_exponent'],'actual coefficient bound');coefficient_checks+=1
        for p in [1000003,1000033,1000037]:
            pp={n:v%p for n,v in ports.items()};fixed={key:fixed_mod(obj,pp,p) for key,obj in bodies.items()}
            for case in range(40):
                vv={n:rng.randrange(100) for n in body['variables']};expected,names=literal(vv,pp,p,data,body,source)
                for (pos,cert),obj in bodies.items():
                    v={n:x+1 for n,x in vv.items()} if pos else vv;out,regs=evaluate(obj,fixed[pos,cert],v,p)
                    require(out==expected,'independent complete formula')
                    for n,z in names.items():
                        if n in regs:require(regs[n]==z,'independent register '+n);registers+=1
                replays+=1
        audit[layout]={**layout_audit,'degree':dc['exact_degree'],'positive_operations':bodies[True,False]['total_operations']}
    borrow=carry=calibration=majorant=crt=finalizer=0
    for B in [8,16,32,64,128]:
        for h in range(-B//4+1,B//4):
            for incoming in [-1,0]:
                raw=2*h+1+incoming;require(((raw%B)&(B-2)==0)==(h==0),'sparse +1 target equivalence')
                require(raw//B in (-1,0) and (2*h+incoming)//B in (-1,0),'borrow invariant');borrow+=1
    for u in range(1,9):
        L=1<<u
        for S in range(L):
            for T in range(L-S):
                R=L*L+(S+T)*L+L-1-S;threshold=u+T.bit_count()+1
                require(R.bit_count()==threshold-(S.bit_count()+T.bit_count()-(S+T).bit_count()),'block pop identity')
                require((R.bit_count()>=threshold)==(S&T==0),'block carry equivalence');carry+=1
    for W,E,kap,k in product([2,174,183],[20,5252,5438,8040],[21,22,1182967],range(1,16)):
        H=E+W+23;delta=(H-15)%2;lp=(21-H*kap)%2;c=((15+delta)*kap+lp-21)//2;e=(H-15-delta)//2;v=kap+2*k
        require(2*(c+delta*k+e*v)==lp+k+E*v+(W+23)*v-31*k-22+1,'exact square threshold');calibration+=1
    for A,C,i,G,H in product(range(2,6),range(2,5),range(1,4),range(2,5),range(1,4)):
        J=4*A-5;D=(A*A-1)*C*C+1;k=i*J*C;E=k*D*C;F=(A*A-1)*E*E+1;I=(G*G-1)*H*H+1;T=k*(8*D*D-4*D-1)
        require(T*T-64*D*F==(8*D+1)*k*k-64*D>0,'Pell defect identity')
        require((T*G*H)**2-64*D*F*I==((8*D+1)*k*k-64*D)*(G*H)**2+64*D*F*(H*H-1)>0,'whole radical majorant');majorant+=1
    for J,C,m,b1,j in product(range(2,8),range(2,8),range(1,4),range(1,2),range(6)):
        F=1+J*C*m;H=C+F*(b1+j*C);oldj=1+(F-1)//C*b1+F*j
        require(H==b1+oldj*C and oldj>=1 and (H-C)%F==0,'CRT witness transport');crt+=1
    for r0,r1,u,q,m in product(range(1,6),range(1,6),range(1,4),range(1,4),range(1,4)):
        a0=r0*r0;a1=r1*r1;V0=r0+1;V1=max(r1+1,q+1);Z=V0+V1+r0+r1;n=m*Z-q;O=u*m;Theta=u*n+u*q-O*(V0+V1)
        require(n>=0 and (Theta*Theta-O*O*(a0+a1))**2-4*O**4*a0*a1==0,'positive-root finalizer completeness');finalizer+=1
    # Separation and positivity are genuinely necessary: record explicit controls.
    def norm(a,b,V,W,u,v,m,n):
        O=u*m;t=u*n+v-O*(V+W);return (t*t-O*O*(a+b))**2-4*O**4*a*b
    require(norm(2,2,2,2,2,2,1,3)==0,'equal nonsquare-radical negative control')
    require(norm(1,4,-2,4,1,1,-1,0)==0,'negative-majorant negative control')
    # Exact universal polynomial identities, independently expanded.
    def power(poly,n):
        z={(0,)*len(next(iter(poly))):1}
        for _ in range(n):z=pmul(z,poly)
        return z
    def scale(poly,n):return {e:n*v for e,v in poly.items() if n*v}
    Dp={(1,0):1};kp={(0,1):1};one={(0,0):1}
    Tp=pmul(kp,padd(padd(scale(power(Dp,2),8),scale(Dp,4),-1),one,-1))
    Fp=padd(pmul(pmul(padd(Dp,one,-1),power(kp,2)),power(Dp,2)),one)
    defect=padd(pmul(padd(scale(Dp,8),one),power(kp,2)),scale(Dp,64),-1)
    require(padd(padd(power(Tp,2),scale(pmul(Dp,Fp),64),-1),defect,-1)=={},'exact universal Pell defect')
    th={(1,0,0,0):1};om={(0,1,0,0):1};x={(0,0,1,0):1};y={(0,0,0,1):1};product_norm={(0,0,0,0):1}
    for sx,sy in product([-1,1],repeat=2):product_norm=pmul(product_norm,padd(th,pmul(om,padd(scale(x,sx),scale(y,sy))),-1))
    squared=padd(power(th,2),pmul(power(om,2),padd(power(x,2),power(y,2))),-1)
    normpoly=padd(power(squared,2),scale(pmul(power(om,4),pmul(power(x,2),power(y,2))),4),-1)
    require(product_norm==normpoly,'exact four-factor norm identity')
    result={'status':'PASS','source_pin_checks':pinchecks,'authenticated_ports':payloads,'independent_source_rows':len(source),'rebuilt_circuits':rebuilds,'exact_symbolic_source_expansions':symbolic_sources,'exact_Pell_defect_and_norm_identities':2,'actual_coefficient_bounds':coefficient_checks,'modular_assignments':replays,'independent_named_register_checks':registers,'layout_audits':audit,'sparse_borrow_cases':borrow,'two_block_carry_cases':carry,'square_threshold_cases':calibration,'pell_majorant_cases':majorant,'CRT_transport_cases':crt,'finalizer_completeness_cases':finalizer,'essential_hypothesis_negative_controls':2,'scope':'Finite implementation/data audit; the universal theorem imports the identified compiler and Jones ratio contracts.'}
    (ROOT/'generated/VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
