"""Construct the new complemented-label radix47 P66 specialization."""
from pathlib import Path
import json,gzip,hashlib,math
from radix_probe import decode_tiles,coefficients,residues,require,prime,factors,order,L,MARKERS
from materialize_radix49 import old_coefficient_route,polynomial_metrics

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'radix47'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def complement_coefficients():
    tiles=decode_tiles();c=coefficients(tiles,True)
    for i,(w,n,p,s) in enumerate(tiles):
        u=w+(n<<8)+(p<<17)+(s<<25)
        c[i]=1+1024*(u+1)
    old,pin=old_coefficient_route()
    for i in range(943):old[i]=2+(1<<44)+1024-old[i]
    require(c==old,'all complemented coefficients vs independent old K route')
    return c,pin

def geometric_checks(c):
    E=set(i for i,x in enumerate(c) if x)|{1063,1064}
    D={30:1,62:1,1100:1,2201:1}
    for e,ce in enumerate(c):
        if ce:
            for target in [4393-e,5495-e]:
                require(target not in D,'distinct kernel residues');D[target]=ce
    require(42 not in D and max(D)<L,'spatial residue separated')
    def row(t):return {e:D[t-e] for e in E if t-e in D}
    claims=[]
    def test(t,expected,name):
        got=row(t);require(got==expected,'native geometry '+name+str(t));claims.append({'target':t,'name':name,'terms':[[k,v] for k,v in sorted(got.items())]})
    for j in range(10):test(1013+j,{983+j:1},'north-copy')
    for j in range(9):test(1065+j,{1003+j:1},'spatial-copy')
    test(2195,{1095:1},'anchor');test(3296,{1095:1},'anchor')
    test(2194,{},'anchor-reset');test(3295,{2195:1},'anchor-reset')
    test(1012,{},'north-reset');test(1064,{},'spatial-reset')
    linear={e:c[e] for e in E if c[e]}
    test(4393,linear,'clause');test(5495,linear,'clause')
    adj={e:c[e+1] for e in E if e+1<len(c) and c[e+1]}
    test(4392,adj,'clause-reset')
    adj2=dict(adj);adj2[3296]=adj2.get(3296,0)+c[2195]
    test(5494,adj2,'clause-reset')
    test(7690,{2195:c[0]},'padding-reset');test(8791,{3296:c[0]},'padding-reset')
    for t in range(7691,7696):test(t,{},'padding-zero')
    for t in range(8792,8807):test(t,{},'tail-zero')
    require(not [(e,f) for e in E for f in E if e-f==1102],'clause hit disjointness')
    require([(e,f) for e in sorted(E) for f in sorted(E) if e-f==1101]==[(3296,2195)],'unique anchor gap')
    require(all(42+e not in [2194,2195,3295,3296,4392,4393,5494,5495,7690,8791] for e in E),'no spatial term at high tests')
    return {'support_count':len(E),'kernel_terms':len(D),'spatial_residue':42,'claims':claims,'unique_anchor_pair':[3296,2195],'clause_gap_absent':1102},E,D

def controller(c):
    b=47;d=b*L;spacing=23*4403
    fixed=[residues(b,c,m) for m in [47,8807]]
    require(all(x['Hctrl'] for x in fixed),'fixed controller units')
    candidates=[];selected=None
    for m in range(5,65):
        p=spacing*m+1;r={'index':m,'candidate':p}
        if not prime(p):
            r['result']='composite';r['least_factor']=next(k for k in range(2,math.isqrt(p)+1) if p%k==0)
        else:
            r.update(residues(b,c,p));r['order']=order(r['B'],p);r['order_factors']=factors(r['order']);r['lambda_minus_one_factors']=factors(p-1)
            r['lift_residue']=pow(2,d*(p-1),p*p);r['lift_quotient']=(r['lift_residue']-1)//p
            if pow(r['B'],2,p)==1:r['result']='square-unit-obstruction'
            elif r['lift_residue']==1:r['result']='lift-obstruction'
            elif r['Hctrl']==0:r['result']='bracket-obstruction'
            else:r['result']='found';selected=r
        candidates.append(r)
        if selected:break
    require(selected is not None,'bounded controller search found')
    return {'radix_bits':47,'d':d,'spacing':spacing,'range':[5,64],'fixed':fixed,'search':candidates,'outcome':'found','selected':selected}

def main():
    OUT.mkdir(exist_ok=True);(OUT/'coefficients').mkdir(exist_ok=True)
    c,oldpin=complement_coefficients();geom,E,D=geometric_checks(c)
    rho=1<<47;B=1<<(47*L);P=lambda e:1<<(47*e)
    K=sum(ce*P(e) for e,ce in D.items())+P(L+42)
    MC=B-1-sum(P(e) for e in E if e!=1)-2*P(1063)
    core=sum(P(e) for e in range(1013,1023))+sum(P(e) for e in range(1065,1074))+P(2195)+P(3296)
    padding=(rho-1)*sum(P(e) for e in range(8792,8807))+(rho-1)*sum(P(e) for e in range(7691,7694))+((1<<28)-4)*P(7694)
    require(padding==B-P(8792)+((1<<28)-3)*P(7694)-P(7691),'compressed padding equality')
    native=4+(rho-2)*(P(4393)+P(5495))+core+padding
    values={'beta':B-1,'K0':K,'MC':MC,'MF':native+B-1}
    require(0<MC<B-1<native+B-1<2*(B-1),'coherent scalar box')
    require(MC%4==2 and native%8==4,'origin residues')
    require(MC.bit_count()==47*L-986 and native.bit_count()==986,'mask populations')
    require(max(c)==1<<44 and max(c[:943])<1<<44,'actual coefficient maximum')
    S=sum(c);M=max(c)
    require(S+2*M+5+3*rho//4+29<30*rho,'predecoded carry29')
    require(88*M+(rho-1024)+2*M+5+3*rho//4+29<13*rho,'decoded carry12')
    require(943+29<1024,'selector bootstrap')
    require(7*M-1024+12<rho,'clause predecessor reset')
    binding={}
    for name,value in values.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little');comp=gzip.compress(raw,compresslevel=9,mtime=0)
        path=OUT/'coefficients'/(name+'.bin.gz');path.write_bytes(comp)
        binding[name]={'file':'coefficients/'+path.name,'bits':value.bit_length(),'raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(comp),'gzip_sha256':sha(comp)}
    cert=controller(c)
    for m in [47,8807,cert['selected']['candidate']]:
        r=residues(47,c,m);require(K%m==r['K'] and (1+B*K+B*B)%m==r['Hctrl'],'whole modular association')
    p=json.loads((ROOT/'sources/candidates/one-page-compact66-radix55/polynomial.json').read_text())
    p['name']='complemented_labels_radix47_p66_degree157'
    p['coefficient_binding']={'schema':'whole_complemented_labels_radix47_p66_binding_v1','ports':binding,'raw_bytes':sum(x['raw_bytes'] for x in binding.values()),'tuple':'complete coherent47 tuple; complemented34 labels; seven shared markers; MF shifted once'}
    p['proof']='radix47_proof.md'
    p['proof_boundary']='New complemented-label/native radix47 proof, complete controller and tuple; retained P66 and K215 syntactic-refutation calibration; no new Lean derivation.'
    metrics=polynomial_metrics(p);require(metrics['operations']==66,'operation count')
    metrics['proved_exact_degree']=157;metrics['proved_factor_degrees']={'N0':22,'N1':18,'Na':62,'Nk':7,'Nt':2,'Ns':46}
    dump(OUT/'polynomial.json',p);dump(OUT/'phi_coefficients.json',c);dump(OUT/'native_geometry.json',geom)
    report={'repository':'VladimirReshetnikov/ProveIt','commit':'55d1f72aedebf892e446c90d35fa1ae37689b0f2','encoding':'34 complemented label bits with unchanged physical support and shared markers','radix_bits':47,'d':47*L,'controller':cert,'binding':binding,'raw_bytes':sum(x['raw_bytes'] for x in binding.values()),'gzip_bytes':sum(x['gzip_bytes'] for x in binding.values()),'phi_slots':len(c),'phi_nonzero':sum(bool(x) for x in c),'phi_sha256':sha(json.dumps(c,separators=(',',':')).encode()),'coefficient_sum':S,'maximum_coefficient':M,'maximum_selector_coefficient':max(c[:943]),'predecoded_carry_cap':29,'decoded_carry_cap':12,'independent_old_K_recovery':oldpin,'metrics':metrics,'masks':{'MC_population':MC.bit_count(),'MF_native_population':native.bit_count(),'MC_mod4':MC%4,'MF_native_mod8':native%8,'padding_population':padding.bit_count()}}
    dump(OUT/'construction_report.json',report);print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
