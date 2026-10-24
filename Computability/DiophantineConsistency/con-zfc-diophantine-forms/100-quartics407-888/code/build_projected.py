#!/usr/bin/env python3
"""Eight bounded columns, natural quadratic source gates, shared certificates."""
from pathlib import Path
import argparse,hashlib,json,sys
import build as ng
sys.path.insert(0,str(Path(__file__).resolve().parent))
from reuse_radix import AdditiveReusedRadixBuilder
from build import ONE,ZERO,TWO,write_json,contract,independent_verify,polynomial_and_metrics
from build_equation import Builder

LOCAL_NAMES=('a','b','c','d','S','Sp','u','vq')

def codes(b,source,env):
    return ng.direct_source(b,source,dict(env,p=ZERO,q=ZERO,v=ZERO),ZERO,False,codes_only=True)

def projected_source(b,source,env,index):
    data=codes(b,source,env);cs=data['codes'];I,A=data['I'],data['A']
    a,z,c,d=[env[s] for s in ('a','b','c','d')]
    add,mul,sd,sq=b.add,b.mul,b.sqdiff,b.square
    S,Sp,M=env['S'],env['Sp'],add(env['M0'],ONE)
    SpM=mul(Sp,M)
    ordinary=[sd(Sp,S)]+[sd(add(Sp,mul(SpM,h)),S) for h in cs[:-1]]
    guard=sd(mul(sd(c,a),sd(c,z)),sq(add(d,ONE)))
    bundle=add(sd(add(Sp,mul(SpM,cs[-1])),S),guard)
    def weight(v):return add(ONE,mul(v,M))
    mp=sd(mul(Sp,weight(z)),b.product([S,weight(a),weight(I(a,z))]))
    gen=sd(mul(Sp,weight(A(a,z))),mul(S,weight(z)))
    horn=b.product(ordinary+[bundle,mp,gen])
    den=add(mul(add(index,ONE),env['y']),ONE)
    beta=[sd(env['x'],add(S,mul(den,env['u']))),
          sd(env['x'],add(Sp,mul(add(den,env['y']),env['vq'])))]
    return b.sum([horn]+beta)

def bound_certificate(b,atoms,output):
    exponents={a[1]:1 for a in atoms.values()}
    def wt(a):return max(0,(a[1]-1).bit_length()) if a[0]=='c' else exponents[a[1]]
    ledger=[]
    for (op,a,c),o in b.cache.items():
        e=max(wt(a),wt(c))+1 if op=='add' else wt(a)+wt(c)
        exponents[o[1]]=e
        ledger.append({'output':o[1],'operation':op,'left':list(a),'right':list(c),'exponent':e})
    return {'inputs':list(atoms),'gates':ledger,'output':list(output),'exponent':wt(output)}

def label_majorant(source):
    b=Builder(True);t=b.new('t');data=codes(b,source,{s:t for s in ('a','b','c','d')})
    labels=data['codes']+[t,data['I'](t,t),data['A'](t,t)]
    # Sum dominates every label, its added one dominates label+1.
    out=b.sum(labels+[ONE])
    cert=bound_certificate(b,{'t':t},out)
    cert['base']='t+1'
    cert['carrier_exponent']=1<<(cert['exponent']-1).bit_length()
    return cert

class UpperBuilder(Builder):
    def sqdiff(self,a,b):return self.square(self.add(a,b))

def local_majorant(source):
    b=UpperBuilder(True)
    atoms={n:b.new(n) for n in ('t','x','y','M0')}
    bounds={n:atoms['t'] if i<4 else atoms['y'] if i<6 else atoms['x'] for i,n in enumerate(LOCAL_NAMES)}
    value=projected_source(b,source,atoms|bounds,atoms['t'])
    out=b.sum([value,atoms['t'],atoms['x'],atoms['y'],ONE])
    cert=bound_certificate(b,atoms,out)
    cert['base']='2+t+x+y+M0'
    cert['squared_difference_majorization']='(u-v)^2 <= (U+V)^2 for 0<=u<=U,0<=v<=V'
    cert['emitted_exponent']=max(4,1<<(cert['exponent']-1).bit_length())
    return cert

def construct():
    b=AdditiveReusedRadixBuilder(positive_powers=True)
    src=(ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes();source=json.loads(src)
    params={n:b.new(n+('0' if n=='t' else ''),'outer') for n in ('t','x','y','M0')}
    params['t']=b.add(params['t'],ONE)
    t,x,y,M0=[params[n] for n in ('t','x','y','M0')]
    labelcert=label_majorant(source)
    basepower=b.power(b.add(t,ONE),t)
    carrier=ng.syn.fixed_power(b,basepower,labelcert['carrier_exponent'])
    b.eq(carrier,b.add(M0,ONE),'projected.carrier')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:t if i<4 else y if i<6 else x for i,n in enumerate(LOCAL_NAMES)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in LOCAL_NAMES}
    C=b.new('crt.encoded_index')
    boundcert=local_majorant(source)
    R=b.sum([TWO,t,x,y,M0]);H=ng.syn.fixed_power(b,R,boundcert['emitted_exponent'])
    T=b.factorial(H);B=b.moduli_product(t,T)
    for n in LOCAL_NAMES:b.divisible_binomial(encoded[n],b.add(bounds[n],ONE),B,'crt.range.'+n)
    b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),B,'crt.canonical_index')
    value=projected_source(b,source,params|encoded,C)
    q=b.new('crt.nonnegative_quotient');b.eq(value,b.mul(B,q),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,src,labelcert,boundcert

def generate(out,caps=(16,64)):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    b,src,lc,bc=construct()
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'projected_eight_columns',True)
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),
                     ('label_majorant.json',lc),('local_majorant.json',bc),
                     ('radix_certificate.json',b.radix_data),('macro_inventory.json',b.macro_log),
                     ('index_derivations.json',b.index_derivations),
                     ('gate_ledger.json',{'square_difference_gates':b.sqd_ledger,
                        'all_variables':b.variables,'all_rows':b.rows,'gates':b.gates})]:write_json(out/name,obj)
    counts={'source':metrics,'label_exponent':lc['carrier_exponent'],
            'local_exponent':bc['emitted_exponent'],'seed_indices':len(b.seed_indices)}
    for cap in caps:
        target,cc=contract(eq,support_cap=cap,terminal_quadratic=True)
        receipt=independent_verify(eq,target,cc);pp,mm=polynomial_and_metrics(target['residuals'],len(target['variables']))
        dest=out/('cap'+str(cap));dest.mkdir(exist_ok=True)
        for name,obj in [('equation.json',target),('expanded_polynomial.json',pp),
                          ('elimination_certificate.json',cc),('VERIFICATION.json',receipt)]:write_json(dest/name,obj)
        counts[str(cap)]=mm
    write_json(out/'METRICS.json',counts)
    return counts

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    print(json.dumps(generate(a.output),indent=2))
