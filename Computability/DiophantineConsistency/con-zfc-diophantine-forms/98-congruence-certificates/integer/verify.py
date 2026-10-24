#!/usr/bin/env python3
"""Independent finite checks, not a proof of the inherited calibration."""
from pathlib import Path
import gzip,hashlib,json,random,importlib.util

ROOT=Path(__file__).resolve().parent
PACKET=ROOT/'equations/integer13_crt_valuation_degree1072.json'

def need(ok,msg):
    if not ok: raise ValueError(msg)

def constants():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    out={}
    for name,rec in binding['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes())
        need(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'coefficient hash: '+name)
        out[name]=int.from_bytes(raw,'little')
    need(out['beta']==2**1064921-1,'literal beta')
    need(out['cone_A']==2**1113 and out['cone_B']==2**666104,'cone scales')
    recipe=ROOT/'coefficients/recipe/source34_builder.py'
    spec=importlib.util.spec_from_file_location('retained_coefficient_recipe',recipe)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    regenerated,audit=module.construct()
    for new,old in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        need(out[new]==regenerated[old],'exact regenerated coefficient: '+new)
    need(audit['basis_convolution_checks']==69230,'native coefficient recipe coverage')
    return out

def evaluate(g,x,p,prime):
    vals=[]
    for node in g['nodes']:
        op=node[0]
        if op=='integer': val=node[1]
        elif op=='coefficient':val=p[node[1]]
        elif op=='variable':val=x[node[1]]
        else:
            a,b=vals[node[1]],vals[node[2]]
            val=a+b if op=='add' else a-b if op=='sub' else a*b
        vals.append(val%prime)
    return vals

def conjugate_product(center,ds,prime):
    """Multiply every linear factor in the free quadratic algebra."""
    rank=1<<len(ds)
    vec=[0]*rank;vec[0]=1
    for signs in range(rank):
        new=[0]*rank
        for mask,a in enumerate(vec):
            new[mask]=(new[mask]+a*center)%prime
            for i in range(len(ds)):
                sign=1 if signs&(1<<i) else -1
                coeff=-sign*a
                if mask&(1<<i):coeff*=ds[i]
                dest=mask^(1<<i)
                new[dest]=(new[dest]+coeff)%prime
        vec=new
    need(all(v==0 for v in vec[1:]),'formal norm must be scalar')
    return vec[0]

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def padd(a,b,p,sign=1):
    c=a+[0]*max(0,len(b)-len(a))
    for i,v in enumerate(b):c[i]=(c[i]+sign*v)%p
    return trim(c)
def pmul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:c[i+j]=(c[i+j]+x*y)%p
    return trim(c)

def degree_slice(g,co,prime):
    vals=[]
    for node in g['nodes']:
        op=node[0]
        if op=='integer':v=[node[1]%prime]
        elif op=='coefficient':v=[co[node[1]]%prime]
        elif op=='variable':v=[0,1]
        elif op=='add':v=padd(vals[node[1]],vals[node[2]],prime)
        elif op=='sub':v=padd(vals[node[1]],vals[node[2]],prime,-1)
        elif op=='mul':v=pmul(vals[node[1]],vals[node[2]],prime)
        vals.append(v)
    output=vals[g['output']]
    q=6*co['beta']%prime;W=12;Y=q;a=q*W*Y%prime;i=2
    R=-pow(q,3,prime)*(W-q)%prime;k=(R+a)%prime
    nv=len(g['variables']);U=8*q*q*a%prime;M=2*q*q%prime
    S=-24*pow(Y,4,prime)*pow(k,4,prime)%prime
    Dt=pow(q*W*Y*Y,2,prime)*pow(k,2,prime)%prime
    Ef=-a*a*i*i%prime;Eg=-S%prime;Et=-Dt%prime
    Q=a*a%prime;V=-R%prime
    if nv==13:
        leader=(pow(2,136,prime)*pow(3,56,prime)*pow(q,64,prime)*
                pow(a,128,prime)*pow(i,64,prime)*pow(R,16,prime)*
                pow(Y,32,prime)*pow(k,32,prime))%prime
    elif nv==14:leader=pow(Q,8,prime)*pow(81*U*U*S,8,prime)*Ef%prime
    elif nv==15:leader=pow(Q,4,prime)*pow(9*U*U*Dt,4,prime)*Ef*Eg%prime
    else:
        ss=U+M*a;Amain=M*M*a*a
        leader=4*Q*Q*U*U*V*V*(ss*ss-Amain)*Ef*Eg*Et%prime
    need(len(output)-1==g['exact_degree'],'literal exact degree attained on diagonal')
    need(output[-1]==leader and leader!=0,'top homogeneous formula')
    return {'prime':prime,'degree':len(output)-1,'leading_coefficient':leader}

def check_packet(path,co):
    g=json.loads(path.read_text());rng=random.Random(1072);nv=len(g['variables'])
    live=set()
    def visit(i):
        if i in live:return
        live.add(i);n=g['nodes'][i]
        if n[0] in ('add','sub','mul'):
            need(0<=n[1]<i and 0<=n[2]<i,'DAG topological order')
            visit(n[1]);visit(n[2])
    visit(g['output']);need(len(live)==len(g['nodes']),'all nodes live')
    need({n[1] for n in g['nodes'] if n[0]=='variable'}==set(g['variables']),'all inputs live')
    count=sum(n[0] in ('add','sub','mul') for n in g['nodes'])
    need(count=={13:195,14:148,15:130,16:118}[nv]==g['operations'],'binary operation count')
    checked=0
    for prime in [1009,1013,1019]:
        for trial in range(24):
            x={v:rng.randrange(-8,9) for v in g['variables']}
            if trial%3==0:x['v']=0
            if trial%4==0:x['c']=0
            vals=evaluate(g,x,co,prime)
            reg={k:vals[n] for k,n in g['named_registers'].items()}
            delta=reg['delta']
            if delta==0:continue
            ds=[reg['scaled_Dmain'],reg['scaled_Cy']*pow(delta,-1,prime)%prime]
            if nv<=15:ds.append(reg['scaled_Dtau'])
            if nv<=14:ds.append(reg['scaled_S'])
            if nv==13:ds.append(reg['scaled_Df'])
            want=pow(delta,1<<(len(ds)-1),prime)*conjugate_product(reg['center'],ds,prime)%prime
            if nv>=14:
                want=(1+want)*reg['Ff']%prime
                if nv>=15:want=want*reg['Fg']%prime
                if nv==16:want=want*reg['Ft']%prime
                want=(want-1)%prime
            need(vals[g['output']]==want,'independent conjugate product')
            checked+=1
    return {'status':'PASS','variables':nv,'operations':count,
             'conjugate_product_signed_assignments':checked,
             'degree_slice':degree_slice(g,co,1009),
             'scope':'Exact coefficient binding, topology/liveness, finite modular identity diagnostics, and exact univariate degree attainment. Unbounded soundness/completeness and degree upper bound are in PROOF.md and FAMILY.md.'}

def main():
    ledger=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for rec in ledger['verbatim_members']:
        data=(ROOT/rec['local_path']).read_bytes()
        need(len(data)==rec['size_bytes'] and hashlib.sha256(data).hexdigest()==rec['sha256'],'retained source hash: '+rec['local_path'])
    co=constants()
    paths=[ROOT/'equations'/s for s in [
        'integer13_crt_valuation_degree1072.json',
        'integer14_crt_valuation_degree414.json',
        'integer15_crt_valuation_degree218.json',
        'integer16_crt_valuation_degree124.json']]
    receipt=[check_packet(p,co) for p in paths]
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
