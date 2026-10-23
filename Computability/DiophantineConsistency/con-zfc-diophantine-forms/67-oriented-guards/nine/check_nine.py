#!/usr/bin/env python3
"""Independent modular literal replay and structural checks. No builder imported."""
from pathlib import Path
import json, gzip, random, math, hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parent
PORTS=('beta','K0','MC','MF')
def require(x,m):
    if not x:raise ValueError(m)
def evaluate(body,ports,v,p):
    fixed={r['name']:sum(t['coefficient']*math.prod(pow(ports[k],e,p) for k,e in zip(PORTS,t['powers'])) for t in r['terms'])%p for r in body['coefficient_recipes']}
    fixed.update(base_scale=pow(2,body['base_scale_exponent'],p),threshold_scale=pow(2,body['threshold_scale_exponent'],p))
    vals=[]
    for j,n in enumerate(body['nodes']):
        typ=n['kind']
        if typ=='variable':z=v[n['name']]
        elif typ=='literal':z=n['value']
        elif typ=='fixed':z=fixed[n['name']]
        else:
            require(n['left']<j and n['right']<j,'acyclic circuit')
            a,b=vals[n['left']],vals[n['right']];z=a+b if typ=='add' else a-b if typ=='sub' else a*b
        vals.append(z%p)
    return vals[body['output']],{k:vals[i] for k,i in body['named_nodes'].items()}
def literal(body,ports,v,p):
    b,g,h,s,w,C,i,j,n=[v[k] for k in body['variables']]
    if body['domain']=='positive integers':j-=1
    else:b+=1;g+=1;h+=1;s+=1;w+=1;C+=1;i+=1;n+=1
    data=json.loads((ROOT/'data'/('split108_code.json' if body['W']==108 else 'split_code.json')).read_text())
    kernels=json.loads((ROOT/'data'/('split108_kernels.json' if body['W']==108 else 'split_kernels.json')).read_text())
    B=pow(2,body['base_scale_exponent'],p)*b*b%p; bp=lambda e:pow(B,e,p)
    ds=[]
    for row in kernels['kernels']:
        ds.append(sum(bp(t['exponent'])*sum(q['coefficient']*math.prod(pow(ports[k],e,p) for k,e in zip(PORTS,q['powers'])) for q in t['coefficient']) for t in row['terms'])%p)
    ell=sum(bp(e) for e in data['weights'])%p; target=sum(bp(e) for e in data['targets'])%p
    us=(ell+g)%p;gs=(ds[0]+ds[1]*us+ds[2]*us*us)%p;N0=bp(body['W']+1)
    tc=(N0-1-(b-1)*ell+N0*(B-2)*target)%p;sc=(g+N0*(2*gs+target))%p
    L=(1<<body['block_scale_power_of_two'])*b*bp(body['Ecode'])%p
    N=pow(2,body['threshold_scale_exponent'],p)*pow(b,body['threshold_b_power'],p)*bp(body['threshold_B_power'])%p
    R=(L*(sc+tc+1)-sc-1)%p; t=b*bp(body['W'])%p
    U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p;K=(R+1+h*(P-1))%p
    A=M*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p;J=(4*A-5)%p
    Q=(3*W1*C-2*(W1*W1-1))%p;D=((A*A-1)*C*C+1)%p;e=i*J*C%p;E=e*D*C%p
    F=((A*A-1)*E*E+1)%p;Lm=(C*D+1-A)%p;G=(A+F*Lm)%p;H=(C+F*(B1+j*C))%p;I=((G*G-1)*H*H+1)%p
    Ns=[(2*e*e*D*(D-1)*Lm+3*C)%p,2*e*e*(D-1)*Lm%p,2*e*e*(Lm-C)%p,2*e*e*C%p]
    order=body['majorant_order'];scale=[128,64,8,4,1][max(0,order)];lam=8 if order==-1 else 2048//scale
    cor=(256*i*(e*e+2)+2048)%p if order==4 else ((512//scale)*i+lam)%p if order else lam
    T=(e*(((1024//scale)*D*D-(512//scale)*D-128//scale)*(2*G+Lm)-sum((a//scale)*q for a,q in zip([64,40,28,21][:order],Ns[:order])))+cor)%p
    if order==-1:T=e*(8*D*D-4*D-1)*G%p
    V0=P*K%p;V1=T*H%p;a0=((P*P-1)*K*K+1)%p;a1=lam*lam*D*F*I%p
    margin=(K*K*(4*t-g)-16*t*(C-K*Y)**2)%p;Omega=J*margin%p;E0=(J*(n+W1*W1)+Q)%p
    Theta=(E0-Omega*(V0+V1))%p;out=((Theta*Theta-Omega*Omega*(a0+a1))**2-4*pow(Omega,4,p)*a0*a1)%p
    return out,D

def main():
    for row in json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']:
        require(hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256'],'source pin '+row['path'])
    pin=json.loads((ROOT/'upstream/FREE_C_SOURCE_PINS.json').read_text())
    for row in pin['imported']:
        if row['path'].startswith('coefficients/') or row['path']=='data/parent_source.json':require(hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256'],'pinned imported payload '+row['path'])
    paths=[('beta','beta.bin.gz'),('K0','K.bin.gz'),('MC','MC.bin.gz'),('MF','MF_source.bin.gz')]
    ports={k:int.from_bytes(gzip.decompress((ROOT/'coefficients/old_tuple'/f).read_bytes()),'little') for k,f in paths}
    rng=random.Random(20261023);tests=0
    for f in sorted((ROOT/'generated').glob('split_*_order*_*.json')):
        if f.name.endswith('_degree.json'):continue
        body=json.loads(f.read_text());counts=Counter(n['kind'] for n in body['nodes'] if n['kind'] in ('add','sub','mul'))
        require(dict(counts)==body['operation_counts'] and sum(counts.values())==body['total_operations'],'gate counts')
        used=set();stack=[body['output']]
        while stack:
            j=stack.pop()
            if j in used:continue
            used.add(j);node=body['nodes'][j]
            if 'left' in node:stack.extend([node['left'],node['right']])
        require(len(used)==len(body['nodes']),'no dead circuit nodes')
        for p in [1000003,1000033,1000000007]:
            if body['degree_certificate_form']:
                fixed={r['name']:sum(t['coefficient']*math.prod(pow(ports[k],e,p) for k,e in zip(PORTS,t['powers'])) for t in r['terms'])%p for r in body['coefficient_recipes']}
                fixed.update(base_scale=pow(2,body['base_scale_exponent'],p),threshold_scale=pow(2,body['threshold_scale_exponent'],p))
                heads=[]
                for node in body['nodes']:
                    kind=node['kind']
                    if kind=='literal': pair=(0,node['value']%p)
                    elif kind=='variable':pair=(1,1)
                    elif kind=='fixed':pair=(0,fixed[node['name']])
                    else:
                        (da,ha),(db,hb)=heads[node['left']],heads[node['right']]
                        if kind=='mul':pair=(da+db,ha*hb%p)
                        else:
                            deg=max(da,db);pair=(deg,((ha if da==deg else 0)+(1 if kind=='add' else -1)*(hb if db==deg else 0))%p)
                    heads.append(pair)
                deg,head=heads[body['output']];dc=json.loads(f.with_name(f.stem+'_degree.json').read_text())
                require(head!=0 and deg==dc['certificate_degree'],'independent exact certificate degree')
                require(deg-16*heads[body['named_nodes']['D']][0]==dc['exact_degree'],'primary degree after polynomial factor')
                expected=0
                for term in dc['certificate_diagonal_leading_coefficient']:
                    expected+=int(term['scalar_odd_part'])*pow(2,term['scalar_power_of_two'],p)*pow(fixed['base_scale'],term['base_scale_power'],p)*pow(fixed['threshold_scale'],term['threshold_scale_power'],p)*math.prod(pow(ports[k],ex,p) for k,ex in zip(PORTS,term['port_powers']))
                require(head==expected%p,'actual-payload leading coefficient')
            for trial in range(8):
                v={k:rng.randrange(1 if body['domain']=='positive integers' else 0,12) for k in body['variables']}
                got,names=evaluate(body,ports,v,p);want,D=literal(body,ports,v,p)
                if body['degree_certificate_form']:want=want*pow(D,16,p)%p
                require(got==want,'literal replay '+f.name);tests+=1
    print(json.dumps({'status':'PASS','modular_literal_replays':tests,'payloads':'old31 whole tuple authenticated','scope':'Finite implementation audits, not end-to-end kernel proof'},indent=2))
if __name__=='__main__':main()
