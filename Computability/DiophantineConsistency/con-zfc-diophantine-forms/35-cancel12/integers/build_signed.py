#!/usr/bin/env python3
"""Build and audit compact sixteen/seventeen-integer consistency polynomials.

Input DAGs are inert JSON.  Standard library only.  No assertion here decides
ZFC consistency; checks concern identities, coefficient recipes and size.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import hashlib, itertools, json, random

if not __debug__:
    raise SystemExit('Optimized Python disables the audit assertions and is not permitted.')

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'upstream' if (HERE/'upstream').exists() else HERE.parent/'integer_source'
BASE=SOURCE/'30-quartic31/nine/nu31/nine_compact_magnitude_tight.json'
CONSTANTS=SOURCE/'30-quartic31/nine/nu31/COMPACT_CONSTANTS.json'
PORT_BITS=[1064921,1070004,1064921,1064922]
EXPECTED_PORT_SHA256={
    'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K':'6984850dcfc65498b42b633855ea81b8c2cf6d0a84e49005cca10f25557ae395',
    'MC':'7c2b34179cb98c9bea1954f816f93fdc1f60213c68d8e98f1541edb41f0e3a4b',
    'MF_source':'28c55970993394dd7ee32d7299a215fd26b4d70e437a643b60594eee8c7cd3a7'}
PIN='8c6eec9d19ef80538c8e61ff6e0180040583446a'

class Circuit:
    def __init__(self): self.nodes=[];self.cache={};self.values={};self.names={}
    def intern(self,n):
        key=tuple(sorted(n.items()))
        if key not in self.cache:
            self.cache[key]=len(self.nodes);self.nodes.append(n)
        i=self.cache[key]
        if n['kind']=='literal':self.values[i]=n['value']
        return i
    def const(self,v):return self.intern(dict(kind='literal',value=v))
    def var(self,v):return self.intern(dict(kind='variable',name=v))
    def fixed(self,v):return self.intern(dict(kind='fixed',name=v))
    def op(self,k,a,b):
        va,vb=self.values.get(a),self.values.get(b)
        if va is not None and vb is not None:
            return self.const(va+vb if k=='add' else va-vb if k=='sub' else va*vb)
        if k=='add' and va==0:return b
        if k in ('add','sub') and vb==0:return a
        if k=='mul' and (va==0 or vb==0):return self.const(0)
        if k=='mul' and va==1:return b
        if k=='mul' and vb==1:return a
        if k in ('add','mul') and b<a:a,b=b,a
        return self.intern(dict(kind=k,left=a,right=b))
    def add(self,*args):
        ans=self.const(0)
        for a in args:ans=self.op('add',ans,a)
        return ans
    def mul(self,*args):
        ans=self.const(1)
        for a in args:ans=self.op('mul',ans,a)
        return ans
    def sub(self,a,b):return self.op('sub',a,b)
    def power(self,a,k):
        if k==0:return self.const(1)
        if k==1:return a
        h=self.power(a,k//2);v=self.mul(h,h)
        return self.mul(v,a) if k%2 else v
    def save(self,name,node):self.names[name]=node;return node
    def pack(self,out):
        alive=set();todo=[out]
        while todo:
            i=todo.pop()
            if i in alive:continue
            alive.add(i);n=self.nodes[i]
            if n['kind'] in ('add','sub','mul'):todo.extend([n['left'],n['right']])
        ids={v:k for k,v in enumerate(sorted(alive))};nodes=[]
        for i in sorted(alive):
            n=self.nodes[i].copy()
            if n['kind'] in ('add','sub','mul'):n['left'],n['right']=ids[n['left']],ids[n['right']]
            nodes.append(n)
        counts=Counter(n['kind'] for n in nodes)
        return dict(nodes=nodes,output=ids[out],named_nodes={k:ids[v] for k,v in self.names.items() if v in ids},
                    variables=[n['name'] for n in nodes if n['kind']=='variable'],
                    operation_counts={k:counts[k] for k in ('add','sub','mul')})

def build(nvars):
    old=json.loads(BASE.read_text());d=Circuit();mapping={};special={}
    if nvars==16:
        special[old['named_nodes']['b']]=d.mul(d.fixed('b_scale'),d.power(d.var('radix_root'),2))
    def clone(i):
        if i in special:return special[i]
        if i in mapping:return mapping[i]
        n=old['nodes'][i]
        if n['kind'] in ('add','sub','mul'):ans=d.op(n['kind'],clone(n['left']),clone(n['right']))
        else:ans=d.intern(n.copy())
        mapping[i]=ans;return ans
    # Copy only the eight-coordinate Jones ratio, not its natural finalizer.
    for name in ['b','B','q','ell','lambda','e','N','Gcap','R','U','Y','M','P','K','A','Wsmall','C','J','Q','D','E','F','Gp','H','I','a0','a1','margin']:
        d.save(name,clone(old['named_nodes'][name]))
    c,add,sub,mul,power=d.const,d.add,d.sub,d.mul,d.power
    get=lambda s:d.names[s]
    guards=['g0','s0','w0','phi','j0']
    if nvars==17:guards.insert(0,'epsilon')
    zz=[d.var('z'+str(j+1)) for j in range(len(guards)+1)]
    stack=c(1)
    for j,name in enumerate(guards):
        disc=add(mul(c(3),d.var(name)),c(2))
        factor=add(c(1),mul(c(4),disc,power(stack,2),power(zz[j],2)))
        stack=d.save('Cguard'+str(j+1),mul(stack,factor))
    disc=sub(mul(c(3),get('margin')),c(1))
    factor=add(c(1),mul(c(4),disc,power(stack,2),power(zz[-1],2)))
    stack=d.save('Cstar',mul(stack,factor))
    D=d.save('Ddiv',mul(get('J'),get('F')))
    T=d.save('Tdiv',add(mul(get('Q'),get('F')),mul(get('J'),sub(get('H'),get('C')))))
    i=add(d.var('i0'),c(1))
    nonzero=[i]+zz
    if nvars==16:nonzero.insert(1,d.var('radix_root'))
    Z=d.save('Znonzero',mul(*nonzero))
    S=d.save('Smerge',mul(Z,power(D,5)))
    rr=add(T,mul(D,d.var('residue')))
    D2=power(D,2)
    Tm=d.save('Tmerge',mul(sub(sub(power(rr,3),mul(D2,rr)),mul(D2,D)),add(power(rr,2),mul(c(23),D2))))
    # New signed separator: |Cstar| > sqrt(|Cstar|) at any possible zero.
    w1=d.save('weight1',stack)
    w2=d.save('weight2',mul(w1,add(power(get('P'),2),power(get('K'),2),c(2))))
    X=d.save('Xnorm',sub(mul(S,d.var('normroot')),Tm));S2=power(S,2)
    A0=d.save('B0norm',mul(S2,stack))
    A1=d.save('B1norm',mul(S2,power(w1,2),get('a0')))
    A2=d.save('B2norm',mul(S2,power(w2,2),get('a1')))
    X2=power(X,2)
    V=d.save('Vnorm',sub(sub(add(X2,A2),A0),A1));V2=power(V,2)
    fourXB=mul(c(4),X2,A2)
    W=d.save('Wnorm',sub(add(V2,fourXB),mul(c(4),A0,A1)))
    out=d.save('output',sub(power(W,2),mul(c(4),V2,fourXB)))
    body=d.pack(out)
    assert len(body['variables'])==nvars
    L=5**32
    formula='813056*5^32+10024' if nvars==16 else '406528*5^32+27512'
    exact=813056*L+10024 if nvars==16 else 406528*L+27512
    body.update(schema='proveit-compact-signed-v1',domain='unrestricted integers',nu=31,L=L,
                exact_degree=exact,exact_degree_formula=formula,guard_coordinates=guards,
                fixed_leaf_recipes='INDEX_CONSTANTS.json',coefficient_binding='../../coefficients/COEFFICIENT_BINDING.json',
                source_revision=PIN,source_arithmetic='package30 nu31 Jones ratio; package29 signed finalizer; new cofinal square radix and signed separator')
    return body

def evaluate(body,variables,fixed,p):
    vals=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='variable':v=variables[n['name']]
        elif k=='fixed':v=fixed[n['name']]
        elif k=='literal':v=n['value']
        else:
            a,b=vals[n['left']],vals[n['right']]
            v=a+b if k=='add' else a-b if k=='sub' else a*b
        vals.append(v%p)
    return vals[body['output']],{name:vals[i] for name,i in body['named_nodes'].items()}

def direct(body,base,x,p):
    C=1
    for j,name in enumerate(body['guard_coordinates'],1):
        C=C*(1+4*(3*x[name]+2)*C*C*x['z'+str(j)]**2)%p
    count=len(body['guard_coordinates'])+1
    C=C*(1+4*(3*base['margin']-1)*C*C*x['z'+str(count)]**2)%p
    D=base['J']*base['F']%p
    T=(base['Q']*base['F']+base['J']*(base['H']-base['C']))%p
    Z=x['i0']+1
    if len(body['variables'])==16:Z*=x['radix_root']
    for j in range(1,count+1):Z=Z*x['z'+str(j)]%p
    S=Z*pow(D,5,p)%p;r=(T+D*x['residue'])%p
    Tm=(r**3-D**2*r-D**3)*(r*r+23*D*D)%p
    X=(S*x['normroot']-Tm)%p
    w2=C*(base['P']**2+base['K']**2+2)%p
    A0=S*S*C%p;A1=S*S*C*C*base['a0']%p;A2=S*S*w2*w2*base['a1']%p
    V=(X*X+A2-A0-A1)%p;W=(V*V+4*X*X*A2-4*A0*A1)%p
    return (W*W-16*V*V*X*X*A2)%p

def degrees(body):
    # Degree-zero arbitrary coefficient leaves carry an unknown marker.
    # The only leading fixed leaf is b_scale, represented as a monomial.
    # Each row (total degree, integer coefficient, b_scale exponent, unknown).
    vals=[];unresolved=[]
    for ni,n in enumerate(body['nodes']):
        k=n['kind']
        if k=='literal':r=(0,n['value'],0,False)
        elif k=='variable':r=(1,1,0,False)
        elif k=='fixed':r=(0,1,1,False) if n['name']=='b_scale' else (0,0,0,True)
        else:
            a,b=vals[n['left']],vals[n['right']]
            if k=='mul':r=(a[0]+b[0],a[1]*b[1],a[2]+b[2],a[3] or b[3])
            elif a[0]>b[0]:r=a
            elif b[0]>a[0]:r=(b[0],b[1]*(1 if k=='add' else -1),b[2],b[3])
            elif a[2]==b[2]:r=(a[0],a[1]+(b[1] if k=='add' else -b[1]),a[2],a[3] or b[3])
            else:r=(a[0],0,0,True)
        vals.append(r)
        if not r[3] and r[1]==0 and r[0]>0:unresolved.append(ni)
    out=vals[body['output']]
    assert out[0]==body['exact_degree'],(out,body['exact_degree'])
    assert out[1]>0 and not out[3],out
    selected={name:dict(degree=vals[idx][0],coefficient_hex=hex(vals[idx][1]),b_scale_exponent=vals[idx][2],unknown=vals[idx][3])
              for name,idx in body['named_nodes'].items() if name in ['R','P','K','a0','a1','margin','Cstar','Smerge','Tmerge','weight2','B2norm','output']}
    return dict(exact_degree=out[0],leading_coefficient_hex=hex(out[1]),b_scale_exponent=out[2],
                positive_for_all_positive_b_scale=True,selected=selected,
                note='Structural leading-cancellation candidates off the output leader do not affect the positive certified output leader.')

def index_constants():
    c=json.loads(CONSTANTS.read_text());rows=[];s=0
    for r in c['coefficient_records']:
        bound=sum(abs(t['coefficient'])<<sum(a*b for a,b in zip(t['powers'],PORT_BITS))
                  for t in r['coefficient_polynomial_in_fixed_ports'])
        k=(bound+1).bit_length();assert bound+1<(1<<k)
        rows.append(dict(name=r['name'],strict_power2_bound=k));s=max(s,k)
    c.update(port_binding='../../coefficients/COEFFICIENT_BINDING.json',actual_port_bit_lengths=PORT_BITS,
             z_index=f'2^{s}',index_exponent=s,b_scale=f'2^({s+1}*(5^32+1))',
             b_scale_exponent=(s+1)*(5**32+1),parent_file='../upstream/30-quartic31/arithmetic/quartic31.json')
    c.pop('previous_index_bound',None)
    return c,dict(status='PASS',port_bits=PORT_BITS,index_exponent=s,records=rows)

def actual_fixed_leaves(constants,p):
    candidates=[HERE.parent/'coefficients',HERE.parent/'root_work/coefficients']
    directory=next((q for q in candidates if (q/'beta.bin').is_file()),None)
    if directory is None:raise FileNotFoundError('The complete frozen coefficient tuple is required for actual-instance checks.')
    raw={name:(directory/(name+'.bin')).read_bytes() for name in ('beta','K','MC','MF_source')}
    assert {k:hashlib.sha256(v).hexdigest() for k,v in raw.items()}==EXPECTED_PORT_SHA256
    ports=[int.from_bytes(raw[name],'little') for name in ('beta','K','MC','MF_source')]
    assert [x.bit_length() for x in ports]==PORT_BITS
    coeffs={}
    for r in constants['coefficient_records']:
        total=0
        for t in r['coefficient_polynomial_in_fixed_ports']:
            a=t['coefficient']
            for value,power_ in zip(ports,t['powers']):a=a*pow(value,power_,p)%p
            total=(total+a)%p
        coeffs[r['name']]=total
    z=pow(2,constants['index_exponent'],p);T=2*z%p;nu=constants['nu'];L=constants['L'];r=5**nu
    hs=[1,0,0,0,0]
    for exponent in [r]+[r-5**j for j in range(nu+1)]:
        w=pow(T,exponent,p)
        for k in range(1,5):hs[k]=(hs[k]+w*hs[k-1])%p
    baseline=pow(T,r,p)*hs[4]%p
    y=(z*baseline+sum(coeffs[c['name']]*pow(T,L-c['expo'],p) for c in constants['coefficient_records']))%p
    coeffs.update(z_index=z,y_index=y,b_scale=pow(2,constants['b_scale_exponent'],p))
    receipt=dict(prime=p,ports=[v%p for v in ports],z_index=z,y_index=y,b_scale=coeffs['b_scale'],
                 coefficient_hashes={name:hashlib.sha256((directory/(name+'.bin')).read_bytes()).hexdigest() for name in ('beta','K','MC','MF_source')})
    return coeffs,receipt

def checks(body):
    rng=random.Random(2026102216+len(body['variables']));comp=0
    old=json.loads(BASE.read_text())
    constants,_=index_constants();receipts=[]
    for p in (101,1009,1000003):
        fixed,receipt=actual_fixed_leaves(constants,p);receipts.append(receipt)
        for _ in range(30):
            x={s:rng.randrange(-9,10) for s in body['variables']}
            out,b=evaluate(body,x,fixed,p)
            assert out==direct(body,b,x,p);comp+=1
            # Independent inherited-source equality after the radix substitution.
            ofixed=dict(fixed);ofixed.setdefault('y_index',rng.randrange(p))
            ox={s:x.get(s,0) for s in old['variables']}
            if len(body['variables'])==16:
                ox['epsilon']=fixed['b_scale']*x['radix_root']**2-ofixed['y_index']-1
            _,ob=evaluate(old,ox,ofixed,p)
            assert all(b[k]==ob[k] for k in ('R','P','K','C','J','Q','D','F','H','a0','a1','margin'))
    norm_checks=0
    for _ in range(200):
        X,r0,r1,r2=[rng.randrange(-20,21) for _ in range(4)]
        A0,A1,A2=r0*r0,r1*r1,r2*r2;V=X*X+A2-A0-A1;W=V*V+4*X*X*A2-4*A0*A1
        ref=1
        for e0,e1,e2 in itertools.product((-1,1),repeat=3):ref*=X-e0*r0-e1*r1-e2*r2
        assert W*W-16*V*V*X*X*A2==ref;norm_checks+=1
    # Independent free-algebra multiplication also covers arbitrary signed
    # radicands, without pretending that they have real or rational roots.
    def multiply_radical_algebra(left,right,rad):
        ans=[0]*8
        for i,a in enumerate(left):
            for j,b in enumerate(right):
                term=a*b
                common=i&j
                for k in range(3):
                    if common&(1<<k):term*=rad[k]
                ans[i^j]+=term
        return ans
    signed_norm_checks=0
    for _ in range(200):
        X=rng.randrange(-20,21);rad=[rng.randrange(-30,31) for _ in range(3)]
        ref=[1]+[0]*7
        for e0,e1,e2 in itertools.product((-1,1),repeat=3):
            factor=[X]+[0]*7;factor[1]=-e0;factor[2]=-e1;factor[4]=-e2
            ref=multiply_radical_algebra(ref,factor,rad)
        A0,A1,A2=rad;V=X*X+A2-A0-A1;W=V*V+4*X*X*A2-4*A0*A1
        assert ref==[W*W-16*V*V*X*X*A2]+[0]*7
        signed_norm_checks+=1
    for C in range(-100,101):
        if abs(C)<=1:continue
        for P in range(-8,9):
            for K in range(-8,9):
                a0=(P*P-1)*K*K+1;V=P*P+K*K+1
                assert V*V>=abs(a0) and C*C>abs(C)
    for n in range(1,1201):assert any((t**3-t-1)*(t*t+23)%n==0 for t in range(n))
    return dict(status='PASS',scope='Finite arithmetic checks; ordinary proof in signed_section.tex supplies universality.',
                variables=len(body['variables']),operation_counts=body['operation_counts'],
                total_operations=sum(body['operation_counts'].values()),degree_certificate=degrees(body),
                modular_formula_and_inherited_source_comparisons=comp,eight_factor_norm_checks=norm_checks,
                arbitrary_signed_radicand_free_algebra_checks=signed_norm_checks,
                intersective_moduli_checked=1200,separator_checks=198*17*17,actual_fixed_instance_fingerprints=receipts)

def main():
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    for r in pins['files']:
        data=(SOURCE/r['path']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==r['sha256'],r['path']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob_sha1'],r['path']
    out=HERE/'generated';out.mkdir(exist_ok=True)
    constants,cert=index_constants()
    (out/'INDEX_CONSTANTS.json').write_text(json.dumps(constants,indent=2)+'\n')
    (out/'INDEX_BOUND_CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
    for n in (16,17):
        body=build(n);check=checks(body)
        (out/f'signed{n}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        (out/f'signed{n}_checks.json').write_text(json.dumps(check,indent=2)+'\n')
        print(n,check['total_operations'],body['exact_degree_formula'],body['operation_counts'])
    print('Index exponent',constants['index_exponent'],'radix-scale exponent',constants['b_scale_exponent'])

if __name__=='__main__':main()
