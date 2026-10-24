#!/usr/bin/env python3
"""Independent exact source, arithmetic-interface and positivity audit.

Reads only JSON. It imports no compiler and performs no mathematical search.
Compositional integer-polynomial identities establish finite transcription;
the accompanying ordinary proofs establish the infinite semantic theorem.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path


def need(p,why):
    if not p: raise ValueError(why)


class Ring:
    def __init__(self): self.keys=[];self.cache={}
    def node(self,key):
        key=tuple(key)
        if key not in self.cache:self.cache[key]=len(self.keys);self.keys.append(key)
        return self.cache[key]
    def c(self,n):return self.node(('c',n))
    def v(self,n):return self.node(('v',n))
    def add(self,a,b):
        if a==self.c(0):return b
        if b==self.c(0):return a
        if self.keys[a][0]==self.keys[b][0]=='c':return self.c(self.keys[a][1]+self.keys[b][1])
        return self.node(('a',*sorted((a,b))))
    def sub(self,a,b):
        if b==self.c(0):return a
        if a==b:return self.c(0)
        if self.keys[a][0]==self.keys[b][0]=='c':return self.c(self.keys[a][1]-self.keys[b][1])
        return self.node(('s',a,b))
    def mul(self,a,b):
        if a==self.c(0) or b==self.c(0):return self.c(0)
        if a==self.c(1):return b
        if b==self.c(1):return a
        if self.keys[a][0]==self.keys[b][0]=='c':return self.c(self.keys[a][1]*self.keys[b][1])
        return self.node(('m',*sorted((a,b))))
    def sum(self,seq):
        a=self.c(0)
        for b in seq:a=self.add(a,b)
        return a
    def product(self,seq):
        a=self.c(1)
        for b in seq:a=self.mul(a,b)
        return a
    def poly(self,terms,env):
        need(all(t['coefficient']>=0 for t in terms),'nonnegative coefficient needed')
        return self.sum(self.product([self.c(t['coefficient'])]+[env[x] for x in t['monomial']]) for t in terms)
    def split(self,terms,env):
        return tuple(self.poly([{'coefficient':abs(t['coefficient']),'monomial':t['monomial']}
                    for t in terms if (t['coefficient']>0)==sign],env) for sign in (True,False))
    def pa(self,p,q):return self.add(p[0],q[0]),self.add(p[1],q[1])
    def pm(self,p,q):return self.add(self.mul(p[0],q[0]),self.mul(p[1],q[1])),self.add(self.mul(p[0],q[1]),self.mul(p[1],q[0]))
    def psum(self,seq):
        a=self.c(0),self.c(0)
        for b in seq:a=self.pa(a,b)
        return a
    def pprod(self,seq):
        a=self.c(1),self.c(0)
        for b in seq:a=self.pm(a,b)
        return a
    def psos(self,seq):return self.psum(self.pm(p,p) for p in seq)
    def sos(self,seq):return self.sum(self.mul(p,p) for p in seq)
    def load(self,nodes,env,absolute=False):
        vals=[]
        for i,n in enumerate(nodes):
            need(n[0] in ('c','v','a','s','m'),'DAG opcode')
            if n[0]=='c':v=self.c(abs(n[1]) if absolute else n[1])
            elif n[0]=='v':
                need(0<=n[1]<len(env),'variable index');v=env[n[1]]
            else:
                need(0<=n[1]<i and 0<=n[2]<i,'DAG acyclicity')
                fn=self.add if n[0]=='a' or (absolute and n[0]=='s') else self.sub if n[0]=='s' else self.mul
                v=fn(vals[n[1]],vals[n[2]])
            vals.append(v)
        return vals


def canonical_branches(r,horn,base):
    answer=[]
    for branch in horn['branches']:
        name=branch['name'];env=dict(base)
        env.update(p=base['a'] if name=='mp' else base['b'] if name=='gen' else r.c(0),
                   q=r.c(0),v=base['b'] if name=='mp' else r.c(0))
        defined=set(env)
        for j,w in enumerate(branch['wires']):
            need(all(t['coefficient']>0 and set(t['monomial'])<=defined for t in w['value']),name+' nonnegative triangular constructor')
            expected=defaultdict(int);expected[(w['name'],)]=1
            for t in w['value']:expected[tuple(t['monomial'])]-=t['coefficient']
            actual={tuple(t['monomial']):t['coefficient'] for t in branch['quadratic_residuals'][j]}
            need({m:c for m,c in expected.items() if c}==actual,name+' constructor defining row')
            env[w['name']]=r.poly(w['value'],env);defined.add(w['name'])
        residuals=branch['quadratic_residuals'][len(branch['wires']):]
        target='q' if name=='mp' else 'v';last=residuals[-1]
        need([t for t in last if target in t['monomial']]==[{'monomial':[target],'coefficient':1}],name+' monic label')
        env[target]=r.poly([{'coefficient':-t['coefficient'],'monomial':t['monomial']} for t in last if target not in t['monomial']],env)
        guard=residuals[:1] if name=='bundle' else []
        for residual in residuals[len(guard):]:
            left,right=r.split(residual,env);need(left==right,name+' exact label projection')
        answer.append({'name':name,'env':env,'guards':guard,'removed':len(branch['wires'])})
    need(len(answer)==12,'twelve rule branches')
    return answer


def expected_row(r,horn,env,paired):
    branches=canonical_branches(r,horn,{s:env[s] for s in ('a','b','c','d')})
    one=r.c(1);M=r.add(env['M0'],one)
    beta=[]
    for at,ix in [('i',env['i']),('next',r.add(env['i'],one))]:
        d=r.add(r.mul(r.add(ix,one),env['y']),one)
        beta.append((env['x'],r.add(r.mul(env['x.'+at+'.quotient'],d),env['x.'+at+'.remainder'])))
    alternatives=[]
    for branch in branches:
        b=branch['env']
        update=(r.mul(env['x.next.remainder'],r.add(r.mul(b['v'],M),one)),
                r.product([env['x.i.remainder'],r.add(r.mul(b['p'],M),one),r.add(r.mul(b['q'],M),one)]))
        residuals=[r.split(g,b) for g in branch['guards']]+[update]
        alternatives.append(r.psos(residuals) if paired else r.sos(r.sub(*q) for q in residuals))
    if paired:return r.pa(r.pprod(alternatives),r.psos(beta))
    return r.add(r.product(alternatives),r.sos(r.sub(*q) for q in beta))


def run(root):
    names=['source/horn_shared_source.json','equations/local_row.json','equations/semantic_certificate.json']
    horn,row,raw=[json.loads((root/name).read_text()) for name in names]
    src=raw['source_binding'];signed=src['encoded_signed_row'];r=Ring()
    rownames=['N','x','y','M0','i','a','b','c','d','x.i.remainder','x.i.quotient','x.next.remainder','x.next.quotient']
    need(row['variables']==signed['variables']==rownames,'exact eight-column row interface')
    renv=[r.v(('row',j)) for j in range(13)];renvnames=dict(zip(rownames,renv))
    rv=r.load(row['nodes'],renv);sv=r.load(signed['nodes'],renv)
    need(tuple(rv[j] for j in row['output'])==expected_row(r,horn,renvnames,True),'original positive-pair row')
    need(sv[signed['output']]==expected_row(r,horn,renvnames,False),'signed row is the same Horn/beta polynomial')
    need(all(n[0] in ('v','c','a','m') and (n[0]!='c' or n[1]>=0) for n in row['nodes']),'original row natural syntax')
    vars_=raw['variable_names'];unrestricted=set(raw['unrestricted_inputs'])
    need(vars_[:4]==['N minus one','x','y','M0'],'outer convention')
    genv=[r.v(('global',j)) for j in range(len(vars_))]
    vals=r.load(raw['nodes'],genv);G=lambda j:vals[j]
    def variable(prefix):
        ids=[j for j,name in enumerate(vars_) if name.startswith(prefix)]
        need(len(ids)==1,'unique variable prefix '+prefix)
        return genv[ids[0]],ids[0]
    def natural(i,why):need(i not in unrestricted,why+' must remain natural')
    N=r.add(genv[0],r.c(1));x,y,M0=genv[1:4];U=G(src['U'])
    bounds=[N]*4+[y,U,y,U]
    need([G(j) for j in src['coordinate_bounds']]==bounds,'heterogeneous N/y/U bounds')
    need(len(src['encoded_coordinates'])==8,'eight encoded columns')
    encoded=[]
    for j,actual in enumerate(src['encoded_coordinates']):
        a,idx=variable('encoded row coordinate '+str(j)+' minus one')
        natural(idx,'encoded positive-column predecessor');encoded.append(r.add(a,r.c(1)))
        need(G(actual)==encoded[-1],'encoded column positive shift')
    upper=[N,x,y,M0,N]+bounds;coded=[N,x,y,M0,G(src['index'])]+encoded
    need([G(i) for i in src['upper_environment']]==upper,'upper environment')
    need([G(i) for i in src['encoded_environment']]==coded,'encoded environment')
    ub=r.load(signed['nodes'],upper,True)[signed['output']]
    value=r.load(signed['nodes'],coded)[signed['output']]
    need(G(src['upper_e'])==ub and G(src['upper_f'])==r.c(0),'absolute-circuit majorant')
    need(G(src['encoded_e'])==value and G(src['encoded_f'])==r.c(0),'signed encoded evaluation')
    branches=canonical_branches(r,horn,{s:N for s in ('a','b','c','d')})
    H=r.sum(b['env'][s] for b in branches for s in ('p','q','v'))
    need(G(src['label_majorant'])==H,'padded monotone label bound')
    height=r.add(r.product([r.c(2),H,N]),r.c(1));need(G(src['height_exponent'])==height,'binary carrier exponent')
    ledger=raw['call_ledger'];eqs={(G(a),G(b),label) for a,b,label in raw['equalities']};expected_eqs=[]
    def eq(a,b,label):
        need((a,b,label) in eqs,'missing exact equality '+label)
        expected_eqs.append((a,b,label))
    def call(kind,args):
        matches=[item for item in ledger if item['kind']==kind and [G(j) for j in item['arguments']]==args]
        need(len(matches)==1,'unique '+kind+' call')
        z=matches[0]['result'];return G(z) if isinstance(z,int) else tuple(G(j) for j in z)
    power=lambda n,k:call('deferred_positive_power',[n,k])
    binom=lambda n,k:call('positive_binomial',[n,k])
    fact=lambda n:call('positive_factorial',[n])
    mp=power(r.c(2),height);need(G(src['height_power'])==mp,'carrier output binding');eq(M0,mp,'padded binary height')
    L=r.sum([ub,r.c(0),N]);need(G(src['scale_argument'])==L,'prime-lift absolute scale')
    T=fact(L);need(G(src['T'])==T,'scale factorial')
    Q=r.add(power(r.add(r.mul(r.add(N,r.c(1)),T),r.c(1)),N),r.c(2));need(G(src['Q'])==Q,'CRT Q')
    tn=power(T,N);nf=fact(N);ch=binom(r.add(Q,N),N);mod=G(src['modulus'])
    eq(r.mul(T,Q),r.add(mod,r.c(1)),'CRT positive modulus predecessor')
    _,B=call('divmod',[r.product([tn,nf,ch]),mod]);need(G(src['B'])==B,'CRT product binding')
    need(G(src['N_factorial'])==nf,'N factorial binding')
    need(len(src['coordinate_certificates'])==8,'eight range certificates')
    for j,cert in enumerate(src['coordinate_certificates']):
        need(G(cert['encoded'])==encoded[j] and G(cert['bound'])==bounds[j],'range coordinate role')
        chosen=binom(encoded[j],r.add(bounds[j],r.c(1)));need(G(cert['choose'])==chosen,'range binomial call')
        eq(chosen,r.mul(B,G(cert['quotient'])),'cancelled-factorial coordinate certificate')
    eq(r.add(r.mul(r.add(G(src['index']),r.c(1)),T),r.c(1)),r.mul(B,G(src['index_quotient'])),'encoded row index')
    for ix,want in [(r.c(0),r.add(M0,r.c(2))),(N,r.c(1))]:
        divisor=r.add(r.mul(r.add(ix,r.c(1)),y),r.c(1));_,rem=call('divmod',[x,divisor]);eq(rem,want,'beta endpoint')
    rq,rqi=variable('row evaluation.signed_q.');need(rqi in unrestricted,'row quotient must allow either sign')
    eq(r.add(value,r.mul(B,rq)),r.c(0),'encoded row evaluation congruence')

    # These checks reconstruct the arithmetic interfaces, not the Pell backend.
    countbin=countfact=countdiv=0
    for rec in ledger:
        kind=rec['kind']
        if kind=='positive_binomial':
            countbin+=1;tag='binomial'+str(countbin);n,k=map(G,rec['arguments']);out=G(rec['result'])
            h,hi=variable(tag+'.high.');rem,ri=variable(tag+'.remainder.');rs,rsi=variable(tag+'.remainder_slack.');os,osi=variable(tag+'.output_slack.')
            outv,oi=variable(tag+'.output.');need(out==outv,'binomial output input')
            for i in (oi,ri,rsi,osi):natural(i,'binomial residue/slack')
            need(hi in unrestricted,'binomial high quotient sign inference')
            q=r.add(power(r.c(2),n),r.c(1));num=power(r.add(q,r.c(1)),n);den=power(q,k)
            eq(num,r.add(r.mul(den,r.add(r.mul(q,h),out)),rem),tag+'.digit_division')
            eq(den,r.sum([rem,rs,r.c(1)]),tag+'.remainder_bound');eq(q,r.sum([out,os,r.c(1)]),tag+'.digit_bound')
        elif kind=='positive_factorial':
            countfact+=1;tag='factorial'+str(countfact);n,=map(G,rec['arguments']);out=G(rec['result'])
            f0,fi=variable(tag+'.output.');natural(fi,'factorial positive predecessor');need(out==r.add(f0,r.c(1)),'positive factorial output')
            rem,ri=variable(tag+'.remainder.');slack,si=variable(tag+'.slack.');natural(ri,'factorial remainder');natural(si,'factorial slack')
            radius=power(r.add(n,r.c(2)),r.add(n,r.c(2)));ch=binom(r.add(radius,n),n);num=power(r.add(radius,r.c(1)),n)
            eq(r.add(num,ch),r.sum([r.mul(ch,out),rem,r.c(1)]),tag+'.ceiling');eq(ch,r.sum([rem,slack,r.c(1)]),tag+'.remainder_bound')
        elif kind=='divmod':
            countdiv+=1;n,d=map(G,rec['arguments']);q,rem=map(G,rec['result']);start=rec['before'][0]
            need(q==genv[start] and rem==genv[start+1],'division coordinates')
            need(start in unrestricted,'division quotient sign inference');natural(start+1,'division remainder');natural(start+2,'division slack')
            eq(n,r.add(r.mul(q,d),rem),'division equation');eq(d,r.add(r.add(rem,genv[start+2]),r.c(1)),'positive divisor/remainder bound')
    need((countbin,countfact,countdiv)==(11,2,3),'arithmetic call inventory')
    prefix=[(G(a),G(b),label) for a,b,label in raw['equalities'][:raw['batch']['prefix_equalities']]]
    need(Counter(prefix)==Counter(expected_eqs),'complete source-prefix equality multiset; no hidden additional condition')
    need(Counter(item['kind'] for item in ledger)==Counter({'deferred_positive_power':40,'positive_binomial':11,'positive_factorial':2,'divmod':3}),
         'complete macro ledger inventory')

    # Unconditional lower bounds; no power/factorial correctness assumption.
    lower=[];depends=[]
    for node in raw['nodes']:
        op=node[0]
        if op=='c':a=node[1];deps=set()
        elif op=='v':a=None if node[1] in unrestricted else 0;deps={node[1]}
        else:
            left,right=lower[node[1]],lower[node[2]];deps=depends[node[1]]|depends[node[2]]
            if left is None or right is None:a=None
            elif op=='a':a=min(2,left+right)
            elif op=='m':a=min(2,left*right) if left>=0 and right>=0 else None
            else:a=None
        lower.append(a);depends.append(deps)
    powers=[item for item in ledger if item['kind']=='deferred_positive_power']
    need(len(powers)==40,'forty positive power calls')
    for j,item in enumerate(powers):
        n,k=item['arguments']
        need(lower[n] is not None and lower[n]>=1,'unconditional positive base '+str(j))
        need(lower[k] is not None and lower[k]>=1,'unconditional positive exponent '+str(j))
        need(not ((depends[n]|depends[k])&unrestricted),'power argument depends on an unguarded signed input')
        m0,mi=variable('power'+str(j+1)+'.output_minus_one.');natural(mi,'positive power predecessor')
        need(G(item['result'])==r.add(m0,r.c(1)),'positive power output shift')
    # The source sign restorations do not feed any power argument.
    derived=[i for i,name in enumerate(vars_) if (name.startswith('binomial') and '.high.' in name)
             or name.startswith('coordinate divisibility quotient') or name.startswith('index divisibility quotient')]
    need(len(derived)==20 and set(derived)<=unrestricted,'twenty derived-sign quotients')
    for i in derived:
        need(all(i not in depends[n] and i not in depends[k] for item in powers for n,k in [item['arguments']]),'sign restoration used circularly')
    return {'status':'PASS','local_columns':8,'horn_branches':12,'signed_row_and_positive_pair':'exact compositional identities',
            'upper_bound':'absolute circuit, checked at full heterogeneous bound vector',
            'arithmetic_interfaces':{'power':40,'binomial':11,'factorial':2,'divmod':3},
            'complete_source_prefix_equalities':len(prefix),
            'unconditionally_positive_power_bases':40,'unconditionally_positive_power_exponents':40,
            'derived_sign_quotients_not_in_power_arguments':20,
            'sha256':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names},
            'scope':'Exact finite source/interfaces and domain licenses; ordinary source, CRT and Pell theorems remain explicit mathematical proofs.'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('package',type=Path,nargs='?',default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path)
    args=ap.parse_args();result=run(args.package)
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(payload)
    print(payload)


if __name__=='__main__':main()
