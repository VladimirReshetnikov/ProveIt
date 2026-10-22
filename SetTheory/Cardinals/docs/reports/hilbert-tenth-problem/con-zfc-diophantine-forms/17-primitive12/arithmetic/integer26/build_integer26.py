#!/usr/bin/env python3
"""Division-free 26-unrestricted-integer primitive-element circuit.

The script counts literal binary +,-,* gates (including numeral products),
prunes dead gates, and emits a self-contained JSON straight-line program.
The semantic correctness proof is in INTEGER26_PROOF.md.
"""
from pathlib import Path
from collections import Counter
import argparse, json, random

WITNESSES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
FIXED=['Bm1','Kconstant','MC','MF']

class Circuit:
    def __init__(self):
        self.gates=[]; self.cache={}; self.named={}
    def op(self,op,a,b):
        if isinstance(a,int) and isinstance(b,int):
            return {'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
        if op=='+' and a==0:return b
        if op=='+' and b==0:return a
        if op=='-' and b==0:return a
        if op=='-' and a==b:return 0
        if op=='*' and (a==0 or b==0):return 0
        if op=='*' and a==1:return b
        if op=='*' and b==1:return a
        if op in ('+','*') and str(a)>str(b):a,b=b,a
        key=(op,a,b)
        if key in self.cache:return self.cache[key]
        n=f'g{len(self.gates):03d}';self.gates.append([n,op,a,b]);self.cache[key]=n
        return n
    def add(self,a,b):return self.op('+',a,b)
    def sub(self,a,b):return self.op('-',a,b)
    def mul(self,a,b):return self.op('*',a,b)
    def sq(self,a):return self.mul(a,a)
    def name(self,n,a):self.named[n]=a;return a
    def packet(self,kind,outputs):
        need={x for x in outputs if isinstance(x,str)}
        for n,op,a,b in reversed(self.gates):
            if n in need:
                need.update(x for x in (a,b) if isinstance(x,str))
        gates=[g for g in self.gates if g[0] in need]
        cnt=Counter(g[1] for g in gates)
        p={'name':kind,'domain':'strictly positive integers','witnesses':WITNESSES,
           'fixed_numerals':FIXED,'mask_convention':'MF is the shifted F mask',
           'source':gates,'named_registers':{n:a for n,a in self.named.items() if a in need},
           'ledger':{'operations':len(gates),'multiplications':cnt['*'],
                     'additions_subtractions':cnt['+']+cnt['-'],
                     'all_gates_live':True,'all_ports_live':set(WITNESSES+FIXED)<=need}}
        return p

def build():
    c=Circuit();ad,su,mu,sq,nm=c.add,c.sub,c.mul,c.sq,c.name
    q=nm('q',ad(mu('Bm1','J'),1));q2=sq(q);q3=mu(q2,q)
    qF=su(q,'F');Cw=nm('Cword',su(qF,'alpha'))
    X=nm('X',mu('w',q));Y=nm('Y',mu('s',q3));E=nm('E',mu(X,Y))
    k=nm('k',ad('eta','zeta'));cc=nm('c',ad(mu(k,Y),'eta'));c2=sq(cc)
    a=nm('a',ad(E,Y));H=nm('H',ad(mu(4,a),3));Delta=nm('Delta',ad(sq(a),H))
    R=nm('R',ad(mu(ad(mu(su(q,1),qF),'alpha'),su(q2,1)),mu(ad('MC',mu(q,'MF')),'J')))
    Nk=nm('Nk',su(su(k,mu('h',E)),R))
    Nt=nm('Nt',su(ad(mu(ad('Kconstant','w'),Cw),qF),mu('z',su(q,1))))
    ell=nm('ell',mu(E,mu(k,Y)));A=nm('A',ad(1,mu(ell,ad(ell,k))))
    I=nm('I',mu('i',c2));D=nm('D',ad(1,mu(Delta,sq(I))))
    Q=nm('Q',sq(mu(Delta,I)));d=nm('d',su(Q,1))
    v=nm('v',mu(cc,'T'));Z=nm('Z',ad(cc,mu(R,D)))
    e=nm('e',su(mu(Q,ad(mu(D,sq(v)),sq(Z))),1))
    B=nm('B',mu(2,mu(Q,mu(v,Z))))
    b=nm('b',ad(X,mu(a,cc)));G=nm('G',ad(mu(Delta,c2),1))
    g=nm('gamma_bound',ad(cc,X));u=nm('tau_bound',ad(ell,k))
    C=nm('Cbound',ad(ad(sq(v),D),Z));r=nm('f_bound',mu(mu(ad(a,2),ad(sq('i'),1)),c2))
    C2=nm('ratio_bound',ad(ad(mu(cc,ad(sq('T'),1)),cc),mu(R,r)))
    at=nm('weight_tau',ad(mu(2,g),1));S=nm('Sbound',ad(mu(at,u),g))
    wy=nm('weight_y',ad(mu(mu(Q,C),S),1))
    wf=nm('weight_f',ad(ad(mu(2,mu(wy,C2)),S),1))
    # Elements of Q[f]/(f^2-D) are pairs (constant,f coefficient).
    def padd(x,y):return (ad(x[0],y[0]),ad(x[1],y[1]))
    def psub(x,y):return (su(x[0],y[0]),su(x[1],y[1]))
    def pscale(x,k):return (mu(x[0],k),mu(x[1],k))
    def pmul(x,y):
        return (ad(mu(x[0],y[0]),mu(D,mu(x[1],y[1]))),
                ad(mu(x[0],y[1]),mu(x[1],y[0])))
    def psq(x):return (ad(sq(x[0]),mu(D,sq(x[1]))),mu(2,mu(x[0],x[1])))
    # zeta = Ht+b-H*wf*f-H*tau, represented as z0+z1*tau.
    zz0=(ad(mu(H,'t'),b),su(0,mu(H,wf)));zz1=su(0,mu(H,at))
    zs0=padd(psq(zz0),(mu(A,sq(zz1)),0));zs1=pscale(zz0,mu(2,zz1))
    qy2=sq(mu(H,wy));rr=(e,su(0,B))
    K0=psub(pscale(padd(zs0,(G,0)),d),pscale(rr,qy2));K1=pscale(zs1,d)
    four_d2_G=mu(4,mu(sq(d),G))
    E0=psub(padd(psq(K0),pscale(psq(K1),A)),pscale(zs0,four_d2_G))
    E1=psub(pscale(pmul(K0,K1),2),pscale(zs1,four_d2_G))
    N=psub(psq(E0),pscale(psq(E1),A))
    P=nm('primitive_norm',su(sq(N[0]),mu(D,sq(N[1]))))
    system=c.packet('integer26_system',[Nk,Nt,P]);system['comparisons']=[[Nk,1],[Nt,1],[P,0]]
    system['residual_exact_degrees']=[13,4,5248]
    # P is a square modulo 4, because each successive norm preserves squares.
    output=su(mu(mu(Nk,Nt),ad(1,P)),1)
    product=c.packet('integer26_product',[output]);product['output']=output;product['exact_degree']=5265
    sos=ad(ad(sq(su(Nk,1)),sq(su(Nt,1))),sq(P))
    psos=c.packet('integer26_sos',[sos]);psos['output']=sos;psos['exact_degree']=10496
    return tuple(substitute_integer26(p) for p in (system,product,psos))


def substitute_integer26(packet):
    guards=['J','F','alpha','z','s','eta','zeta']
    witnesses=[]; pre=[]
    for name in guards:
        x,y,z=[name+'_'+a for a in ('x','y','z')]
        witnesses += [x,y,z]
        pre += [[name+'_x2','*',x,x], [name+'_xx','+',name+'_x2',x],
                [name+'_y2','*',y,y], [name+'_xy','+',name+'_xx',name+'_y2'],
                [name+'_z2','*',z,z], [name+'_xyz','+',name+'_xy',name+'_z2'],
                [name,'+',name+'_xyz',1]]
    witnesses += ['h','i_raw','T','w_raw','t']
    pre += [['i_twice','*',2,'i_raw'],['i','+','i_twice',1],['w','*','w_raw','w_raw']]
    packet['source']=pre+packet['source'];packet['witnesses']=witnesses
    packet['domain']='unrestricted integers'
    packet['source_pin']='f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
    packet['coefficient_binding']={'manifest_from_package_root':'INSTANCE.json',
        'default_recipe_from_package_root':'compiler/PRUNED_T4_CONSTANTS.json',
        'fallback':'14-integer29 inherited06-blank67 tuple',
        'scope':'Whole tuples only; the signed canonical transfer must cover odd i and square w.'}
    cnt=Counter(g[1] for g in packet['source'])
    packet['ledger'].update(operations=len(packet['source']),multiplications=cnt['*'],
        additions_subtractions=cnt['+']+cnt['-'])
    known=set(packet['witnesses']+packet['fixed_numerals'])
    for n,op,a,b in packet['source']:
        if n in known or op not in ('+','-','*'):raise ValueError('bad gate')
        if not all(isinstance(x,int) or x in known for x in (a,b)):raise ValueError('undefined input')
        known.add(n)
    outputs=[packet['output']] if 'output' in packet else [a for row in packet['comparisons'] for a in row if isinstance(a,str)]
    need=set(outputs)
    for n,op,a,b in reversed(packet['source']):
        if n in need:need.update(x for x in (a,b) if isinstance(x,str))
    if not all(n in need for n,_,_,_ in packet['source']):raise ValueError('dead gate')
    if not set(packet['witnesses']+packet['fixed_numerals'])<=need:raise ValueError('dead input')
    if len(witnesses)!=26:raise ValueError('wrong variable count')
    return packet

def evaluate(packet,values,modulus=None):
    vals=dict(values)
    for n,op,a,b in packet['source']:
        x=a if isinstance(a,int) else vals[a];y=b if isinstance(b,int) else vals[b]
        r=x+y if op=='+' else x-y if op=='-' else x*y
        vals[n]=r if modulus is None else r%modulus
    return vals

def exact_degree_line(packet):
    """Supplementary exact modular degree computation on one generic line.

    Dense finite-field multiplication avoids expansion in12 variables.
    This checks the independently proved leading-degree predictions; it is not
    itself the universal degree proof.
    """
    prime=65521
    def ar(x):return [x]
    def plus(x,y,sgn=1):
        z=[((x[j] if j<len(x) else 0)+sgn*(y[j] if j<len(y) else 0))%prime for j in range(max(len(x),len(y)))]
        while len(z)>1 and z[-1]==0:z=z[:-1]
        return z
    def multiply(x,y):
        z=[0]*(len(x)+len(y)-1)
        for j,xx in enumerate(x):
            for k,yy in enumerate(y):z[j+k]+=xx*yy
        z=[a%prime for a in z]
        while len(z)>1 and z[-1]==0:z=z[:-1]
        return z
    rng=random.Random(120026)
    vals={n:[rng.randrange(1,18),rng.randrange(1,18)] for n in packet['witnesses']}
    vals.update(dict(zip(FIXED,map(ar,[31,127,10,45]))))
    for n,op,a,b in packet['source']:
        x=ar(a) if isinstance(a,int) else vals[a];y=ar(b) if isinstance(b,int) else vals[b]
        vals[n]=plus(x,y) if op=='+' else plus(x,y,-1) if op=='-' else multiply(x,y)
    if 'output' in packet:return [len(vals[packet['output']])-1]
    return [len(plus(vals[a],ar(b) if isinstance(b,int) else vals[b],-1))-1 for a,b in packet['comparisons']]

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'generated26');p.add_argument('--degree-check',action='store_true');args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    packets=build();receipt=[]
    for obj in packets:
        if not obj['ledger']['all_ports_live']:raise RuntimeError('dead supplied port')
        (args.out/(obj['name']+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
        entry={'name':obj['name'],'ledger':obj['ledger'],'degree':obj.get('exact_degree',obj.get('residual_exact_degrees'))}
        if args.degree_check:
            entry['modular_line_degrees']=exact_degree_line(obj)
            expected=[obj['exact_degree']] if 'output' in obj else obj['residual_exact_degrees']
            if entry['modular_line_degrees']!=expected:raise ValueError('degree mismatch')
        receipt.append(entry)
    (args.out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
