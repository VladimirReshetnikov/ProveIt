"""Independently authored arithmetic DAGs for the degree-958 positive form.

Only local JSON data is emitted. No upstream executable is imported or run.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent

class Circuit:
    def __init__(self):
        self.rows=[]
        self.cache={}
    def gate(self, operator, left, right, name=None):
        key=(operator, *(sorted((left,right),key=str) if operator in ('+','*') else (left,right)))
        if key in self.cache:
            return self.cache[key]
        name=name or 'r'+str(len(self.rows))
        self.rows.append([name,operator,left,right]); self.cache[key]=name
        return name
    def add(self,x,y,n=None): return self.gate('+',x,y,n)
    def sub(self,x,y,n=None): return self.gate('-',x,y,n)
    def mul(self,x,y,n=None): return self.gate('*',x,y,n)
    def square(self,x,n=None): return self.mul(x,x,n)

def build(carrier='full', modulus='Y', shifted_transport=False):
    dag=Circuit(); add,sub,mul,sq=dag.add,dag.sub,dag.mul,dag.square
    qm=mul('beta','J','qm'); q=add(qm,1,'q'); q2=sq(q,'q2'); q3=mul(q2,q,'q3')
    s0='s' if modulus=='none' else add('s',mul(3,q),'s0')
    X=mul('w',q,'X'); Y=mul(s0,q3,'Y'); E=mul(X,Y,'E')
    k=add('eta','zeta','k'); kY=mul(k,Y,'kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
    a=add(E,Y,'a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ell=mul(E,kY,'ell'); A=add(mul(ell,add(ell,k)),1,'A'); G=add(mul(Delta,c2),1,'G')
    ac=mul(a,c,'ac'); b0=add(X,ac,'b0'); qF=sub(q,'F','qF'); Cw=sub(qF,'alpha','Cw')
    R=add(mul(add(mul(qm,qF),'alpha'),sub(q2,1)),mul(add('MC',mul(q,'MF')),'J'),'R')
    Nk=sub(sub(k,mul('h',E)),R,'Nk') if modulus=='none' else None
    transport=mul(add('K0','w'),Cw,'transport'); zqm=mul('z',qm,'zqm')
    if shifted_transport:
        Nt=None; tright=add('F',zqm,'transport_right')
    else:
        Nt=sub(add(transport,qF),zqm,'Nt')
    I=mul('i',c2,'I'); DI=mul(Delta,I,'DI'); Q=sq(DI,'Q'); D=add(mul(I,DI),1,'D')
    d=sub(Q,1,'d'); v=mul(c,'T','v'); b=add(c,mul(R,D),'b'); Dv2=mul(D,sq(v),'Dv2'); b2=sq(b,'b2')
    IT=mul(I,'T','IT'); K=IT if carrier=='lean' else add(IT,1,'K')
    HK=mul(H,K,'HK'); L0=add(HK,1,'L0')
    if carrier=='lean': delta=ell
    else:
        delta=sub(ac,ell,'delta_short')
        if carrier=='full': delta=add(delta,mul(2,c),'delta_full')
    if modulus=='none':
        S=H; L=L0; W=add(b0,mul(H,add(add('t',b),delta)),'W')
    else:
        B=Y if modulus=='Y' else E
        S=mul(H,B,'S'); L=mul(B,L0,'L')
        u=sub(sub(k,R),1,'u')
        W=add(mul(B,b0),mul(H,add(mul(B,add(add('t',b),delta)),u)),'W')
    S2=sq(S,'S2'); dn=mul(d,mul(S2,A),'dn'); SQ=mul(S2,Q,'SQ')
    HP=mul(SQ,Dv2,'HP'); HU=mul(SQ,b2,'HU'); He=sub(add(HP,HU),S2,'He'); j=mul(4,mul(HP,HU),'j')
    W2=sq(W,'W2'); LG=mul(sq(L),G,'L2G'); Tr=mul(2,mul(d,add(W2,LG)),'Trace')
    Kn=sq(mul(d,sub(W2,LG)),'Knorm'); AA=mul(2,add(dn,He),'AA')
    cc=sub(sq(sub(dn,He)),j,'constant'); at=sub(Tr,AA,'at'); bt=sub(cc,Kn,'bt')
    co=mul(16,mul(dn,j),'coef'); vb=sub(co,mul(at,add(mul(at,Tr),mul(2,bt))),'vbar')
    ur=sub(sq(bt),mul(sq(at),Kn),'ur'); left=mul(ur,sub(mul(Tr,vb),ur),'norm_left'); right=mul(Kn,sq(vb),'norm_right')
    deg=({'lean':888,'full':892,'short':896}[carrier])+{'Y':64,'E':96,'none':0}[modulus]
    witnesses=['J','F','alpha','z']+(['h'] if modulus=='none' else [])+['i','T','s','w','eta','zeta','t']
    common={'carrier':carrier,'absorption_modulus':modulus,'domain':'strictly positive integers',
        'witnesses':witnesses,
        'fixed_numerals':['beta','K0','MC','MF'],'coefficient_binding_file':'COEFFICIENT_BINDING.json',
        'proof':'Y_ABSORPTION_PROOF.md'}
    comparisons=[[transport,tright],[left,right]] if shifted_transport else [[Nt,1],[left,right]]
    if Nk is not None: comparisons.insert(0,[Nk,1])
    system={**common,'source':dag.rows.copy(),'comparisons':comparisons,'exact_maximum_residual_degree':deg}
    if shifted_transport: packets=[system]
    else:
        N=sub(right,left,'N'); units=Nt if Nk is None else mul(Nk,Nt)
        out=sub(mul(units,add(N,1)),1,'out')
        packets=[system,{**common,'source':dag.rows.copy(),'output':out,'exact_degree':deg+(2 if Nk is None else 9)}]
    for packet in packets:
        needed={packet['output']} if 'output' in packet else set(x for pair in packet['comparisons'] for x in pair)
        for row in reversed(packet['source']):
            if row[0] in needed: needed.update(row[2:])
        packet['source']=[row for row in packet['source'] if row[0] in needed]
        packet['operations']=len(packet['source'])
        missing=set(common['witnesses']+common['fixed_numerals'])-needed
        if missing: raise ValueError('Unused supplied inputs: '+repr(missing))
    return packets

if __name__=='__main__':
    receipt=[]
    # The recommended release contains only undominated lean carriers.
    # build(carrier,modulus,...) remains available for comparison experiments.
    for carrier in ['lean']:
        for modulus in ['Y','none']:
            for shifted in [False,True]:
                for packet in build(carrier,modulus,shifted):
                    tag='product' if 'output' in packet else ('shifted_system' if shifted else 'system')
                    name=f'positive{len(packet["witnesses"])}_{modulus}_{carrier}_{tag}.json'
                    (ROOT/name).write_text(json.dumps(packet,indent=2)+'\n')
                    receipt.append({'file':name,'operations':packet['operations'],'degree':packet.get('exact_degree',packet.get('exact_maximum_residual_degree'))})
    (ROOT/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
