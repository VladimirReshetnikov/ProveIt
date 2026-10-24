#!/usr/bin/env python3
"""Shared binary evaluators for the literal joint-sign polynomial family."""
from pathlib import Path
import hashlib,json
from collections import Counter

ROOT=Path(__file__).resolve().parent
FAMILY=['joint19_degree88','joint20_degree32','joint21_degree20','joint22_degree16','joint23_degree12','joint25_octic']

class DAG:
    def __init__(self):self.rows=[];self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y):x,y=y,x
        key=(op,x,y)
        if key in self.cache:return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(r[0]==name for r in self.rows):raise ValueError(name)
        self.rows.append([name,op,x,y]);self.cache[key]=name;return name
    def add(self,x,y,name=None):return self.gate('+',x,y,name)
    def sub(self,x,y,name=None):return self.gate('-',x,y,name)
    def mul(self,x,y,name=None):return self.gate('*',x,y,name)
    def sq(self,x,name=None):return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for n,op,x,y in reversed(self.rows):
            if n in needed:needed.update((x,y))
        return [r for r in self.rows if r[0] in needed],needed

def build(name):
    source_path=ROOT.parent/'joint'/(name+'.json');src=json.loads(source_path.read_text())
    d=DAG();add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    p={v:v for v in src['variables']};named={}
    def bind(n,v):named[n]=v;return v
    J=bind('J',add(mul(3,'J3'),1,'J'));qm=bind('qm',mul('beta',J,'qm'));q=bind('q',add(qm,1,'q'))
    q2=bind('q2',sq(q,'q2'));q3=bind('q3',mul(q2,q,'q3'))
    W=bind('W',add(mul(12,'w3'),4,'W'));X=bind('X',mul(q,W,'X'))
    Y=bind('Y',mul(add(mul(2,'v_scale'),1),q3,'Y'))
    qF=bind('qF',sub(q,'F','qF'));C=bind('C',sub(qF,'alpha','C'))
    fo=bind('fo',mul('f','o','fo'))
    V=bind('V',p.get('V') or sub(fo,'c','V'))
    c2=bind('c2',sq('c','c2'));Irest=bind('Irest',mul(add(mul(2,'r'),1),c2,'Irest'))
    I=bind('I',p.get('I') or Irest)
    E=bind('E',p.get('E') or mul(X,Y,'E'))
    a=bind('a',p.get('a') or add(E,Y,'a'))
    aE=bind('aE',sub(a,E,'aE') if 'a' in p else Y)
    cj=bind('cj',mul('c','j','cj'));cjmV=bind('cjmV',sub(cj,V,'cjmV'))
    hE=bind('hE',mul('h',E,'hE'));k=bind('k',add(add(cjmV,hE),1,'k'))
    kY=bind('kY',mul(k,Y,'kY'))
    eta=bind('eta',p.get('eta') or sub('c',kY,'eta'))
    cmEta=bind('cmEta',sub('c',eta,'cmEta') if 'eta' in p else kY)
    kmEta=bind('kmEta',sub(k,eta,'kmEta'))
    H=bind('H',add(mul(4,a),3,'H'));Delta=bind('Delta',add(sq(a),H,'Delta'))
    G=bind('G',add(mul(qm,qF),'alpha','G'))
    R=bind('R',add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R'))
    Ucone=bind('Ucone',mul('cone_A','F','Ucone'));Wcone=bind('Wcone',mul('cone_B',C,'Wcone'))
    det=bind('det',sub(mul(Ucone,Wcone),sq(sub(sub(q,Ucone),Wcone)),'det'))
    T=bind('T',mul(eta,p['zeta'] if 'zeta' in p else kmEta,'T'))
    pos=bind('pos',add(add(add(1,sq('pair_pos1')),sq('pair_pos2')),mul('pair_pos3',add('pair_pos3',1)),'pos'))
    Ecm=bind('Ecm',mul(E,cmEta,'Ecm'))
    mainroot=bind('mainroot',add(add(X,mul(a,'c')),mul('gamma',H),'mainroot'))
    I2=bind('I2',sq(I,'I2'));f2m=bind('f2m',sub(sq('f'),1,'f2m'))
    strongprod=bind('strongprod',mul(Delta,f2m,'strongprod'))
    V2=bind('V2',sq(V,'V2'));y2=bind('y2',sq('y','y2'))
    rowmap={
      0:sub(aE,Y,'r0'),1:sub(E,mul(X,aE),'r1'),
      2:sub(cmEta,mul(k,aE),'r2'),
      3:sub(sub(sq('tau'),mul(Ecm,add(k,Ecm))),1,'r3'),
      4:sub(sub(sq(mainroot),mul(Delta,c2)),1,'r4'),
      5:sub(cjmV,R,'r5'),
      6:sub(sub(mul(add('K0',W),C),'F'),mul('z',qm),'r6'),
      7:sub(add(V,'c'),fo,'r7'),8:sub(I,Irest,'r8'),
      9:sub(I2,strongprod,'r9')}
    reduced=name=='joint22_degree16'
    rowmap[10]=sub(add(mul(strongprod if reduced else I2,sub(V2,y2)),y2),1,'r10')
    pairinside=bind('pairinside',add(sub(sub(sq('pair_root'),det),T),1,'pairinside'))
    rowmap[11]=sub(sub(mul(det,T),sq(pairinside)),pos,'r11')
    deleted=set()
    if 'V' not in p:deleted.add(7)
    if 'I' not in p:deleted.add(8)
    if 'a' not in p:deleted.add(0)
    if 'E' not in p:deleted.add(1)
    if 'eta' not in p:deleted.add(2)
    residuals=[rowmap[i] for i in range(11) if i not in deleted]
    source_indices=[i for i in range(11) if i not in deleted]
    if 'zeta' in p:
        residuals.append(sub('zeta',kmEta,'restore_zeta'));source_indices.append('restore_zeta')
    residuals.append(rowmap[11]);source_indices.append(11)
    squares=[sq(r) for r in residuals];out=squares[0]
    for s in squares[1:]:out=add(out,s)
    rows,needed=d.live([out]);core,_=d.live(residuals)
    if not set(src['variables']+src['fixed_numerals'])<=needed:raise ValueError('Dead input '+name)
    if len(residuals)!=src['residual_count']:raise ValueError('Residual count '+name)
    return dict(name=name+'_shared_dag',domain=src['domain'],witnesses=src['variables'],fixed_numerals=src['fixed_numerals'],
       source=rows,residuals=residuals,source_row_indices=source_indices,output=out,operations=len(rows),system_operations=len(core),
       operation_breakdown=dict(Counter(r[1] for r in rows)),named_registers={n:v for n,v in named.items() if v in needed},
       exact_degree=src['exact_degree'],source_polynomial='../joint/'+name+'.json',source_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
       coefficient_binding=src['coefficient_binding'],equivalence='Literal equality to the source sum of squared residuals; no row reduction or finalizer change.',
       count_convention='Every live binary +,-,* gate, including scalar multiplication and squaring. Fixed numeral leaves and shared register reuse are free.')

def main():
    result=[]
    for n in FAMILY:
        p=build(n);(ROOT/(n+'_dag.json')).write_text(json.dumps(p,indent=2)+'\n')
        result.append({k:p[k] for k in ['name','exact_degree','operations','system_operations','operation_breakdown']})
    (ROOT/'BUILD.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
