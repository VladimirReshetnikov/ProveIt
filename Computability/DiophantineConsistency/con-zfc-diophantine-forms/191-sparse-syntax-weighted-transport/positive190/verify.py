#!/usr/bin/env python3
"""Independent finite graph, sparse-algebra, degree and numeral verification.

No producer module or inherited checker is imported. Unbounded Pell and
logical claims are established in the ordinary proof, not by these checks.
"""
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PARENT_HASH='6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449'


def require(test, message):
    if not test:
        raise ValueError(message)


class Ring:
    def __init__(self,names,weights=None):
        self.names=tuple(names)
        self.n=len(names)
        self.weights=weights or [1]*self.n

    def constant(self,c):
        return {(0,)*self.n:c} if c else {}

    def var(self,name):
        ex=[0]*self.n;ex[self.names.index(name)]=1
        return {tuple(ex):1}

    def add(self,p,q,sign=1):
        d=dict(p)
        for e,c in q.items():d[e]=d.get(e,0)+sign*c
        return {e:c for e,c in d.items() if c}

    def mul(self,p,q):
        d=collections.defaultdict(int)
        for e,c in p.items():
            for f,v in q.items():
                d[tuple(a+b for a,b in zip(e,f))]+=c*v
        return {e:c for e,c in d.items() if c}

    def scale(self,c,p):
        return {e:c*v for e,v in p.items() if c*v}

    def power(self,p,n):
        out=self.constant(1)
        for unused in range(n):out=self.mul(out,p)
        return out

    def product(self,*xs):
        out=self.constant(1)
        for x in xs:out=self.mul(out,x)
        return out

    def quotient(self,p,index,degree):
        d={}
        for e,c in p.items():
            if e[index]>=degree:
                f=list(e);f[index]-=degree;d[tuple(f)]=c
        return d

    def degree(self,p):
        return max((sum(a*b for a,b in zip(e,self.weights)) for e in p),default=-1)

    def top(self,p):
        n=self.degree(p)
        return {e:c for e,c in p.items() if sum(a*b for a,b in zip(e,self.weights))==n}

    def eval_row(self,row,env):
        name,op,x,y=row
        a=self.constant(x) if isinstance(x,int) else env[x]
        b=self.constant(y) if isinstance(y,int) else env[y]
        if op=='+':return self.add(a,b)
        if op=='-':return self.add(a,b,-1)
        if op=='*':return self.mul(a,b)
        raise ValueError('Invalid operation')


def check_graph(graph,parent):
    require(graph['witnesses']==parent['witnesses'],'Changed quantifiers')
    require(graph['fixed_numerals']==parent['fixed_numerals'],'Changed fixed ports')
    require(graph['domain']=='strictly positive integers','Changed domain')
    rows=graph['source'];known=set(graph['witnesses']+graph['fixed_numerals'])
    table={}
    for row in rows:
        require(len(row)==4,'Bad row')
        name,op,x,y=row
        require(name not in known,'Repeated register')
        require(op in '+-*','Bad operator')
        for arg in (x,y):require(type(arg) is int or (type(arg) is str and arg in known),'Unbound reference')
        table[name]=row;known.add(name)
    live={graph['output']}
    for name,op,x,y in reversed(rows):
        if name in live:
            live.update(a for a in (x,y) if isinstance(a,str))
    require(live==known,'Dead gate, port or variable')
    require(len(rows)==120==graph['operations'],'Wrong operation count')
    counts=dict(collections.Counter(row[1] for row in rows))
    require(counts=={'*':75,'+':24,'-':21}==graph['operation_breakdown'],'Wrong operation split')
    modified={
        'L':['L','*','wc_b2','UE'],
        'center':['center','-','wc_raw_center','wc_Omega'],
        'RG':['RG','*','M2','wc_G16'],
    }
    for row in parent['source']:
        require(table[row[0]]==modified.get(row[0],row),'Changed inherited row: '+row[0])
    for row in [
        ['wc_b2','*','cTR','cTR'],
        ['wc_raw_center','-','n','LBt'],
        ['wc_G16','*',16,'Dg'],
    ]:require(table[row[0]]==row,'Changed new carrier or norm row')
    new_names=set(table)-{row[0] for row in parent['source']}
    require(len(new_names)==33,'Unexpected gate')
    center_names=new_names-{'wc_b2','wc_raw_center','wc_G16'}
    require(len(center_names)==30,'Unexpected center gate')
    return [row for row in rows if row[0] in center_names]


def center_algebra(center_rows):
    ring=Ring(['A','Ybar','k','U','b','c'],[4,2,1,5,4,2])
    A,Y,k,U,b,c=[ring.var(x) for x in ring.names]
    one=ring.constant(1)
    Aminus=ring.add(A,one,-1)
    ell=ring.product(k,Y,ring.add(ring.add(A,Y,-1),one,-1))
    E=ring.add(one,ring.mul(ell,ring.add(ell,k)))
    Delta=ring.add(ring.power(A,2),one,-1)
    a=ring.product(Delta,ring.power(U,2),E)
    f=ring.add(one,ring.scale(2,a))
    V=ring.add(ring.mul(f,b),c,-1)
    G=ring.mul(E,ring.add(one,a))
    F=ring.mul(E,V)
    q1=ring.quotient(F,0,1);q3=ring.quotient(F,0,3)
    require(all(v%2==0 for v in q3.values()),'Q3 not even')
    expected=ring.mul(U,ring.add(ring.add(ring.scale(4,ring.mul(A,F)),ring.scale(2,q1),-1),{e:v//2 for e,v in q3.items()},-1))
    env={'Am1':Aminus,'k':k,'qY':Y,'V0kk':ring.add(ell,k),'U':U,'cTR':b,'Dtau':E,'c':c,'V':V}
    for row in center_rows:env[row[0]]=ring.eval_row(row,env)
    require(env['wc_Omega']==expected,'Actual center differs from polynomial-quotient identity')
    require(len(expected)==84 and ring.degree(expected)==59,'Unexpected center support/degree')
    defect=ring.add(ring.power(expected,2),ring.scale(16,ring.product(G,ring.power(V,2))),-1)
    lead=ring.scale(8,ring.product(ring.power(A,6),ring.power(Y,8),ring.power(k,8),ring.power(U,6),ring.power(b,2),ring.add(ring.power(A,2),ring.scale(6,ring.power(Y,4)),-1)))
    require(len(defect)==594,'Unexpected norm-defect support')
    require(ring.degree(defect)==94 and ring.top(defect)==lead,'Wrong norm-defect degree/leader')
    return ring,expected,defect,lead


def substitute(source_poly,source_ring,target_ring,mapping):
    result={}
    for ex,c in source_poly.items():
        term=target_ring.constant(c)
        for name,power in zip(source_ring.names,ex):
            if power:term=target_ring.mul(term,target_ring.power(mapping[name],power))
        result=target_ring.add(result,term)
    return result


def actual_degree(parent,ring,center,defect_top):
    names=parent['witnesses']+parent['fixed_numerals']
    r=Ring(names,[1]*10+[0]*4)
    env={n:r.var(n) for n in names}
    # The parent registers used below have nonzero leading terms at each step.
    # Exact top polynomials, rather than a maximum-degree rule, detect leading
    # cancellations. The final parent's norm cancellation is not used here.
    needed={'Q','Mtot','Dtau','U','cTR','c','V','Am1','qY','Bt','Hp','P1mu2'}
    found={}
    for row in parent['source']:
        value=r.eval_row(row,env)
        require(bool(value),'Vanishing intermediate leader '+row[0])
        env[row[0]]=r.top(value)
        if row[0] in needed:found[row[0]]=env[row[0]]
        if row[0]=='Mtot':break
    mapping={'A':found['Am1'],'Ybar':found['qY'],'k':env['k'],'U':found['U'],'b':found['cTR'],'c':found['c']}
    actual_defect=substitute(defect_top,ring,r,mapping)
    actual_center=substitute(ring.top(center),ring,r,mapping)
    require(r.degree(actual_center)==59,'Center top cancels after actual substitution')
    require(r.degree(actual_defect)==94,'Defect top cancels after actual substitution')
    full_leader=r.product(found['Q'],r.power(found['Mtot'],2),actual_defect)
    q0=r.mul(r.var('beta'),r.var('J'))
    k0=r.add(r.var('eta'),r.var('zeta'))
    form=r.scale(9*2**11,r.product(
        r.power(q0,74),r.power(r.var('w'),18),r.power(r.var('s'),52),
        r.power(r.var('i'),10),r.power(k0,32),r.power(r.add(q0,r.var('F'),-1),2),
        r.add(r.power(r.var('w'),2),r.scale(6,r.power(r.var('s'),2)),-1)))
    require(full_leader==form,'Incorrect complete degree190 form')
    require(r.degree(form)==190 and len(form)==198,'Actual degree190 leader absent')
    degrees={'Q':r.degree(found['Q']),'M':r.degree(found['Mtot']),'E':r.degree(found['Dtau']),'U':r.degree(found['U']),'b':r.degree(found['cTR']),'V':r.degree(found['V'])}
    require(degrees=={'Q':72,'M':12,'E':14,'U':5,'b':4,'V':36},'Incorrect free-chart cut degrees')
    L=r.product(r.power(found['cTR'],2),found['U'],found['Dtau'])
    Z0=r.scale(-1,r.product(found['P1mu2'],found['Hp'],L,found['Bt']))
    require(r.degree(L)==27 and r.degree(Z0)==41,'Weighted carrier degrees wrong')
    bounds=[72+2*41,72+12+41+59,72+2*12+94,2*12+46,2*(12+59)]
    require(bounds==[154,184,190,70,142],'Wrong final decomposition')
    return degrees,bounds,len(form)


def coefficients(graph,parent):
    ports=parent['coefficient_binding']['ports']
    require(graph['coefficient_binding']['ports']==ports,'Changed coefficient tuple')
    require(graph['coefficient_binding']['tuple']==parent['coefficient_binding']['tuple'],'Changed calibration identity')
    require(graph['coefficient_binding']['path']=='coefficients','Wrong coefficient path')
    require(graph['coefficient_binding']['endianness']=='little','Wrong byte order')
    values={};receipts={}
    for name,meta in ports.items():
        payload=(ROOT/'coefficients'/meta['file']).read_bytes()
        require(hashlib.sha256(payload).hexdigest()==meta['gzip_sha256'],'Compressed numeral hash '+name)
        raw=gzip.decompress(payload)
        require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Raw numeral hash '+name)
        v=int.from_bytes(raw,'little')
        require(v.bit_length()==meta['bits'],'Numeral bit length '+name)
        values[name]=v
        receipts[name]={'bits':v.bit_length(),'raw_bytes':len(raw),'raw_sha256':meta['raw_sha256']}
    require(values['beta']==2**590069-1,'Radix definition')
    require(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'Scalar box')
    require(values['K0']>0,'K0 positivity')
    return receipts


def main():
    raw=(ROOT/'inherited/parent87.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PARENT_HASH,'Parent pin mismatch')
    parent=json.loads(raw);graph=json.loads((ROOT/'equation.json').read_text())
    center_rows=check_graph(graph,parent)
    ring,center,defect,leader=center_algebra(center_rows)
    degrees,bounds,leader_count=actual_degree(parent,ring,center,leader)
    numeral_receipts=coefficients(graph,parent)
    # Every center operator is challenged independently; unchanged parent rows
    # and the three carrier/norm changes are authenticated by exact comparisons.
    rejected=0
    for i,row in enumerate(center_rows):
        for op in '+-*':
            if op==row[1]:continue
            mutant=copy.deepcopy(center_rows);mutant[i][1]=op
            try:center_algebra(mutant)
            except (ValueError,KeyError):rejected+=1
            else:raise ValueError('Undetected center operator corruption')
    require(rejected==60,'Incomplete corruption suite')
    receipt={
        'status':'passed','variables':10,'domain':'strictly positive integers',
        'operations':120,'operation_breakdown':graph['operation_breakdown'],
        'exact_degree':190,'center_monomials':len(center),'norm_defect_monomials':len(defect),
        'norm_defect_weighted_degree':94,'complete_leader_monomials':leader_count,
        'component_degrees':degrees,'decomposition_degree_bounds':bounds,
        'rejected_center_operator_mutations':rejected,'numerals':numeral_receipts,
        'equation_sha256':hashlib.sha256((ROOT/'equation.json').read_bytes()).hexdigest(),
        'scope':'Finite artifact checks. Unbounded arithmetic and logical equivalence are ordinary proofs.'
    }
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
