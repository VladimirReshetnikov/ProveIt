#!/usr/bin/env python3
"""Check a finite derived-schema proof of gate exchange.

This is a finite syntactic certificate, not a Lean build or a machine calibration.
K, S, exchange are re-derived from the imported restricted-rho8 proof terms;
the small outer certificate uses these checked schemas, GEN, distribution, MP.
"""
from pathlib import Path
import argparse, functools, hashlib, json, re, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
from check_restricted_exchange import parse_expression

def require(v,msg):
    if not v:raise ValueError(msg)

def check_library(source):
    clean=re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    found=list(re.finditer(r'^(?:private )?def (\w+)\b',clean,re.M));defs={}
    for j,m in enumerate(found):
        name=m.group(1)
        if name=='liftRight':break
        piece=clean[m.end():found[j+1].start() if j+1<len(found)else len(clean)]
        head,body=piece.split(':=',1);params=[]
        for q in re.finditer(r'\(([\w\s]+)\s*:\s*A\)',head):params+=q.group(1).split()
        defs[name]=(params,parse_expression(body.strip()))
    terms=[['v','a'],['v','b'],['v','c']];tids={tuple(t):i for i,t in enumerate(terms)}
    proofs=[];pids={}
    def I(a,b):
        t=('i',a,b)
        if t not in tids:tids[t]=len(terms);terms.append(list(t))
        return tids[t]
    @functools.lru_cache(None)
    def subterm(a,b):return a==b or (terms[b][0]=='i'and(subterm(a,terms[b][1])or subterm(a,terms[b][2])))
    def put(p):
        t=tuple(p)
        if t not in pids:pids[t]=len(proofs);proofs.append(p)
        return pids[t]
    def row(a,b,c,u):
        require(subterm(u,a),'rho8 domination is not justified by subterm inclusion')
        return put(['row',I(I(I(c,u),a),I(I(a,c),I(b,c))),a,b,c,u])
    def mp(major,minor):
        a,b=proofs[major][1],proofs[minor][1]
        require(terms[a][0]=='i'and terms[a][1]==b,'invalid imported MP')
        return put(['mp',terms[a][2],major,minor])
    def term(e,env):
        if e[0]=='name':return env[e[1]]
        require(e[0]=='imp','bad imported term');return I(term(e[1],env),term(e[2],env))
    def proof(e,env):
        require(e[0]=='app'and e[1][0]=='name','bad imported proof')
        name,args=e[1][1],e[2]
        if name=='rules.row':return row(*(term(a,env)for a in args[:4]))
        if name=='rules.mp':return mp(proof(args[0],env),proof(args[1],env))
        require(name in defs and args[0]==('name','rules'),'unknown imported theorem')
        n=len(defs[name][0]);require(len(args)in(n+1,n+2),'imported theorem arity')
        return instantiate(name,tuple(term(a,env)for a in args[1:n+1]))
    @functools.lru_cache(None)
    def instantiate(name,args):
        params,body=defs[name];require(len(params)==len(args),'theorem arity')
        return proof(body,dict(zip(params,args)))
    targets={'k':I(0,I(1,0)),
             's':I(I(0,I(1,2)),I(I(0,1),I(0,2))),
             'exchange':I(I(0,I(1,2)),I(1,I(0,2)))}
    ends={name:instantiate(name,(0,1)if name=='k'else(0,1,2))for name in targets}
    for name,end in ends.items():require(proofs[end][1]==targets[name],'wrong schema '+name)
    for i,p in enumerate(proofs):
        if p[0]=='row':
            _,con,a,b,c,u=p
            require(subterm(u,a)and con==I(I(I(c,u),a),I(I(a,c),I(b,c))),'bad rho8 data')
        else:
            _,con,major,minor=p
            require(major<i and minor<i and terms[proofs[major][1]]==['i',proofs[minor][1],con],'bad MP data')
    data={'terms':terms,'proofs':proofs,'ends':ends}
    return {'PASS':True,'schemas':list(targets),'proof_rows':len(proofs),'terms':len(terms),
            'rho8_leaves':sum(p[0]=='row'for p in proofs),'MP_rows':sum(p[0]=='mp'for p in proofs),
            'all_side_conditions_by_subterm':True,
            'certificate_sha256':hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest(),
            'source_sha256':hashlib.sha256(source.encode()).hexdigest()}

class Kernel:
    def __init__(self, distribution='ordinary'):
        self.terms=[];self.tids={};self.proofs=[];self.pids={}
        require(distribution in ('ordinary','exchanged'),'bad distribution orientation')
        self.distribution=distribution
    def term(self,t):
        t=tuple(t)
        if t not in self.tids:self.tids[t]=len(self.terms);self.terms.append(list(t))
        return self.tids[t]
    def I(self,a,b):return self.term(('i',a,b))
    def U(self,c,a):return self.term(('u',c,a))
    def var(self,a):return self.term(('var',a))
    def put(self,p):
        t=tuple(p)
        if t not in self.pids:self.pids[t]=len(self.proofs);self.proofs.append(p)
        return self.pids[t]
    def concl(self,p):return self.proofs[p][1]
    def schema(self,name,args):
        I=self.I;a,b=args[:2]
        if name=='k':return I(a,I(b,a))
        c=args[2]
        if name=='s':return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
        require(name=='exchange','bad schema');return I(I(a,I(b,c)),I(b,I(a,c)))
    def lemma(self,name,*args):return self.put(['lemma',self.schema(name,args),name,*args])
    def mp(self,f,a):
        t=self.terms[self.concl(f)];require(t[0]=='i'and t[1]==self.concl(a),'bad outer MP')
        return self.put(['mp',t[2],f,a])
    def gen(self,c,p):return self.put(['gen',self.U(c,self.concl(p)),c,p])
    def dist(self,c,a,b):
        ua,uab,ub=self.U(c,a),self.U(c,self.I(a,b)),self.U(c,b)
        if self.distribution=='ordinary':
            return self.put(['dist',self.I(ua,self.I(uab,ub)),c,a,b])
        q=self.put(['qdist',self.I(uab,self.I(ua,ub)),c,a,b])
        return self.mp(self.lemma('exchange',uab,ua,ub),q)
    def liftU(self,c,p):
        a,b=self.terms[self.concl(p)][1:];g=self.gen(c,p)
        d=self.dist(c,a,b)
        swap=self.lemma('exchange',self.U(c,a),self.U(c,self.I(a,b)),self.U(c,b))
        return self.mp(self.mp(swap,d),g)
    # Temporary proof terms support hypotheses; all hypotheses are abstracted
    # into checked K/S applications before becoming final certificate rows.
    def const(self,p):return ('const',p,self.concl(p),frozenset())
    def hyp(self,name,t):return ('hyp',name,t,frozenset((name,)))
    def app(self,f,a):
        ty=self.terms[f[2]];require(ty[0]=='i'and ty[1]==a[2],'bad lambda application')
        return ('app',(f,a),ty[2],f[3]|a[3])
    def abstr(self,x,t,p):
        if x not in p[3]:return self.app(self.const(self.lemma('k',p[2],t)),p)
        if p[0]=='hyp':
            require(p[1]==x and p[2]==t,'bad hypothesis')
            i=self.mp(self.mp(self.lemma('s',t,self.I(t,t),t),self.lemma('k',t,self.I(t,t))),self.lemma('k',t,t))
            return self.const(i)
        require(p[0]=='app','bad abstraction term');f,a=p[1]
        return self.app(self.app(self.const(self.lemma('s',t,a[2],p[2])),self.abstr(x,t,f)),self.abstr(x,t,a))
    def compile(self,p):
        require(not p[3],'undischarged hypothesis')
        if p[0]=='const':return p[1]
        require(p[0]=='app','unexpected temporary proof');return self.mp(*(self.compile(x)for x in p[1]))
    def contragate(self,V,Q1,Q2,q21,F):
        G1=self.I(self.I(V,Q1),F);vq2=self.I(V,Q2)
        g=self.hyp('g',G1);h=self.hyp('h',vq2);v=self.hyp('v',V)
        q1=self.app(self.const(q21),self.app(h,v))
        vq1=self.abstr('v',V,q1)
        result=self.app(g,vq1)
        return self.compile(self.abstr('g',G1,self.abstr('h',vq2,result)))
    def audit(self):
        for i,p in enumerate(self.proofs):
            kind,con=p[:2]
            if kind=='lemma':require(con==self.schema(p[2],p[3:]),'schema mismatch')
            elif kind=='mp':
                f,a=p[2:];require(f<i and a<i and self.terms[self.concl(f)]==['i',self.concl(a),con],'data MP mismatch')
            elif kind=='gen':
                c,a=p[2:];require(a<i and con==self.U(c,self.concl(a)),'data GEN mismatch')
            elif kind=='dist':
                c,a,b=p[2:];require(con==self.I(self.U(c,a),self.I(self.U(c,self.I(a,b)),self.U(c,b))),'data distribution mismatch')
            elif kind=='qdist':
                c,a,b=p[2:];require(con==self.I(self.U(c,self.I(a,b)),self.I(self.U(c,a),self.U(c,b))),'data exchanged distribution mismatch')
            else:raise ValueError(kind)

def check_gate(distribution='ordinary'):
    k=Kernel(distribution);S,P,V=map(k.var,('S','P','V'));F=k.term(('constant',1));binder='c'
    E1=k.I(S,k.I(P,F));E2=k.I(P,k.I(S,F));Q1=k.U(binder,E1);Q2=k.U(binder,E2)
    q12=k.liftU(binder,k.lemma('exchange',S,P,F));q21=k.liftU(binder,k.lemma('exchange',P,S,F))
    g12=k.contragate(V,Q1,Q2,q21,F);g21=k.contragate(V,Q2,Q1,q12,F)
    G1=k.I(k.I(V,Q1),F);G2=k.I(k.I(V,Q2),F)
    require(k.concl(g12)==k.I(G1,G2)and k.concl(g21)==k.I(G2,G1),'wrong gate conclusion')
    k.audit()
    return {'format':'gate-quantified-exchange-v1','terms':k.terms,'proofs':k.proofs,
            'endpoints':{'old_implies_new':g12,'new_implies_old':g21},
            'old_gate':'(V -> forall c, (S -> (P -> false))) -> false',
            'new_gate':'(V -> forall c, (P -> (S -> false))) -> false',
            'base_schemas':['derived K','derived S','derived exchange',distribution+' quantifier distribution'],
            'rules':['MP','generalization of closed proofs']}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'evidence');a=p.parse_args()
    require(__debug__,'Run with Python assertions enabled')
    lib=check_library((ROOT/'vendor/RestrictedImplication.lean').read_text())
    cert=check_gate();qcert=check_gate('exchanged');a.output.mkdir(parents=True,exist_ok=True)
    data=(json.dumps(cert,indent=2)+'\n').encode();(a.output/'gate_exchange_certificate.json').write_bytes(data)
    qdata=(json.dumps(qcert,indent=2)+'\n').encode();(a.output/'gate_exchange_q_certificate.json').write_bytes(qdata)
    receipt={'status':'PASS','imported_schema_check':lib,'gate_proof_rows':len(cert['proofs']),
             'gate_terms':len(cert['terms']),'certificate_sha256':hashlib.sha256(data).hexdigest(),
             'exchanged_distribution_gate_proof_rows':len(qcert['proofs']),
             'exchanged_distribution_gate_terms':len(qcert['terms']),
             'exchanged_distribution_certificate_sha256':hashlib.sha256(qdata).hexdigest(),
             'new_machine_claim':False,'kernel_checked':False,
             'scope':'Universal fixed proof templates for gate equivalence; no iPRA end-to-end Con(PA) calibration.'}
    (a.output/'gate_exchange_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
