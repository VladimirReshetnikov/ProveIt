#!/usr/bin/env python3
"""New independent parser of reconstructed canonical streams; standard library only.
No upstream code, recipe, ant program or upstream schedule is imported or executed.
"""
import sys,json,hashlib,importlib.util,re
from pathlib import Path
from array import array
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
P=1000000007
NAMED={'Cu':pow(3,481238074400,P),'Cx':(pow(3,481238074400,P)-1)%P,'Cbase':pow(3,481238074181,P),'C198':pow(3,198,P),'EndpointK':pow(3,481225262775,P),'EndpointD':(pow(3,481238074400,P)-2)%P}
EXPECTED={2:(2307457,1153586,1153871,285,465,'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac'),1:(2307467,1153590,1153877,286,467,'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a')}

def need(t,msg):
    if not t:raise ValueError(msg)
def sample(s):return int.from_bytes(hashlib.sha256(s.encode()).digest()[:8],'big')%P

def coeff(s):
    need(type(s)is str and s.startswith('C:'),'coefficient syntax');k=s[2:]
    if re.fullmatch('-?[0-9]+',k):need(int(k)in[0,1,2,3,4,6,8,9],'unpaid numeral');return int(k)%P
    if k in NAMED:return NAMED[k]
    m=re.fullmatch('(tile|first|anchor):(0|[1-9][0-9]*)',k)
    need(m is not None and int(m[2])<(584 if m[1]=='anchor'else 576000),'coefficient range')
    return sample(s)

class Observer:
    def __init__(self,arity):
        self.arity=arity;self.env={};self.names=[];self.raw=None;self.v=array('I');self.deg=array('I');self.pairs=[];self.res=[];self.M=0;self.A=0;self.constants=set();self.hash=hashlib.sha256();self.final=None
        gates,M,A,eq,w,h=EXPECTED[arity];self.sos_start=gates-(3*eq-1);self.expected_eq=eq;self.squares=[];self.sumref=None
    def value(self,x):
        if type(x)is int:need(0<=x<len(self.v),'forward reference');return self.v[x]
        need(type(x)is str,'operand type')
        if x.startswith('C:'):self.constants.add(x);return coeff(x)
        need(x in self.env,'undeclared coordinate');return self.env[x]
    def degree(self,x):return self.deg[x]if type(x)is int else(0 if x.startswith('C:')else 1)
    def write(self,line):
        self.hash.update(line.encode());r=json.loads(line)
        if r[0]=='raw_positive':
            need(self.raw is None and not self.v,'raw declaration position');self.raw=r[1]
            need(self.raw==(['RawLeft','RawRight']if self.arity==2 else['RawInput']),'raw domains')
            for n in self.raw:self.env[n]=sample(n)-P//2
        elif r[0]=='positive':
            n=r[1];need(n not in self.env and not n.startswith('C:'),'coordinate collision');self.env[n]=sample(n)-P//2;self.names.append(n)
        elif r[0]=='residual_pair':
            _,i,a,b,section=r;need(i==len(self.pairs),'residual sequence');need(len(self.v)<=self.sos_start,'late component equation')
            self.pairs.append((a,b,section,max(self.degree(a),self.degree(b))));self.res.append((self.value(a)-self.value(b))%P)
        elif r[0]=='eq':
            need(self.final is None and r[2]=='C:0','final equation');self.final=r[1]
            need(self.value(r[1])==sum(z*z for z in self.res)%P and self.value(r[2])==0,'modular SOS')
        else:
            need(len(r)==4,'gate shape');i,op,a,b=r;need(type(i)is int and i==len(self.v),'gate index');need(op in['+','-','*'],'opcode')
            av,bv=self.value(a),self.value(b);ad,bd=self.degree(a),self.degree(b)
            if i>=self.sos_start:
                k=i-self.sos_start;m=self.expected_eq;need(len(self.pairs)==m,'all component equations present')
                if k<2*m:
                    q=k//2
                    if k%2==0:need(op=='-'and(a,b)==self.pairs[q][:2],'paid difference identity')
                    else:need(op=='*'and a==i-1 and b==i-1,'paid square identity');self.squares.append(i)
                else:
                    q=k-2*m
                    left=self.squares[0]if q==0 else i-1
                    need(op=='+'and a==left and b==self.squares[q+1],'SOS addition identity')
            self.v.append((av+bv if op=='+'else av-bv if op=='-'else av*bv)%P);self.deg.append(ad+bd if op=='*'else max(ad,bd))
            if op=='*':self.M+=1
            else:self.A+=1
    def finish(self):
        gates,M,A,eq,w,h=EXPECTED[self.arity]
        need((len(self.v),self.M,self.A,len(self.pairs),len(self.names),self.hash.hexdigest())==(gates,M,A,eq,w,h),'old canonical stream or ledger mismatch')
        need(self.final==gates-1,'final output location');need(len(self.constants)==1152598,'coefficient ledger')
        top=[i for i,p in enumerate(self.pairs)if p[3]==1152000];need(top==[64,178],'top residual positions')
        need(self.deg[self.final]==2304000,'final degree upper bound')
        need(set(n for n in self.env if n.startswith('Parent:'))=={'Parent:'+n for n in['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']},'five positive parent ports')
        return {'status':'PASS_NEW_INDEPENDENT_RECONSTRUCTION_OBSERVER','raw_arity':self.arity,'gates':gates,'M':M,'A':A,'positive_witnesses':w,'residual_pairs':eq,'one_final_equation':True,'source_sha256':h,'old_canonical_stream_identity_verified':True,'coefficient_labels':len(self.constants),'degree_upper_bound':2304000,'top_residual_positions':top,'all_SOS_operations_checked':True,'signed_off_solution_modular_SOS_checked':True}

def run():
    spec=importlib.util.spec_from_file_location('recovered_own_generator',ROOT/'merged_source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    result=[]
    for a in[2,1]:
        o=Observer(a);r=m.build(o,a);result.append(o.finish());need(r['source_sha256']==o.hash.hexdigest(),'author-observer digest')
    return {'status':'PASS','edition':'new recovery audit, not restored original audit bytes','source_file_sha256':hashlib.sha256((ROOT/'merged_source.py').read_bytes()).hexdigest(),'results':result,'scope':'Independent literal topology, domains, ledger, all SOS gates, degree upper bounds and canonical arithmetic identity. Exact leading-term proof in PROOF.md; inherited all-integer theorems are not newly reproved.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
