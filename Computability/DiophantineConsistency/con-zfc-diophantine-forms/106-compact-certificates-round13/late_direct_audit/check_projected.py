#!/usr/bin/env python3
"""Independent exact audit of projected eight-column direct certificates.

Candidate JSON and source text are inert data. No candidate builder or upstream
executable is imported. Arithmetic audits reuse only our independent checker.
"""
import argparse
import ast
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'direct_audit'))
from check_exact import Audit,need,add,mul,sub,num,key

class Expressions:
    def __init__(self):self.nodes=[];self.cache={}
    def node(self,x):
        x=tuple(x)
        if x not in self.cache:self.cache[x]=len(self.nodes);self.nodes.append(x)
        return self.cache[x]
    def c(self,n):return self.node(('c',n))
    def v(self,n):return self.node(('v',n))
    def plus(self,a,b):
        if a==self.c(0):return b
        if b==self.c(0):return a
        x,y=self.nodes[a],self.nodes[b]
        if x[0]==y[0]=='c':return self.c(x[1]+y[1])
        return self.node(('add',*sorted([a,b])))
    def times(self,a,b):
        if a==self.c(0) or b==self.c(0):return self.c(0)
        if a==self.c(1):return b
        if b==self.c(1):return a
        x,y=self.nodes[a],self.nodes[b]
        if x[0]==y[0]=='c':return self.c(x[1]*y[1])
        return self.node(('mul',*sorted([a,b])))
    def sq(self,a):return self.times(a,a)
    def sum(self,xs):
        r=self.c(0)
        for x in xs:r=self.plus(r,x)
        return r
    def prod(self,xs):
        r=self.c(1)
        for x in xs:r=self.times(r,x)
        return r
    def pa(self,a,b):return self.plus(a[0],b[0]),self.plus(a[1],b[1])
    def pm(self,a,b):return self.plus(self.times(a[0],b[0]),self.times(a[1],b[1])),self.plus(self.times(a[0],b[1]),self.times(a[1],b[0]))
    def ps(self,a):return self.plus(self.sq(a[0]),self.sq(a[1])),self.prod([self.c(2),a[0],a[1]])

def expected_rules(X,e):
    ad,mu,sq=X.plus,X.times,X.sq;zero,one,two,three,four=map(X.c,range(5))
    def I(a,b):
        s=ad(a,b);return ad(mu(two,mu(s,ad(s,one))),mu(four,b))
    def A(a,b):return ad(I(a,b),two)
    def M(a,b):return ad(I(a,b),one)
    def E(a,b):return ad(I(a,b),three)
    def neg(a):return I(a,one)
    def Exists(a,b):return neg(A(a,neg(b)))
    def req(x,k,f):return A(x,I(f,neg(A(x,I(f,neg(M(x,k)))))))
    def clos(x,y,k,f):
        subset=A(k,I(M(k,x),M(k,y)));tail=I(subset,req(y,k,f));tail=neg(A(x,tail));tail=neg(A(x,I(f,tail)));return A(y,I(M(y,k),tail))
    def bundle(x,y,z):
        nks=A(z,I(clos(x,y,z,z),neg(req(y,z,z))));vrel=I(M(x,y),A(z,M(x,y)));return neg(I(vrel,nks))
    a,b,c,d=[e[n] for n in ['a','b','c','d']]
    codes=[Exists(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),I(E(c,a),I(M(c,b),M(a,b))),I(Exists(a,A(a,b)),b),I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),I(I(I(c,d),a),I(I(a,c),I(b,c))),bundle(a,b,c)]
    gp,gn=X.ps((ad(sq(c),mu(a,b)),mu(c,ad(a,b))));guard=(gp,ad(gn,sq(ad(d,one))))
    names=['rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle']
    out=[('truth',[zero,zero,zero],None)]+[(name,[zero,zero,code],guard if name=='bundle' else None) for name,code in zip(names,codes)]
    out += [('mp',[a,I(a,b),b],None),('gen',[b,zero,A(a,b)],None)]
    return out

class ProjectedAudit(Audit):
    def expression_reader(self,X,environment):
        cut={a[1]:X.v(name) for name,a in environment.items() if a[0]=='v'};cache={}
        def at(a):
            if a[0]=='c':return X.c(a[1])
            i=a[1]
            if i in cut:return cut[i]
            if i in cache:return cache[i]
            need(i in self.gates,'undeclared source leaf')
            p=self.gate_rhs(i);op=self.gate_ops[i]
            if op=='mul':
                need(len(p)==1,'invalid product gate');mon,c=next(iter(p.items()))
                cache[i]=X.prod([X.c(c)]+[at(['v',j]) for j in mon])
            else:
                values=[]
                for mon,c in p.items():
                    if mon:values.extend([at(['v',mon[0]])]*c)
                    else:values.append(X.c(c))
                need(op=='add' and len(values)==2,'invalid addition gate')
                cache[i]=X.plus(*values)
            return cache[i]
        return at
    def check_bindings(self):
        b=self.binding;p=b['parameters'];ex,at=self.expander([p['m']])
        N,x,y,M0=[at(p[k]) for k in ['t','x','y','M0']]
        need(N==add(self.v('N0'),num(1)) and y==add(M0,num(2),self.v('y0')),'outer parameterization')
        names={'a','b','c','d','S','Sp','u','vq'}
        need(b['row_coordinate_count']==8 and set(b['upper'])==set(b['encoded_columns'])==names,'wrong projected coordinates')
        for n in names:
            upper=at(b['upper'][n]);lower=at(b['range_lower_arguments'][n])
            want=N if n in 'abcd' else y if n in ('S','Sp') else x
            need(upper==want and lower==(y if n in ('S','Sp') else add(want,num(1))),'projected bound role '+n)
            need(at(b['encoded_columns'][n])==add(self.v('CRT.column.'+n),num(1)),'positive encoded column')
        D=add(num(1),mul(add(N,num(1)),y))
        need(ex(self.named['endpoint.initial'])==sub(x,add(M0,num(2),mul(add(y,num(1)),self.v('endpoint.u0')))),'initial endpoint')
        need(ex(self.named['endpoint.final'])==sub(x,add(num(1),mul(D,self.v('endpoint.ut')))),'final endpoint')
        self.check_source();self.check_majorants();self.counts['exact_projected_bindings']=True
    def check_source(self):
        b=self.binding;p=b['parameters'];detail=b['encoded_source'];env={k:v for k,v in p.items() if k!='m'}|b['encoded_columns']
        need(detail['environment']==env and detail['index']==b['encoded_index'],'encoded source environment binding')
        X=Expressions();at=self.expression_reader(X,env|{'index':b['encoded_index']});e={k:X.v(k) for k in env};index=X.v('index')
        rules=expected_rules(X,e);need([r['name'] for r in detail['rules']]==[r[0] for r in rules],'rule list mismatch')
        M=X.plus(e['M0'],X.c(1));total=(X.c(1),X.c(0))
        for actual,(name,labels,guard) in zip(detail['rules'],rules):
            need([at(a) for a in actual['labels']]==labels,'projected label mismatch '+name)
            need((None if actual['guard'] is None else tuple(map(at,actual['guard'])))==guard,'guard mismatch '+name)
            w=lambda l:X.plus(X.c(1),X.times(l,M))
            left=X.times(e['Sp'],w(labels[2]));right=X.prod([e['S'],w(labels[0]),w(labels[1])])
            need(tuple(map(at,actual['accumulator']))==(left,right),'branch accumulator mismatch '+name)
            branch=X.ps((left,right))
            if guard is not None:branch=X.pa(branch,X.ps(guard))
            need(tuple(map(at,actual['branch_pair']))==branch,'branch SOS mismatch '+name)
            total=X.pm(total,branch)
        D=X.plus(X.times(X.plus(index,X.c(1)),e['y']),X.c(1));Dp=X.plus(D,e['y'])
        beta=[(e['x'],X.plus(e['S'],X.times(D,e['u']))),(e['x'],X.plus(e['Sp'],X.times(Dp,e['vq'])))]
        need([tuple(map(at,r)) for r in detail['beta_pairs']]==beta,'beta source pair mismatch')
        for pair in beta:total=X.pa(total,X.ps(pair))
        need((at(b['encoded_E']),at(b['encoded_F']))==total,'whole projected source pair mismatch')
        self.counts['exact_projected_rule_triples']=12;self.counts['exact_whole_projected_source_pair']=True
    def check_majorants(self):
        b=self.binding;p=b['parameters'];env=b['encoded_source']['environment']|{'index':b['encoded_index']}
        X=Expressions();at=self.expression_reader(X,env)
        def h(expr,memo):
            if expr in memo:return memo[expr]
            node=X.nodes[expr]
            if node[0]=='v':answer=1
            elif node[0]=='c':
                n=node[1];answer=0;power=1
                while power<n:answer+=1;power*=4
            elif node[0]=='add':answer=max(h(node[1],memo),h(node[2],memo))+1
            else:answer=h(node[1],memo)+h(node[2],memo)
            memo[expr]=answer;return answer
        def certify(certificate,expected_radius,actual_roots,height):
            cut=list(p.values());ex,aa=self.expander(cut);R=certificate['radius_atom'];D=certificate['exponent']
            need(aa(R)==expected_radius,'incorrect majorant radius')
            memo={};degrees=[h(at(a),memo) for a in actual_roots]
            needed=max(1,*degrees);need(certificate['root_exponents']==degrees and certificate['minimum_sufficient_exponent']==needed,'incorrect literal majorant exponent record')
            need(D==1 << (needed-1).bit_length(),'insufficient/noncanonical dyadic exponent')
            cache={}
            def power(a):
                if a==R:return 1
                need(a[0]=='v' and a[1] in self.gates,'bad fixed-power leaf');i=a[1]
                if i in cache:return cache[i]
                rhs=self.gate_rhs(i);need(self.gate_ops[i]=='mul' and len(rhs)==1,'fixed-power nonproduct')
                mon,coef=next(iter(rhs.items()));need(coef==1 and len(mon)==2,'fixed-power nonunit product')
                cache[i]=sum(power(['v',j]) for j in mon);return cache[i]
            need(power(height)==D and certificate['height']==height,'fixed-power height mismatch')
            return D,len(cache),len(memo)
        ex,aa=self.expander(list(p.values()));label=b['label_bound_certificate']
        need(label['actual_parameter_bound']==p['t'],'wrong horizon label bound')
        label_roots=[a for r in b['encoded_source']['rules'] for a in r['labels']]
        ld,lcount,_=certify(label,add(num(4),aa(p['t'])),label_roots,p['m'])
        source=b['radius_majorant'];expected_env={k:v for k,v in p.items() if k!='m'}|b['upper']
        need(source['source_environment']==expected_env and source['source_index']==p['t'],'majorant environment mismatch')
        sd,scount,nodes=certify(source,add(num(4),*(aa(p[k]) for k in ['t','x','y','M0'])),[b['encoded_E'],b['encoded_F']],b['H'])
        self.counts.update(label_majorant_exponent=ld,label_majorant_squarings=lcount,source_majorant_exponent=sd,source_majorant_squarings=scount,literal_source_majorant_nodes=nodes)

def main():
    p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--integer',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    a=ProjectedAudit(args.candidate);result=a.run()
    if args.integer:
        from check_normalized import inspect_integer
        result={'status':'PASS','core':result,'integer':inspect_integer(a,args.integer)}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
