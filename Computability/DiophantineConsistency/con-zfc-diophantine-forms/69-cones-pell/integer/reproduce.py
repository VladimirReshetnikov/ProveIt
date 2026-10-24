#!/usr/bin/env python3
"""Build and exactly audit the canonical-anchor cone reduction.

Python standard library only. Imported upstream files are read-only. No
consistency search is run. Symbolic checks are exact sparse ring arithmetic.
"""
from __future__ import annotations
import ast
import gzip
import hashlib
import importlib.util
import itertools
import json
import shutil
import sys
from pathlib import Path

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
UP = HERE / 'upstream'
OUT = HERE
PIN = '9cca523d9f27ad39d52993f4065cbd7e58f8bdd4'

def need(c, message):
    if not c:
        raise ValueError(message)

class P:
    """Sparse polynomials; monomials are sorted (name,exponent) tuples."""
    def __init__(self, d=None):
        self.d = {m:c for m,c in (d or {}).items() if c}
    @staticmethod
    def val(x):
        return x if isinstance(x,P) else P({():int(x)})
    @staticmethod
    def var(s):
        return P({((s,1),):1})
    def __add__(self, other):
        d = dict(self.d)
        for m,c in P.val(other).d.items():
            d[m] = d.get(m,0)+c
        return P(d)
    __radd__ = __add__
    def __neg__(self):
        return P({m:-c for m,c in self.d.items()})
    def __sub__(self, other):
        return self+-P.val(other)
    def __rsub__(self, other):
        return P.val(other)+-self
    def __mul__(self, other):
        d={}
        for m,c in self.d.items():
            for n,e in P.val(other).d.items():
                v=dict(m)
                for k,a in n:v[k]=v.get(k,0)+a
                t=tuple(sorted(v.items()))
                d[t]=d.get(t,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(self,n):
        need(isinstance(n,int) and n>=0,'nonnegative fixed exponent')
        r=P.val(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,other):return self.d==P.val(other).d
    def names(self):return {s for m in self.d for s,e in m}
    def degree(self,unknowns):
        return max([sum(e for s,e in m if s in unknowns) for m in self.d],default=-1)
    def subst(self, defs):
        out=P()
        for m,c in self.d.items():
            t=P.val(c)
            for s,e in m:t=t*(defs.get(s,P.var(s))**e)
            out=out+t
        return out
    def text(self):
        if not self.d:return '0'
        terms=[]
        for m,c in sorted(self.d.items(),key=lambda x:(sum(e for _,e in x[0]),x[0])):
            factors=[str(c)]+[s if e==1 else s+'**'+str(e) for s,e in m]
            terms.append('*'.join(factors))
        return ' + '.join(terms).replace('+ -','- ')
    def packet(self):
        return [{'coefficient':c,'powers':dict(m)} for m,c in sorted(self.d.items())]

def parse(text):
    def f(t):
        if isinstance(t,ast.Constant) and type(t.value)==int:return P.val(t.value)
        if isinstance(t,ast.Name):return P.var(t.id)
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return -f(t.operand)
        if isinstance(t,ast.BinOp):
            a=f(t.left)
            if isinstance(t.op,ast.Add):return a+f(t.right)
            if isinstance(t.op,ast.Sub):return a-f(t.right)
            if isinstance(t.op,ast.Mult):return a*f(t.right)
            if isinstance(t.op,ast.Pow) and isinstance(t.right,ast.Constant):return a**t.right.value
        raise ValueError('Unsupported syntax: '+ast.dump(t))
    return f(ast.parse(text,mode='eval').body)

def writej(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def packet(name,variables,rows,degree,coefficient_monomial,extra=None):
    pp=[parse(r) for r in rows]; unknowns=set(variables)
    ports={'beta','K0','MC','MF','Walpha','WC'}
    need(set.union(*(r.names() for r in pp))<=unknowns|ports,name+' undeclared variable')
    need(set.union(*(r.names() for r in pp))&unknowns==unknowns,name+' unused variable')
    poly=sum((p*p for p in pp),P())
    exact=poly.degree(unknowns)
    need(exact==degree,name+' exact symbolic degree')
    mon=tuple(sorted(coefficient_monomial.items()))
    need(poly.d.get(mon)==1,name+' coefficient certificate')
    # The coefficient is exactly 1 with no additional coefficient-port monomials.
    matching=[(m,c) for m,c in poly.d.items() if tuple((s,e) for s,e in m if s in unknowns)==mon]
    need(matching==[(mon,1)],name+' coefficient independence')
    result={
      'name':name,'domain':'unrestricted integers','variables':variables,
      'variable_count':len(variables),'residuals':rows,'equation_count':len(rows),
      'single_polynomial':'sum of squares of the listed residuals',
      'exact_degree':degree,'residual_degrees':[p.degree(unknowns) for p in pp],
      'fixed_numerals':['beta','K0','MC','MF','Walpha','WC'],
      'fixed_binding':'coefficients/COEFFICIENT_BINDING.json',
      'degree_certificate':{'monomial':coefficient_monomial,'coefficient':1},
      'source_commit':PIN,'source':'upstream/quartic41.json',
      'proof':'PROOF.md','status':'ordinary mathematical proof relative to the explicitly cited inherited source theorem; not an end-to-end proof-assistant certificate',
      'symbolic_port_expansion_terms':len(poly.d)}
    if extra:result.update(extra)
    writej(OUT/(name+'.json'),result)
    writej(OUT/'certificates'/(name+'_expansion.json'),{'monomials':poly.packet()})
    return result,pp

def canonical_coefficients():
    spec=importlib.util.spec_from_file_location('authentic_upstream',UP/'coefficients'/'build_coefficients.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    ports,audit=mod.construct()
    beta=ports['beta'];rho=1<<121;A=1<<(121*3296);H=1<<(121*2196)
    T=ports['K']-beta*rho+1
    need(T>0 and A>H>0,'positive fixed scales')
    need(2*(T+1)*(A+H)<beta,'anchor capacity for alpha')
    need(T+1 < (1<<(121*5496)),'T coefficient bound')
    vals={'beta':beta,'K0':ports['K'],'MC':ports['MC'],'MF':ports['MF_source'],
          'Walpha':2*T*A,'WC':T*beta}
    payloads={}
    for name,v in vals.items():
        raw=v.to_bytes((v.bit_length()+7)//8,'little')
        gz=gzip.compress(raw,mtime=0)
        p=OUT/'coefficients'/(name+'.bin.gz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(gz)
        payloads[name]={'file':p.relative_to(OUT).as_posix(),'bits':v.bit_length(),
                       'raw_bytes':len(raw),'gzip_bytes':len(gz),'raw_sha256':hashlib.sha256(raw).hexdigest(),
                       'gzip_sha256':hashlib.sha256(gz).hexdigest()}
    bind={'source_tuple':'source34 mixed-parity-unrounded-1064921','MF_convention':'already shifted MF_native+beta',
          'coefficient_recipes':{'rho':'2**121','beta':'2**1064921-1','A':'2**398816','H':'2**265716',
             'T':'K0-beta*rho+1','Walpha':'2*T*A','WC':'T*beta'},
          'payloads':payloads,'new_fixed_bound':'2*(T+1)*(A+H)<beta',
          'total_raw_bytes':sum(x['raw_bytes'] for x in payloads.values()),
          'total_gzip_bytes':sum(x['gzip_bytes'] for x in payloads.values()),'upstream_audit':audit}
    writej(OUT/'coefficients'/'COEFFICIENT_BINDING.json',bind)
    return bind

def build():
    OUT.mkdir(parents=True,exist_ok=True)
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    for item in pins['files']:
        raw=(HERE/item['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        need(blob==item['git_blob'],'source Git blob mismatch: '+item['local'])
    source=json.loads((UP/'quartic41.json').read_text())
    need(len(source['variables'])==41 and len(source['residuals'])==26,'source dimensions')
    removed=[v for v in source['variables'] if v.startswith('FA_pos') or v.startswith('FC_pos')]
    need(len(removed)==6,'six original private guard variables')
    newvars=[v for v in source['variables'] if v not in removed]+['cone1','cone2','cone3']
    C='(beta*J+1-F-alpha)'
    x='(beta*F)';y='(Walpha*alpha)';z='(WC*'+C+')'
    guard=f'2*({x}*{y}+{x}*{z}+{y}*{z})-{x}**2-{y}**2-{z}**2-cone1**2-cone2**2-cone3*(cone3+1)-1'
    rows=source['residuals'][:23]+[source['residuals'][25],guard]
    q38,p38=packet('quartic38',newvars,rows,4,{'tau':4},{'source_guard_rows_replaced':[23,24],
         'zero_set_claim':'every new zero restores an old zero; canonical old witnesses give new zeros; no bijection claim'})
    q='(beta*J+1)'
    d32={'N':q+'*(L+1)','X':'4*w_scale*'+q,'C2':'c**2','F2':'f**2','Baux':'I**2',
         'P':'E*(c-eta)+eta+zeta','tau':'tau+E*(c-eta)'}
    deleted32={1,2,6,10,14,19}
    polys32={k:parse(v) for k,v in d32.items()}
    s32=[p.subst(polys32) for p in p38]
    need(all(s32[i]==0 for i in deleted32),'sextic deleted definitions')
    n32=[v for v in newvars if v not in set(d32)-{'tau'}]
    q32,p32=packet('sextic32',n32,[p.text() for i,p in enumerate(s32) if i not in deleted32],6,{'I':4,'g':2},
           {'restoration_map':d32,'deleted_source_row_indices_zero_based':sorted(deleted32),
            'zero_set_claim':'bijection to quartic38 by the listed integer-polynomial restoration'})
    k='(1-V+j*c+h*E)'
    d27={'L':q+'**2-1','N':q+'**3','X':'4*w_scale*'+q,'C2':'c**2','F2':'f**2','Baux':'I**2',
        'g':'y**2-V**2','P':'E*(c-eta)+'+k,'zeta':k+'-eta',
        'D':'4*w_scale*'+q+'+a*c+gamma*(4*a+3)','Delta':'a**2+4*a+3'}
    deleted27={0,1,2,6,8,9,10,14,16,17,19}
    polys27={k:parse(v) for k,v in d27.items()}
    s27=[p.subst(polys27) for p in p38]
    need(all(s27[i]==0 for i in deleted27),'octic deleted definitions')
    n27=[v for v in newvars if v not in d27]
    q27,p27=packet('octic27',n27,[p.text() for i,p in enumerate(s27) if i not in deleted27],8,{'I':4,'V':4},
          {'restoration_map':d27,'deleted_source_row_indices_zero_based':sorted(deleted27),
           'zero_set_claim':'bijection to quartic38 by the listed integer-polynomial restoration'})
    need([len(n32),len(n27),len(rows)]==[32,27,25],'new dimensions')
    # Fixed-scaling covariance and every box vertex, exactly over integers.
    cone=lambda x,y,z:2*(x*y+x*z+y*z)-x*x-y*y-z*z
    vertices=[{'point':p,'value':cone(*p)} for p in itertools.product((1,2),repeat=3)]
    need(min(v['value'] for v in vertices)==3,'cone vertex minimum')
    mixed=0
    for t in itertools.product(range(-12,13),repeat=3):
        if cone(*t)>0:
            need(all(v>0 for v in t) or all(v<0 for v in t),'finite mixed sign control')
        mixed+=1
    # Diagnostic toy cells: complete cyclic rotations, exact native remainder,
    # and normalizing inequalities. This tests all words of length <=5.
    toy_count=0
    for N in range(1,6):
        B=1024;beta=B-1;A=16;H=4;DC=2;DR=1;T=DC+DR+1
        J=(B**N-1)//beta; q=B**N
        for data in itertools.product(range(H),repeat=N):
            C=sum((A+v)*B**i for i,v in enumerate(data))
            U=(B*C)%(q-1)
            for width in range(N):
                V=(B**width*C)%(q-1)
                F=DC*C+DR*U+V;alpha=q-F-C
                need(0<F<q-1,'toy remainder')
                need((DC+B*DR+B**width)*C%(q-1)==F,'toy transport')
                X=beta*F;Y=2*T*A*alpha;Z=T*beta*C;lower=T*A*beta*J
                need(all(lower<=v<=2*lower for v in (X,Y,Z)),'toy canonical cone box')
                need(cone(X,Y,Z)>=3*lower**2,'toy cone positivity')
                toy_count+=1
    coefficient_binding=canonical_coefficients()
    metrics={'status':'PASS','comparison_commit':PIN,'results':[
       {k:r[k] for k in ['name','domain','variable_count','equation_count','exact_degree','symbolic_port_expansion_terms']}
       for r in (q38,q32,q27)],'exact_deleted_equation_checks':len(deleted32)+len(deleted27),
       'cone_vertices':vertices,'finite_mixed_sign_diagnostics':mixed,'toy_native_word_diagnostics':toy_count,
       'coefficient_raw_bytes':coefficient_binding['total_raw_bytes'],
       'boundary':'finite audits do not replace the universal cone proof or inherited unbounded compiler/Pell theorem'}
    writej(OUT/'CHECKS.json',metrics)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':build()
