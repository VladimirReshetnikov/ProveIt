#!/usr/bin/env python3
"""Bind an independent C222 syntax AST and its depth bound to the pinned source.

Runs the preserved square-shell source through a symbolic arithmetic builder,
lowers an independent constructor AST, and compares all nine axiom outputs
and the two inference-label constructors exactly. No prover or network is used.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import types

import schema_audit as ar

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'inherited/syntax/shell_source.py'
EXPECTED='59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199'
REPO_PATH=('Computability/DiophantineConsistency/con-zfc-diophantine-forms/'
 '112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/'
 'ConZFC_Shell_Reciprocal_660/code/shell_source.py')

class AST:
    def __init__(self): self.nodes=[];self.cache={}
    def make(self,op,*args):
        key=(op,args)
        if key in self.cache:return self.cache[key]
        idx=len(self.nodes)
        depth=0 if op in ('var','const') else 1+max(self.nodes[j]['depth'] for j in args)
        node={'id':idx,'op':op,'args':list(args),'depth':depth,
              'bound_exponent':2**(depth+1)-1}
        self.nodes.append(node);self.cache[key]=idx;return idx
    def lower(self,idx):
        n=self.nodes[idx];op=n['op'];aa=n['args']
        if op=='var':return ar.V(aa[0])
        if op=='const':return ar.C(aa[0])
        x,y=[self.lower(j) for j in aa]
        return {'I':ar.I,'M':ar.M,'A':ar.A,'E':ar.E}[op](x,y)

def independent_ast():
    b=AST()
    zero,one=b.make('const',0),b.make('const',1)
    a,bb,c,d=[b.make('var',s) for s in 'abcd']
    I=lambda x,y:b.make('I',x,y)
    M=lambda x,y:b.make('M',x,y)
    A=lambda x,y:b.make('A',x,y)
    E=lambda x,y:b.make('E',x,y)
    N=lambda x:I(x,one)
    Ex=lambda x,h:N(A(x,N(h)))
    def req(y,k,h):
        return A(y,I(h,N(A(y,I(h,N(M(y,k)))))))
    def clos(x,y,k,h):
        subset=A(k,I(M(k,x),M(k,y)))
        return A(y,I(M(y,k),N(A(x,I(h,N(A(x,I(subset,req(y,k,h)))))))))
    def bundle(x,y,k):
        rv=I(M(x,y),A(k,M(x,y)))
        negative_seed=A(k,I(clos(x,y,k,k),N(req(y,k,k))))
        return N(I(rv,negative_seed))
    roots=[Ex(a,E(a,bb)),I(A(a,I(bb,c)),I(A(a,bb),A(a,c))),
      I(E(a,bb),I(M(c,a),M(c,bb))),I(A(a,A(bb,c)),A(bb,A(a,c))),
      I(E(c,a),I(M(c,bb),M(a,bb))),I(Ex(a,A(a,bb)),bb),
      I(E(c,a),I(E(c,bb),A(M(a,bb),E(a,bb)))),
      I(I(I(c,d),a),I(I(a,c),I(bb,c))),bundle(a,bb,c)]
    extra=[a,bb,I(a,bb),A(a,bb),one]
    return b,roots,extra

class ArithmeticBuilder:
    @staticmethod
    def normalize(x):
        if isinstance(x,tuple) and len(x)==2 and x[0]=='c':return ar.C(x[1])
        return x
    @staticmethod
    def add(*xs):return ar.add(*(ArithmeticBuilder.normalize(x) for x in xs))
    @staticmethod
    def mul(*xs):return ar.mul(*(ArithmeticBuilder.normalize(x) for x in xs))
    @staticmethod
    def square(x):return ar.sq(ArithmeticBuilder.normalize(x))
    @staticmethod
    def sqdiff(x,y):return ar.sd(ArithmeticBuilder.normalize(x),ArithmeticBuilder.normalize(y))
    @staticmethod
    def sum(xs):return ArithmeticBuilder.add(*xs)
    @staticmethod
    def product(xs):return ArithmeticBuilder.mul(*xs)

def source_outputs():
    # A four-constant interface is the complete imported dependency of this
    # source file. Its exact hash is checked before execution.
    constants=types.ModuleType('build_equation')
    for name,val in [('ZERO',0),('ONE',1),('TWO',2),('FOUR',4)]:
        setattr(constants,name,ar.C(val))
    prior=sys.modules.get('build_equation')
    sys.modules['build_equation']=constants
    try:
        spec=importlib.util.spec_from_file_location('_pinned_shell_source',SOURCE)
        mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    finally:
        if prior is None:sys.modules.pop('build_equation',None)
        else:sys.modules['build_equation']=prior
    env={s:ar.V(s) for s in ('a','b','c','d','p','q','v')}
    out=mod.direct_source(ArithmeticBuilder(),{},env,ar.C(0),False,codes_only=True)
    return out['codes'],[env['a'],env['b'],out['I'](env['a'],env['b']),
                        out['A'](env['a'],env['b']),ar.C(1)]

def main():
    raw=SOURCE.read_bytes()
    digest=hashlib.sha256(raw).hexdigest()
    if digest!=EXPECTED:raise RuntimeError('pinned constructor source hash mismatch')
    b,roots,extra=independent_ast()
    codes,additional=source_outputs()
    if len(codes)!=9:raise RuntimeError('wrong axiom count')
    for i,(idx,out) in enumerate(zip(roots+extra,codes+additional)):
        if b.lower(idx)!=out:raise RuntimeError(f'constructor/source mismatch at output {i}')
    depths=[b.nodes[i]['depth'] for i in roots]
    if depths!=[4,3,3,3,3,5,4,3,19]:raise RuntimeError('unexpected depth vector')
    maxdepth=max(b.nodes[i]['depth'] for i in roots+extra)
    if maxdepth!=19:raise RuntimeError('maximum depth is not 19')
    # Exact rational inequality proving the worst constructor estimate:
    # (8 + 14/16 + 7/256) < 16.
    if not 8*256+14*16+7<16*256:raise RuntimeError('constructor inequality failed')
    cert={'schema':'c222-square-shell-depth-certificate-v1',
      'repository':'https://github.com/VladimirReshetnikov/ProveIt',
      'commit':'953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4',
      'source_path':REPO_PATH,'source_sha256':digest,'source_bytes':len(raw),
      'source_scheme':'xx0','source_outputs_compared':14,
      'comparison':'Independent constructor AST lowered to canonical commutative arithmetic DAG; exact structural equality to pinned source outputs.',
      'nodes':b.nodes,'axiom_roots':roots,'axiom_names':['rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle222'],
      'additional_label_roots':extra,'axiom_depths':depths,
      'maximum_depth':19,'maximum_label_bound_exponent':2**20-1,
      'derived_label_sum_terms':14,'carrier_degree_constant':2**20,
      'hypotheses':{'horizon_minimum':16,'local_parameters':'0<=a,b,c,d<t'},
      'constructor_majorization':{'upper':'8*t^(2e)+14*t^e+7','bound':'t^(2e+1)',
        'conditions':'t>=16, e>=1, 0<=u,v<=t^e',
        'integer_check_lhs':8*256+14*16+7,'integer_check_rhs':16*256},
      'status':'Finite AST/source/depth certificate. The accompanying inductive argument proves the unbounded majorization.'}
    print(json.dumps(cert,indent=2))

if __name__=='__main__':main()
