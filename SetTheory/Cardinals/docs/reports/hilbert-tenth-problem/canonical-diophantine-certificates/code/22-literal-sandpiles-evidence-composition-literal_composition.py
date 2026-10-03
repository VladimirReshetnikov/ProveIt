#!/usr/bin/env python3
"""Finite-prism certificate composition with the separately audited U15 loader.

Imports only newly authored local code, never fetched upstream programs. No
background table or polynomial is materialized by the default bound command.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, sys
from dataclasses import dataclass
from pathlib import Path
sys.dont_write_bytecode=True
from prism_certificate import Prism,Compiler,natural
DEFAULT_LOADER=Path(__file__).resolve().parent.parent/'loader'
B=186238848;ZMAX=1955501572
PERIODS=(1303671936,744955392,1955501604)
C=80*B*B*(ZMAX+1)

def load_module(root):
    root=Path(root);manifest=root/'FROZEN-INPUTS.json'
    if hashlib.sha256(manifest.read_bytes()).hexdigest()!='de3e161de813afb098110223f9850c49cb8bcd481af69f8b9789daa3ca2950e3':raise ValueError('loader manifest changed; review needed')
    for name,entry in json.loads(manifest.read_text())['files'].items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=entry['sha256']:raise ValueError('frozen loader file changed: '+name)
    path=root/'compiler'/'literal_loader.py'
    spec=importlib.util.spec_from_file_location('literal_loader_for_certificate',path)
    module=importlib.util.module_from_spec(spec)
    names=('lazy_u15','periodic_router');missing=object();prior={name:sys.modules.get(name,missing) for name in names};old_path=sys.path[:]
    try:
        for name in names:sys.modules.pop(name,None)
        spec.loader.exec_module(module)
        for name,relative in (('lazy_u15','ca/lazy_u15.py'),('periodic_router','geometry/periodic_router.py')):
            if Path(sys.modules[name].__file__).resolve()!=(root/relative).resolve():raise ValueError('unexpected dependency import: '+name)
    finally:
        sys.path[:]=old_path
        for name in names:
            if prior[name] is missing:sys.modules.pop(name,None)
            else:sys.modules[name]=prior[name]
    return module

@dataclass(frozen=True)
class LiteralInput:
    ell:str
    right:str
    root:Path=DEFAULT_LOADER
    def __post_init__(self):
        if not isinstance(self.ell,str) or not isinstance(self.right,str) or any(c not in '01' for c in self.ell+self.right):raise ValueError('binary halves required')
        module=load_module(self.root);circuit=module.Circuit()
        if circuit.B!=B or circuit.P!=PERIODS:raise ValueError('loader constants changed; composition needs review')
        object.__setattr__(self,'_module',module);object.__setattr__(self,'_circuit',circuit)
        object.__setattr__(self,'seeds',frozenset(module.tape_pair_loader(self.ell,self.right,circuit)))
    def height(self,p):return self._module.background_height(tuple(p),self._circuit)+int(tuple(p) in self.seeds)
    def check_prism(self,P):
        if any(not P.contains(p) for p in self.seeds):raise ValueError('prism omits a seed')
    def bound_prism(self,T,p):return halt_prism(self.ell,self.right,T,p)

def halt_prism(ell,right,T,p):
    natural(T)
    if type(p)is not int or abs(p)>T:raise ValueError('head position must satisfy |p|<=T')
    if any(c not in '01' for c in ell+right):raise ValueError('nonbinary input')
    L=min(-3,-len(ell)-1);R=max(3,len(right)+1)
    H=2*T+max(p-L,R-p);xmin=2*L-2*T-p+1;xmax=2*R+2*T-p-1
    lower=(B*(xmin-2),0,0);upper=(B*(xmax+3),B*(H+1),ZMAX)
    return Prism(lower,tuple(upper[i]-lower[i]+1 for i in range(3)))

def dimension_ledger(P):
    """No oracle calls and no loops over V; exact dimension-only quantities."""
    v,e,h=P.V,P.E,P.H
    return {'lower':P.lower,'lengths':P.lengths,'V':v,'E':e,'H':h,'witnesses':8*v+6*e+h,'summands':8*v+7*e+h,'plain_square_residuals':3*v+e+h,'weighted_square_residuals':2*v+5*e,'product_summands':3*v+e,'degree':3,'raw_monomial_upper_bound':955*v+173*e+10*h,'coefficient_multiplication_upper_bound':1415*v+301*e+16*h,'evaluation_multiplications':33*v+76*e+4*h,'evaluation_addition_upper_bound':22*v+63*e+4*h-1,'natural_witness_value_bound':max(5,v),'natural_witness_bits_per_coordinate':max(5,v).bit_length(),'dense_period_sites':PERIODS[0]*PERIODS[1]*PERIODS[2],'quadratic_volume_constant':C,'coefficient_generation':'streaming only; not materialized'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--ell',default='');ap.add_argument('--right',default='');ap.add_argument('--time',type=int,default=0);ap.add_argument('--head',type=int,default=0);ap.add_argument('--stream',choices=('raw','collected'));ap.add_argument('--loader-root',type=Path,default=DEFAULT_LOADER);ap.add_argument('--take',type=int);args=ap.parse_args()
    P=halt_prism(args.ell,args.right,args.time,args.head)
    if args.stream:
        source=LiteralInput(args.ell,args.right,args.loader_root);compiler=Compiler(P,source)
        records=compiler.records() if args.stream=='raw' else compiler.collected_records()
        from itertools import islice
        for m,c in records if args.take is None else islice(records,args.take):print(json.dumps({'monomial':m,'coefficient':c},separators=(',',':')))
    else:print(json.dumps(dimension_ledger(P),indent=2,sort_keys=True))
