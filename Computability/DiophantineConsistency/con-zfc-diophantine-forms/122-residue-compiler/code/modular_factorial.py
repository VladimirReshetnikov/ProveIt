#!/usr/bin/env python3
"""Common modular Pell numerators on the round14 factorial-carrier source.

Research builder: a complete ordinary-proof note accompanies the output.
It imports pinned upstream source read-only; all writes use --output.
"""
from pathlib import Path
import argparse, hashlib, json, os, sys

WORK = Path(__file__).resolve().parent.parent
PACKAGED_ROUND = WORK / 'vendor/round14'
DEFAULT_ROUND = PACKAGED_ROUND if PACKAGED_ROUND.is_dir() else WORK / 'frontier_audit/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24'
ROUND = Path(os.environ.get('CONZFC_ROUND14_ROOT', str(DEFAULT_ROUND)))
sys.path.insert(0, str(ROUND / 'architecture'))
import build_derived_label_range as src
from build_equation import ONE, TWO, const, require
h = src.h

class ModularFactorialBuilder(h.HybridBuilder):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.modular_requests = []
        ModularFactorialBuilder.last_instance = self

    def common_root_modulus(self, q, K):
        self.root_modulus_recipe = {'kind':'q^(K+1)','exponents':[K]}
        return self.mul(q,self.power(q,K))

    def _scale(self):
        if self.shared_parameters is None:
            W,L,s,zm1 = [self.new('shared.'+n) for n in ('W','lower_A','A_slack','Zminus1')]
            A = self.add(L,s)
            Z = self.add(zm1,ONE)
            self.norm(self.add(W,ONE),L,self.mul(W,Z),'shared.last_norm_lower')
            self.shared_parameters = W,A,Z
            self.scale_lower = L
        return self.shared_parameters

    def finalize_binomials(self):
        require(not getattr(self,'binomials_finalized',False),'repeated finalization')
        self.binomials_finalized = True
        moduli = {v[2] for v in self.range_requests}
        require(len(moduli)==1,'one common amplified modulus required')
        N = next(iter(moduli))
        K = self.amplification_data['K']
        aggregate_requests = getattr(self,'aggregate_requests',self.range_requests)
        count = len(aggregate_requests)
        aggregate = self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(count),self.square(N)),
                self.add(self.sum(n for n,_,_,_ in aggregate_requests),aggregate),
                'crt.aggregate_representative_bound')
        V = self.factorial_radix['numerator']
        q = self.mul(N,self.power(self.sum([N,V,ONE]),K))
        qb = self.add(q,ONE)
        for i,((n,k),out) in enumerate(self.binomials.items()):
            den = self.power(q,k)
            self.modular_requests.append({'kind':'exact','n':n,'k':k,'output':out,
                'den':den,'label':'choose'+str(i)})
        for i,(n,k,modulus,label) in enumerate(self.range_requests):
            den = self.power(q,k)
            self.modular_requests.append({'kind':'divisible','n':n,'k':k,
                'den':den,'label':label})
        M = self.common_root_modulus(q,K)
        _,A,_ = self._scale()
        rootq = self.new('modular.root_quotient')
        self.eq(self.product([TWO,A,qb]),self.sum([self.square(qb),ONE,self.mul(M,rootq)]),
                'modular.common_root')
        self.radix_data = {'radix':q,'modulus':N,'K':K,'V':V,'aggregate_count':count,
            'aggregate_slack':aggregate,'kind':'N*(N+V+1)^K','bound':'count*N^2',
            'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests),
            'modular_requests':self.modular_requests,'common_root_modulus':M,
            'root_modulus_recipe':self.root_modulus_recipe,'root_base':qb,'root_quotient':rootq}

    def finalize_power_frame(self):
        if self.shared_frame_finalized:
            return
        if not self.power_indices_ready:
            self.known_exponents = {k for _,k,_,_ in self.pending_powers} | {r['n'] for r in self.modular_requests}
            self.index_definitions = {out:key for key,out in self.cache.items()}
            _,A,_ = self._scale()
            for n,k,m,tag in self.pending_powers:
                X,Y = self._index(k)
                T = self._base(n)
                quotient = self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,
                    'shared_scale':True,'index_addition':True})
            q = self.radix_data['radix']
            qb = self.radix_data['root_base']
            N = self.radix_data['modulus']
            for request in self.modular_requests:
                n,den,label = request['n'],request['den'],request['label']
                X,Y = self._index(n)
                quotient,r,s = [self.new(label+'.modular_'+role) for role in ('quotient','remainder','rslack')]
                modulus = self.mul(den,q if request['kind']=='exact' else N)
                residue = r
                if request['kind']=='exact':
                    out = request['output']
                    os = self.new(label+'.modular_oslack')
                    residue = self.add(r,self.mul(den,out))
                    self.eq(q,self.sum([out,os,ONE]),label+'.digit_bound')
                self.eq(self.add(X,self.mul(qb,Y)),self.sum([self.mul(A,Y),residue,self.mul(modulus,quotient)]),label+'.modular_digit')
                self.eq(den,self.sum([r,s,ONE]),label+'.remainder_bound')
                request.update({'pair':(X,Y),'quotient':quotient,'remainder':r,
                    'remainder_slack':s,'modulus':modulus})
            self.power_indices_ready = True
        if not self.index_product_finalized:
            U,V,B = self._auxiliary_index()
            productY2 = self.product([self.square(Y) for X,Y in self.seed_indices.values()])
            vm1 = self.new('shared_index.Vquotient_minus1')
            self.eq(V,self.mul(productY2,self.add(vm1,ONE)),'shared_index.V_positive_product')
            self.index_product_finalized = True
        atoms = {a for (n,k),m in self.powers.items() for a in (n,k,m)}
        W,_,_ = self._scale()
        self.eq(W,self.sum([TWO]+sorted(atoms)),'shared.frame_definition')
        self.shared_frame_finalized = True

def generate(out,syntax='cantor',horizon_minimum=16):
    old = h.HybridBuilder
    h.HybridBuilder = ModularFactorialBuilder
    try:
        result = src.generate(out,syntax,horizon_minimum)
        write_transform(out)
        return result
    finally:
        h.HybridBuilder = old

class ProductModularFactorialBuilder(ModularFactorialBuilder):
    """Only actual denominator powers; adjacent power derived by multiplication."""
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.power_derivations = {}

    def power(self,n,k):
        key = n,k
        if key in self.power_derivations:
            return self.power_derivations[key]['output']
        definition = {out:key for key,out in self.cache.items()}.get(k)
        if definition and definition[0]=='add':
            _,a,b = definition
            parent = a if b==ONE else b if a==ONE else None
            if parent is not None and (n,parent) in self.powers:
                prev = self.powers[n,parent]
                out = self.mul(n,prev)
                self.power_derivations[key] = {'base':n,'exponent':k,'previous_exponent':parent,
                    'previous_output':prev,'output':out,'identity':'n^(k+1)=n*n^k'}
                return out
        return super().power(n,k)

    def common_root_modulus(self,q,K):
        # The actual source has lower indices t,t+1,x+1,y+1.  Multiplying
        # denominator powers for t,x+1,y+1 dominates each q^(k+1).
        t = self.amplification_data['t']
        atoms = {v['name']:('v',i) for i,v in enumerate(self.variables)}
        x,y = atoms['x'],atoms['y']
        exponents = [t,self.add(x,ONE),self.add(y,ONE)]
        self.modular_product_exponents = exponents
        self.root_modulus_recipe = {'kind':'denominator_product','exponents':exponents}
        return self.product([self.power(q,k) for k in exponents])

def generate_product(out,syntax='cantor',horizon_minimum=16):
    old = h.HybridBuilder
    h.HybridBuilder = ProductModularFactorialBuilder
    try:
        result = src.generate(out,syntax,horizon_minimum)
        write_transform(out)
        return result
    finally:
        h.HybridBuilder = old

class DominantModularFactorialBuilder(ProductModularFactorialBuilder):
    """Endpoint-derived x dominates every lower index: M=N*q^(x+1)."""
    def common_root_modulus(self,q,K):
        atoms = {v['name']:('v',i) for i,v in enumerate(self.variables)}
        self.modular_product_exponents = [self.add(atoms['x'],ONE)]
        self.root_modulus_recipe = {'kind':'N_times_dominant_denominator',
            'exponents':self.modular_product_exponents,'N':self.amplification_data['N']}
        den = self.power(q,self.modular_product_exponents[0])
        return self.mul(self.amplification_data['N'],den)

def generate_dominant(out,syntax='cantor',horizon_minimum=16):
    old = h.HybridBuilder
    h.HybridBuilder = DominantModularFactorialBuilder
    try:
        result = src.generate(out,syntax,horizon_minimum)
        write_transform(out)
        return result
    finally:
        h.HybridBuilder = old

def write_transform(out):
    b = ModularFactorialBuilder.last_instance
    record = {'schema':'cofinal_modular_numerator_transform_v1','source_pin':'45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6',
        'source_archive':'ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip',
        'modular_method_predecessor':'con-zfc-diophantine-forms/108-pell-residues',
        'exact_powers':[{'base':n,'exponent':k,'output':m,'tag':tag} for n,k,m,tag in b.pending_powers],
        'power_derivations':list(getattr(b,'power_derivations',{}).values()),
        'root_modulus_recipe':b.root_modulus_recipe,'radix':b.radix_data,
        'scale':b.shared_parameters,'scale_lower':b.scale_lower,
        'modular_requests':b.modular_requests}
    h.write(Path(out)/'TRANSFORM.json',record)
    dependencies=[]
    for module in list(sys.modules.values()):
        path=getattr(module,'__file__',None)
        if not path:
            continue
        path=Path(path).resolve()
        if path.is_relative_to(ROUND.resolve()) and path.is_file():
            dependencies.append({'path':str(path.relative_to(ROUND.resolve())),
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    h.write(Path(out)/'DEPENDENCIES.json',{'round14_files':sorted(dependencies,key=lambda d:d['path'])})

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--product',action='store_true')
    p.add_argument('--dominant',action='store_true')
    p.add_argument('--horizon-minimum',type=int,default=16)
    a=p.parse_args()
    generate_choice = generate_dominant if a.dominant else generate_product if a.product else generate
    print(json.dumps(generate_choice(a.output,a.syntax,a.horizon_minimum),indent=2))
