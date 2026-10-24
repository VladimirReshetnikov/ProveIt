"""Exact binomial digits from common Pell residues, without full numerators.

Experimental builder. Proof supplied separately; exported rows remain quadratic.
"""
from reuse_radix import AdditiveReusedRadixBuilder
from shared_power import SharedPowerBuilder
from build_equation import ONE,TWO,ZERO,const,require

class ModularBinomialBuilder(AdditiveReusedRadixBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.modular_requests=[]

    def _scale(self):
        if self.shared_parameters is None:
            W,L,sm,zm1=[self.new('shared.'+n) for n in ('W','lower_A','A_slack','Zminus1')]
            A=self.add(L,sm)
            Z=self.add(zm1,ONE)
            self.norm(self.add(W,ONE),L,self.mul(W,Z),'shared.last_norm_lower')
            self.shared_parameters=W,A,Z
            self.scale_lower=L
        return self.shared_parameters

    def finalize_binomials(self):
        require(not getattr(self,'binomials_finalized',False),'repeated finalization')
        self.binomials_finalized=True
        moduli={r[2] for r in self.range_requests}
        require(len(moduli)==1,'one common range modulus required')
        B=next(iter(moduli));rcount=len(self.range_requests)
        aggregate=self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(rcount),B),self.add(self.sum(n for n,_,_,_ in self.range_requests),aggregate),'crt.aggregate_representative_bound')
        V=self.factorial_radix['numerator']
        q=self.mul(B,self.add(V,ONE));qb=self.add(q,ONE)
        for i,((n,k),out) in enumerate(self.binomials.items()):
            den=self.power(q,k)
            self.modular_requests.append({'kind':'exact','n':n,'k':k,'output':out,'den':den,'label':'choose'+str(i)})
        for i,(n,k,B,label) in enumerate(self.range_requests):
            den=self.power(q,k)
            self.modular_requests.append({'kind':'divisible','n':n,'k':k,'den':den,'label':label})
        H=self.factorial_radix['H'];topden=self.power(q,H)
        self.modular_root=self.mul(q,topden)
        _,A,_=self._scale()
        self.root_quotient=self.new('modular.root_quotient')
        self.eq(self.product([TWO,A,qb]),self.sum([self.square(qb),ONE,self.mul(self.modular_root,self.root_quotient)]),'modular.common_root')
        self.radix_data={'upper_atoms':list(dict.fromkeys([n for n,k in self.binomials]+[n for n,_,_,_ in self.range_requests])),
             'radix':q,'radix_multiple':B,'factorial_radix':self.factorial_radix,'aggregate_range_count':rcount,'aggregate_slack':aggregate,
             'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests),'modular_requests':self.modular_requests,
             'common_root_modulus':self.modular_root,'top_exponent':H,'root_base':qb,'root_quotient':self.root_quotient}

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        if not self.power_indices_ready:
            self.known_exponents={k for _,k,_,_ in self.pending_powers}|{r['n'] for r in self.modular_requests}
            self.index_definitions={out:key for key,out in self.cache.items()}
            _,A,_=self._scale()
            for n,k,m,tag in self.pending_powers:
                X,Y=self._index(k);T=self._base(n);quotient=self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,'shared_scale':True,'index_addition':True})
            q=self.radix_data['radix'];qb=self.radix_data['root_base'];B=self.radix_data['radix_multiple']
            for request in self.modular_requests:
                n,den,label=request['n'],request['den'],request['label']
                X,Y=self._index(n)
                h,r,s=[self.new(label+'.modular_'+role) for role in ('quotient','remainder','rslack')]
                modulus=self.mul(den,q if request['kind']=='exact' else B)
                residue=r
                if request['kind']=='exact':
                    out=request['output'];os=self.new(label+'.modular_oslack')
                    residue=self.add(r,self.mul(den,out))
                    self.eq(q,self.sum([out,os,ONE]),label+'.digit_bound')
                self.eq(self.add(X,self.mul(qb,Y)),self.sum([self.mul(A,Y),residue,self.mul(modulus,h)]),label+'.modular_digit')
                self.eq(den,self.sum([r,s,ONE]),label+'.remainder_bound')
                request.update({'pair':(X,Y),'quotient':h,'remainder':r,'remainder_slack':s,'modulus':modulus})
            self.power_indices_ready=True
        if not self.index_product_finalized:
            U,V,B=self._auxiliary_index()
            productY2=self.product([self.square(Y) for X,Y in self.seed_indices.values()])
            vm1=self.new('shared_index.Vquotient_minus1')
            self.eq(V,self.mul(productY2,self.add(vm1,ONE)),'shared_index.V_positive_product')
            self.index_product_finalized=True
        atoms={a for (n,k),m in self.powers.items() for a in (n,k,m)}
        W,_,_=self._scale()
        self.eq(W,self.sum([TWO]+sorted(atoms)),'shared.frame_definition')
        self.shared_frame_finalized=True
