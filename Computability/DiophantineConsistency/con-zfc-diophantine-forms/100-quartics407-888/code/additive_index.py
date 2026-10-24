"""Derive requested Pell indices by exact addition identities.

This module subclasses the synchronized compiler's SharedProductPowerBuilder.
It uses a delayed power phase so the complete requested exponent set is known.
The unique scale A is common; only seed indices use the inherited index test.
Every derived coordinate is determined by quadratic natural-valued identities.
"""
from shared_product_power import SharedProductPowerBuilder
from build_equation import ZERO, ONE, TWO, const, require


class AdditiveIndexPowerBuilder(SharedProductPowerBuilder):
    def __init__(self, positive_powers=True, **kwargs):
        super().__init__(positive_powers=positive_powers, **kwargs)
        self.pending_powers=[]
        self.power_indices_ready=False
        self.seed_indices={}
        self.index_derivations=[]
        self.known_exponents=set()
        self.index_definitions={}
        self.pell_D=None
        self.constant_indices={}

    def power(self,n,k):
        require(not self.shared_frame_finalized,'cannot add a power after finalization')
        key=n,k
        if key in self.powers:return self.powers[key]
        tag='pow'+str(len(self.powers))
        m=self.new(tag+'.output')
        self.powers[key]=m
        self.pending_powers.append((n,k,m,tag))
        return m

    def _discriminant(self):
        if self.pell_D is None:
            _,A,_=self._scale()
            self.pell_D=self.new('index_addition.D')
            self.eq(self.square(A),self.add(self.pell_D,ONE),'index_addition.D_definition')
        return self.pell_D

    def _small_index(self,n):
        if n in self.constant_indices:return self.constant_indices[n]
        _,A,_=self._scale()
        if n==0:pair=ONE,ZERO
        elif n==1:pair=A,ONE
        elif n==2:
            X=self.add(self.mul(TWO,self._discriminant()),ONE)
            pair=X,self.mul(TWO,A)
        else:raise ValueError('unsupported fixed index')
        self.constant_indices[n]=pair
        return pair

    def _combine(self,a,b):
        X,Y=a;U,V=b
        D=self._discriminant()
        return self.add(self.mul(X,U),self.mul(D,self.mul(Y,V))),self.add(self.mul(X,V),self.mul(Y,U))

    def _index(self,k):
        if k in self.shared_indices:return self.shared_indices[k]
        definition=self.index_definitions.get(k)
        if definition and definition[0]=='add':
            _,a,b=definition
            if a[0]=='c' and 0<a[1]<=2 and b in self.known_exponents:
                pair=self._combine(self._index(b),self._small_index(a[1]))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'shift','target':k,'source':b,'shift':a[1],'pair':pair})
                return pair
            if b[0]=='c' and 0<b[1]<=2 and a in self.known_exponents:
                pair=self._combine(self._index(a),self._small_index(b[1]))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'shift','target':k,'source':a,'shift':b[1],'pair':pair})
                return pair
            if a in self.known_exponents and b in self.known_exponents:
                pair=self._combine(self._index(a),self._index(b))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'sum','target':k,'sources':[a,b],'pair':pair})
                return pair
        pair=super()._index(k)
        self.seed_indices[k]=pair
        return pair

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        if not self.power_indices_ready:
            self.known_exponents={k for _,k,_,_ in self.pending_powers}
            self.index_definitions={out:key for key,out in self.cache.items()}
            _,A,_=self._scale()
            for n,k,m,tag in self.pending_powers:
                X,Y=self._index(k)
                T=self._base(n)
                quotient=self.new(tag+'.quotient')
                self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
                self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,'shared_scale':True,'index_addition':True})
            self.power_indices_ready=True
        # Only independent indices need auxiliary divisibility; derived pairs
        # have already been fixed by the exact ring addition law.
        if not self.index_product_finalized:
            U,V,B=self._auxiliary_index()
            productY2=self.product([self.square(Y) for X,Y in self.seed_indices.values()])
            vm1=self.new('shared_index.Vquotient_minus1')
            self.eq(V,self.mul(productY2,self.add(vm1,ONE)),'shared_index.V_positive_product')
            self.index_product_finalized=True
        # Parent skips the already completed global auxiliary product.
        super().finalize_power_frame()
