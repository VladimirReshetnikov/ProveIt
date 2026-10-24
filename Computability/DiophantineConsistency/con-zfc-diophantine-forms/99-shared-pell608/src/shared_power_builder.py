"""One Pell environment shared by a finite family of positive powers.

Every exponent has one Pell index certificate; equal exponent atoms share it.
The global bound W is the sum of every base and exponent.  Its defining row
is emitted by finalize(), which must be called before exporting.
"""
from power_builder import PowerBuilder
from base_builder import ONE,TWO,FOUR


class SharedPowerBuilder(PowerBuilder):
    def __init__(self, positive_powers=False):
        super().__init__(positive_powers=positive_powers)
        self.shared_pell=None
        self.pell_indices={}
        self.power_arguments=[]
        self.finalized=False
        self.binomial_upper_arguments=[]

    def binomial(self,n,k):
        key=(n,k)
        if key in self.binomials:
            return self.binomials[key]
        if self.shared_digit_base is None:
            raise ValueError('shared digit base must be initialized')
        tag='choose'+str(len(self.binomials))
        out=self.new(tag+'.output')
        self.binomials[key]=out
        self.binomial_upper_arguments.append(n)
        q=self.shared_digit_base
        numerator=self.power(self.add(q,ONE),n)
        denominator=self.power(q,k)
        h,r,rs,os=[self.new(tag+'.'+s) for s in ('high','remainder','rslack','oslack')]
        quotient=self.add(self.mul(q,h),out)
        self.eq(numerator,self.add(self.mul(denominator,quotient),r),tag+'.digit_division')
        self.eq(denominator,self.sum([r,rs,ONE]),tag+'.remainder_bound')
        self.eq(q,self.sum([out,os,ONE]),tag+'.digit_bound')
        self.macro_log.append({'macro':'binomial','output':out,'n':n,'k':k})
        return out

    def factorial(self,n):
        if n in self.factorials:
            return self.factorials[n]
        tag='factorial'+str(len(self.factorials))
        out=self.new(tag+'.output')
        self.factorials[n]=out
        radius=self.mul(out,self.square(n))
        c=self.binomial(self.add(radius,n),n)
        numerator=self.power(self.add(radius,ONE),n)
        remainder=self.new(tag+'.remainder')
        slack=self.new(tag+'.slack')
        self.eq(self.add(numerator,c),
                self.sum([self.mul(c,out),remainder,ONE]),tag+'.ceiling')
        self.eq(c,self.sum([remainder,slack,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,
                              'radius':'output*n^2'})
        return out

    def environment(self):
        if self.shared_pell is None:
            self.shared_pell={name:self.new('shared_pell.'+name)
                              for name in ('W','A','Z','U','V','B','qB')}
        return self.shared_pell

    def index_certificate(self,k):
        if k in self.pell_indices:
            return self.pell_indices[k]
        tag='index'+str(len(self.pell_indices))
        common=self.environment()
        A,U,V,B=[common[s] for s in ('A','U','V','B')]
        X,S,R=[self.new(tag+'.'+s) for s in ('X','S','R')]
        yk=self.new(tag+'.yk')
        Y=self.add(k,yk)
        self.norm(A,X,Y,tag+'.normA')
        self.norm(B,S,R,tag+'.normB')
        q4=self.new(tag+'.q4minus1')
        fourY=self.mul(FOUR,Y)
        self.eq(B,self.add(ONE,self.mul(fourY,self.add(q4,ONE))),tag+'.B_mod_4Y')
        vd=self.new(tag+'.Vquotient_minus1')
        self.eq(V,self.mul(self.square(Y),self.add(vd,ONE)),tag+'.V_multiple')
        qs=self.new(tag+'.Squotient')
        qr=self.new(tag+'.Rquotient')
        self.eq(S,self.add(X,self.mul(U,qs)),tag+'.S_mod_U')
        self.eq(R,self.add(k,self.mul(fourY,qr)),tag+'.R_mod_4Y')
        self.pell_indices[k]=(X,Y)
        return X,Y

    def power(self,n,k):
        if not self.positive_powers:
            return super().power(n,k)
        key=(n,k)
        if key in self.powers:
            return self.powers[key]
        if self.finalized:
            raise ValueError('cannot add power after finalization')
        tag='pow'+str(len(self.powers))
        start=len(self.variables)
        m=self.new(tag+'.output')
        self.powers[key]=m
        self.power_arguments.append((n,k))
        A=self.environment()['A']
        X,Y=self.index_certificate(k)
        gap=self.new(tag+'.gap')
        T=self.sum([m,gap,ONE])
        quotient=self.new(tag+'.quotient')
        self.eq(self.add(X,self.mul(Y,n)),
                self.sum([self.mul(Y,A),m,self.mul(T,quotient)]),tag+'.power_congruence')
        self.row([(2,[A,n]),(-1,[T]),(-1,[n,n]),(-1,[])],tag+'.T_definition')
        self.macro_log.append({'macro':'power','output':m,'base':n,'exponent':k,
                              'first_variable':start,'end_variable':len(self.variables)})
        return m

    def finalize(self):
        if self.finalized: raise ValueError('already finalized')
        if not self.power_arguments: raise ValueError('empty positive power family')
        self.row([(1,[self.shared_digit_limit])]+[(-1,[n]) for n in self.binomial_upper_arguments],
                 'shared_digits.global_limit')
        c=self.environment()
        W,A,Z,U,V,B,qB=[c[s] for s in ('W','A','Z','U','V','B','qB')]
        row=[(1,[W])]
        for n,k in self.power_arguments:
            row.extend([(-1,[n]),(-1,[k])])
        self.row(row,'shared_pell.global_bound')
        self.norm(A,U,V,'shared_pell.auxiliary_norm')
        self.norm(self.add(W,ONE),A,self.mul(W,Z),'shared_pell.growth_norm')
        self.eq(B,self.add(A,self.mul(U,qB)),'shared_pell.B_mod_U')
        self.finalized=True
