"""Local factorial/radix overrides for the authenticated 407 source engine."""
from reuse_radix import AdditiveReusedRadixBuilder
from build_equation import ONE


class ProjectedRadiusBuilder(AdditiveReusedRadixBuilder):
    radius_mode='both'

    def factorial(self,n):
        if n in self.factorials:return self.factorials[n]
        if self.factorials and self.radius_mode=='H-only':return super().factorial(n)
        tag='factorial'+str(len(self.factorials));out=self.new(tag+'.output')
        self.factorials[n]=out
        rho=self.mul(out,self.square(n))
        C=self.binomial(self.add(rho,n),n);V=self.power(self.add(rho,ONE),n)
        r=self.new(tag+'.remainder');s=self.new(tag+'.slack')
        self.eq(self.add(V,C),self.sum([self.mul(C,out),r,ONE]),tag+'.ceiling')
        self.eq(C,self.sum([r,s,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,'radius':rho,
                               'radius_rule':'output*n^2'})
        data={'input':n,'output':out,'radius':rho,'binomial':C,'numerator':V}
        if not hasattr(self,'new_factorial_data'):self.new_factorial_data=[]
        self.new_factorial_data.append(data)
        if not hasattr(self,'factorial_radix'):
            self.factorial_radix={'H':n,'rho':rho,'numerator':V,'factorial':out}
        return out

    def finalize_binomials(self):
        if getattr(self,'binomials_finalized',False):raise ValueError('repeated finalization')
        self.binomials_finalized=True
        moduli={r[2]for r in self.range_requests}
        if len(moduli)!=1:raise ValueError('one common range modulus required')
        B=next(iter(moduli));rcount=len(self.range_requests)
        aggregate=self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(('c',rcount),B),
                self.add(self.sum(n for n,_,_,_ in self.range_requests),aggregate),
                'crt.aggregate_representative_bound')
        numerators=[r['numerator']for r in self.new_factorial_data]
        radix_power=self.sum(numerators)
        q=self.mul(B,self.add(radix_power,ONE))
        for i,((n,k),out)in enumerate(self.binomials.items()):
            tag='choose'+str(i)
            numerator=self.power(self.add(q,ONE),n);den=self.power(q,k)
            h,r,rs,os=[self.new(tag+'.'+s)for s in('high','remainder','rslack','oslack')]
            self.eq(numerator,self.add(self.mul(den,self.add(self.mul(q,h),out)),r),tag+'.digit')
            self.eq(den,self.sum([r,rs,ONE]),tag+'.remainder_bound')
            self.eq(q,self.sum([out,os,ONE]),tag+'.digit_bound')
        for i,(n,k,B,label)in enumerate(self.range_requests):
            num=self.power(self.add(q,ONE),n);den=self.power(q,k)
            h,r,s=[self.new('range'+str(i)+'.'+role)for role in('quotient','remainder','slack')]
            self.eq(num,self.add(self.product([den,B,h]),r),label+'.quotient_multiple')
            self.eq(den,self.sum([r,s,ONE]),label+'.remainder_bound')
        self.radix_data={'upper_atoms':list(dict.fromkeys([n for n,k in self.binomials]+[n for n,_,_,_ in self.range_requests])),
                         'radix':q,'radix_multiple':B,'factorial_radix':self.factorial_radix,
                         'aggregate_range_count':rcount,'aggregate_slack':aggregate,
                         'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests),
                         'new_factorial_numerators':numerators,'radius_mode':self.radius_mode}
