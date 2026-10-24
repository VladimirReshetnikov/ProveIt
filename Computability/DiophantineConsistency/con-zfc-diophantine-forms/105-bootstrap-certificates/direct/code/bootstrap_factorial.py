"""A polynomial self-scaled radius serves the first factorial and every smaller one.

The caller proves that its first factorial argument dominates all later ones.
This concrete caller requests H! followed by t!, with H>=t>=1.
"""
from shared_product_power import SharedProductPowerBuilder
from build_equation import ONE,TWO
class BootstrapFactorialBuilder(SharedProductPowerBuilder):
    radius_mode="square"
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.factorial_radius=None
        self.factorial_radius_bound=None
        self.factorial_radius_log=[]
    def factorial(self,n):
        if n in self.factorials:return self.factorials[n]
        tag=f'factorial{len(self.factorials)}'
        out=self.new(tag+'.output')
        self.factorials[n]=out
        if self.factorial_radius is None:
            self.factorial_radius_bound=n
            self.factorial_radius=(self.square(out) if self.radius_mode=="square"
                                   else self.mul(self.square(n),out))
        radius=self.factorial_radius
        c=self.binomial(self.add(radius,n),n)
        numerator=self.power(self.add(radius,ONE),n)
        remainder,slack=self.new(tag+'.remainder'),self.new(tag+'.slack')
        self.eq(self.add(numerator,c),self.sum([self.mul(c,out),remainder,ONE]),tag+'.ceiling')
        self.eq(c,self.sum([remainder,slack,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,'shared_radius':radius})
        self.factorial_radius_log.append({'n':n,'bound':self.factorial_radius_bound,'radius':radius})
        return out
