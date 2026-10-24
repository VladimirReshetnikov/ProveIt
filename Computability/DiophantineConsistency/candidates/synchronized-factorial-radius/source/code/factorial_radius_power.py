"""Shared power frame with the separately proved self-bounding factorial."""
from shared_product_power import SharedProductPowerBuilder
from build_equation import ONE


class FactorialRadiusPowerBuilder(SharedProductPowerBuilder):
    def factorial(self,n):
        if n in self.factorials:
            return self.factorials[n]
        tag='factorial'+str(len(self.factorials))
        out=self.new(tag+'.output')
        self.factorials[n]=out
        radius=self.mul(out,self.square(n))
        choose=self.binomial(self.add(radius,n),n)
        numerator=self.power(self.add(radius,ONE),n)
        r=self.new(tag+'.remainder')
        s=self.new(tag+'.slack')
        self.eq(self.add(numerator,choose),
                self.sum([self.mul(choose,out),r,ONE]),tag+'.ceiling')
        self.eq(choose,self.sum([r,s,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,
                               'radius':radius,'radius_rule':'output*n^2'})
        return out
