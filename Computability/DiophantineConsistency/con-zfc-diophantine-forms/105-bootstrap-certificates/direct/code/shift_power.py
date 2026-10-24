"""Pell addition transfers a shared index certificate from k to k+2."""
from shared_product_power import SharedProductPowerBuilder
from build_equation import ONE,TWO
class ShiftPowerBuilder(SharedProductPowerBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.derived_indices={}
        self.index_step=None
        self.shift_log=[]
    def _step2(self):
        if self.index_step is None:
            _,A,_=self._scale()
            D=self.new('shared.delta')
            self.eq(self.square(A),self.add(D,ONE),'shared.delta_definition')
            P=self.add(self.mul(TWO,D),ONE)
            Q=self.mul(TWO,A)
            self.index_step=D,P,Q
        return self.index_step
    def _index(self,k):
        if k in self.derived_indices:return self.derived_indices[k]
        lookup={out:(op,a,b) for (op,a,b),out in self.cache.items()}
        expression=lookup.get(k)
        if expression is not None and expression[0]=='add' and expression[1]==TWO:
            base=expression[2]
            X,Y=super()._index(base)
            D,P,Q=self._step2()
            X2=self.add(self.mul(P,X),self.product([Q,D,Y]))
            Y2=self.add(self.mul(Q,X),self.mul(P,Y))
            self.derived_indices[k]=(X2,Y2)
            self.shift_log.append({'base':base,'shifted':k,'delta':D,'P':P,'Q':Q,'old':[X,Y],'new':[X2,Y2]})
            return X2,Y2
        return super()._index(k)
    def sharing_census(self):
        data=super().sharing_census()
        data['shifted_indices']=len(self.derived_indices)
        return data
