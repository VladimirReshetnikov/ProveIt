"""Synchronize the two divisibility families in shared Pell-index certificates."""
from shared_power import SharedPowerBuilder
from build_equation import ONE,FOUR,require


class SharedProductPowerBuilder(SharedPowerBuilder):
    def __init__(self,positive_powers=True,**kwargs):
        super().__init__(positive_powers=positive_powers,**kwargs)
        self.common_index_parameters=None
        self.index_product_finalized=False

    def _auxiliary_index(self):
        if self.common_index_parameters is None:
            _,A,_=self._scale()
            U,V,q4minus1,bq=[self.new("shared_index."+s)
                             for s in("U","V","q4minus1","Bquotient")]
            self.norm(A,U,V,"shared_index.norm")
            B=self.add(ONE,self.mul(self.mul(FOUR,V),self.add(q4minus1,ONE)))
            self.eq(B,self.add(A,self.mul(U,bq)),"shared_index.B_mod_U")
            self.common_index_parameters=U,V,B
        return self.common_index_parameters

    def _index(self,k):
        if k in self.shared_indices:
            return self.shared_indices[k]
        _,A,_=self._scale()
        U,V,B=self._auxiliary_index()
        tag="index"+str(len(self.shared_indices))
        X,Y,S,R=[self.new(tag+"."+s) for s in("X","Y","S","R")]
        yk=self.new(tag+".YminusK")
        self.eq(Y,self.add(k,yk),tag+".index_at_most_Y")
        self.norm(A,X,Y,tag+".norm1")
        self.norm(B,S,R,tag+".norm3")
        fourY=self.mul(FOUR,Y)
        sq,rq=[self.new(tag+"."+s) for s in("Squotient","Rquotient")]
        self.eq(S,self.add(X,self.mul(U,sq)),tag+".S_mod_U")
        self.eq(R,self.add(k,self.mul(fourY,rq)),tag+".R_mod_4Y")
        self.shared_indices[k]=X,Y
        return X,Y

    def finalize_power_frame(self):
        if not self.index_product_finalized:
            require(bool(self.shared_indices),"shared product needs an index")
            U,V,B=self._auxiliary_index()
            productY2=self.product([self.square(Y) for X,Y in self.shared_indices.values()])
            vminus1=self.new("shared_index.Vquotient_minus1")
            self.eq(V,self.mul(productY2,self.add(vminus1,ONE)),
                    "shared_index.V_positive_product")
            self.index_product_finalized=True
        super().finalize_power_frame()

    def sharing_census(self):
        out=super().sharing_census()
        out["common_auxiliary_index_triples"]=int(self.common_index_parameters is not None)
        out["global_index_divisibility_product"]=self.index_product_finalized
        return out
