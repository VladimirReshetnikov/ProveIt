"""Shared self-bounding factorial radius with recycled low-digit radix."""
from pathlib import Path
import sys,json,hashlib,argparse
sys.path.insert(0,str(Path(__file__).resolve().parent))
from norm_transform import NormProductBuilder,ROOT
import build_projected
from build_equation import ONE

class SharedRadiusBuilder(NormProductBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.shared_factorial_radius=None
        self.factorial_certificates=[]
    def factorial(self,n):
        if n in self.factorials:return self.factorials[n]
        tag='fact'+str(len(self.factorials))
        out=self.new(tag+'.output')
        self.factorials[n]=out
        first=self.shared_factorial_radius is None
        if first:
            rho=self.mul(out,self.square(n))
            self.shared_factorial_radius=rho
        else:rho=self.shared_factorial_radius
        c=self.binomial(self.add(rho,n),n)
        numerator=self.power(self.add(rho,ONE),n)
        remainder,slack=self.new(tag+'.remainder'),self.new(tag+'.slack')
        self.eq(self.add(numerator,c),self.sum([self.mul(c,out),remainder,ONE]),tag+'.ceiling')
        self.eq(c,self.sum([remainder,slack,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,'shared_selfbounding_radius':True})
        self.factorial_certificates.append({'input':n,'output':out,'radius':rho,'binomial':c,'numerator':numerator,'remainder':remainder,'slack':slack,'selfbounding':first})
        if first:self.factorial_radix={'H':n,'rho':rho,'numerator':numerator,'factorial':out}
        return out

def make(out):
    build_projected.AdditiveReusedRadixBuilder=SharedRadiusBuilder
    b,src,label,local=build_projected.construct()
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'shared_selfbounding_radius_norm_product',True)
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    meta={'powers':[{'base':n,'exponent':k,'output':v} for (n,k),v in b.powers.items()],
          'factorials':b.factorial_certificates,
          'binomials':[{'n':n,'k':k,'output':v} for (n,k),v in b.binomials.items()],
          'ranges':b.range_requests,'radix':b.radix_data,'scale':b.shared_parameters,
          'auxiliary':b.common_index_parameters,'discriminant':b.pell_D,
          'derivations':b.index_derivations,
          'seeds':[{'exponent':k,'pair':v} for k,v in b.seed_indices.items()],
          'indices':[{'exponent':k,'pair':v} for k,v in b.shared_indices.items()],
          'label_majorant':label,'local_majorant':local,
          'variables':b.variables,'rows':b.rows,'gates':b.gates}
    for name,item in [('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics),('norm_compressions.json',b.norm_compressions),('square_product_compressions.json',b.square_product_compressions),('raw_audit_input.json',meta)]:
        (out/name).write_text(json.dumps(item,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(metrics,indent=2))
    print('norms',len(b.norm_compressions),'square products',len(b.square_product_compressions),'seed indices',len(b.seed_indices),'derived indices',len(b.index_derivations))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();make(a.output)
