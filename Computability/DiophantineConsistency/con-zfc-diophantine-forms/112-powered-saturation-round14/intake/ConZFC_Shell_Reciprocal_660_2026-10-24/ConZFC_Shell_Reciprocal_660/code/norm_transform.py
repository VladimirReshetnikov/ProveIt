"""Exact shared-Pell norm compression experiment.

Every use of x^2+y^2=1+a^2*y^2 is replaced by w=a*y and
x^2+y^2=1+w^2. Product-of-squares gates use (product Y)^2.
"""
from pathlib import Path
import sys,json,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1]/'upstream'/'ConZFC_407_888_Quartics'
sys.path.insert(0,str(ROOT/'code'))
import build_projected
from reuse_radix import AdditiveReusedRadixBuilder
from build_equation import ONE,ZERO,TWO

class NormProductBuilder(AdditiveReusedRadixBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.square_sources={}
        self.norm_compressions=[]
        self.square_product_compressions=[]
    def square(self,a):
        q=super().square(a)
        self.square_sources[q]=a
        return q
    def norm(self,a,x,y,label,guard=None):
        if guard is not None:raise ValueError('unguarded norm required')
        w=self.mul(a,y)
        self.row([(1,[x,x]),(1,[y,y]),(-1,[w,w]),(-1,[])],label)
        self.norm_compressions.append({'base':a,'abscissa':x,'ordinate':y,'product':w,'label':label})
    def product(self,values):
        values=list(values)
        if len(values)>=2 and all(v in self.square_sources for v in values):
            roots=[self.square_sources[v] for v in values]
            root=super().product(roots)
            out=self.square(root)
            self.square_product_compressions.append({'squares':values,'roots':roots,'root_product':root,'output':out})
            return out
        return super().product(values)

def make(out):
    build_projected.AdditiveReusedRadixBuilder=NormProductBuilder
    b,src,label,local=build_projected.construct()
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'pell_norm_product_compression',True)
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    for name,item in [('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics),('norm_compressions.json',b.norm_compressions),('square_product_compressions.json',b.square_product_compressions),('gate_ledger.json',{'variables':b.variables,'rows':b.rows,'gates':b.gates})]:
        (out/name).write_text(json.dumps(item,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(metrics,indent=2))
    print('norms',len(b.norm_compressions),'square products',len(b.square_product_compressions))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();make(a.output)
