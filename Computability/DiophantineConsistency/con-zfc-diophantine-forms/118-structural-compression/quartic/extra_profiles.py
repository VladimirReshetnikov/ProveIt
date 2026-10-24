#!/usr/bin/env python3
from build_pair_guards import *

def main():
    census={}
    raw=read('pair69/parent.json')
    old=read('factorial-radius-output-sign-profile_compact_parent.json')
    domain=read('factorial-radius-output-sign-profile_compact_domain.json')
    compact,newdomain=make_parent(old,domain)
    compact['variant']='shared_modulus_pair69_compact'
    write('pair69_compact/parent.json',compact);write('pair69_compact/domain.json',newdomain)
    configs=[('old75_compact/support32',old,32,None,False),
        ('pair69_compact/support32',compact,32,None,False),
        ('pair69/support16_affine2',raw,16,2,False),
        ('pair69/support32_quadratic_first',raw,32,None,True)]
    for name,eq,cap,affine,qfirst in configs:
        out,cert,metrics=engine.optimize(eq,max_support=cap,affine_support=affine,quadratic_first=qfirst)
        normalize_projection_metadata(out,cert)
        engine.verify(eq,out,cert)
        if cert['unconstrained_removed']:raise ValueError('unconstrained deletion')
        write(name+'/equation.json',out);write(name+'/projection.json',cert);write(name+'/polynomial.json',engine.expand(out))
        census[name]=metrics;print(name,metrics,flush=True)
    write('EXTRA_CENSUS.json',census)

if __name__=='__main__':main()
