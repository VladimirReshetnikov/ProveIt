#!/usr/bin/env python3
"""Bind every derived fixed coefficient to the complete sibling compiler tuple."""
from pathlib import Path
import gzip, hashlib, json

ROOT=Path(__file__).resolve().parent

def evaluate_recipe(terms,ports):
    ans=0
    for term in terms:
        v=term['coefficient']
        for x,e in zip(ports,term['powers']):v*=x**e
        ans+=v
    return ans

def load_fixed():
    source=json.loads((ROOT/'source_data.json').read_text())
    base=ROOT.parent/'compiler'
    files=['beta','K','MC','MF_source']
    ports=[int.from_bytes(gzip.decompress((base/'coefficients'/(name+'.bin.gz')).read_bytes()),'little') for name in files]
    bnd=source['coefficient_bound_C']
    C=bnd['constant']+evaluate_recipe(bnd['positive_terms'],ports)
    exponent=(2048*C).bit_length()
    fixed={name:evaluate_recipe(recipe,ports) for name,recipe in source['fixed_recipes'].items()}
    assert C>0 and all(abs(x)<C for x in fixed.values())
    fixed['kappa']=1<<exponent
    assert fixed['kappa']>2048*C
    return source,fixed,C,exponent

def main():
    source,fixed,C,exponent=load_fixed()
    raw=fixed['kappa'].to_bytes((exponent+8)//8,'little')
    (ROOT/'kappa.bin.gz').write_bytes(gzip.compress(raw,mtime=0))
    receipt={'instance':'wang943-complemented77-length8807-prime56611',
             'native_binding':'../compiler/COEFFICIENT_BINDING.json',
             'fixed_recipe_file':'source_data.json','C_bit_length':C.bit_length(),
             'kappa_exponent':exponent,'kappa_definition':'2^%d'%exponent,
             'kappa_raw_bytes':len(raw),'kappa_sha256':hashlib.sha256(raw).hexdigest(),
             'strict_bound':'kappa > 2048*C > 2048*abs(each weighted quadratic coefficient)',
             'derived_coefficient_count':len(fixed)-1,
             'derived_coefficients':{name:{'sign':(x>0)-(x<0),'absolute_bit_length':abs(x).bit_length(),
                    'magnitude_sha256':hashlib.sha256(abs(x).to_bytes((abs(x).bit_length()+7)//8,'little')).hexdigest()}
                    for name,x in fixed.items() if name!='kappa'}}
    (ROOT/'COEFFICIENT_BINDING.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('instance','C_bit_length','kappa_exponent','derived_coefficient_count')}))

if __name__=='__main__':main()
