#!/usr/bin/env python3
"""Build an integer quartic by certified sign inference and monic contraction.
Usage: python build_integer.py --source natural.json --output new-directory
"""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json
from sign_inference import infer_nonnegativity
import terminal_elimination as elimination
from verify_integer import domain

def main(source,output,max_support):
 source=Path(source).resolve();dst=Path(output).resolve()
 if dst.exists() and any(dst.iterdir()):raise ValueError('output must be empty')
 parent_bytes=source.read_bytes();parent=json.loads(parent_bytes)
 if parent['domain']!='nonnegative integers':raise ValueError('source is not natural')
 proof=infer_nonnegativity(parent)
 signed=deepcopy(parent);signed['domain']='unrestricted integers';signed.pop('metrics',None)
 guards=[]
 for v in proof['guard_indices']:
  a,b,c=range(len(signed['variables']),len(signed['variables'])+3)
  signed['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
  signed['residuals'].append({'label':f'nonnegative.{v}','terms':elimination.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
  guards.append({'variable':v,'auxiliary':[a,b,c]})
 digest=lambda x:hashlib.sha256(elimination.canonical_bytes(x)).hexdigest()
 conversion={'parent_sha256':digest(parent),'signed_sha256':digest(signed),'positivity':proof,'guards':guards}
 domain_receipt=domain(parent,signed,conversion)
 target,projection,metrics=elimination.optimize(signed,max_support=max_support)
 review=elimination.verify(signed,target,projection);polynomial=elimination.expand(target)
 dst.mkdir(parents=True,exist_ok=True);(dst/'source_natural.json').write_bytes(parent_bytes)
 # The content digest pins the source; basename is only descriptive provenance.
 pins={'parent_sha256':hashlib.sha256(parent_bytes).hexdigest(),'source_basename':source.name}
 items=[('SOURCE_PINS.json',pins),('guarded.json',signed),('domain_conversion.json',conversion),('equation.json',target),('expanded_polynomial.json',polynomial),('elimination_certificate.json',projection),('BUILD.json',{'metrics':metrics,'domain':domain_receipt,'projection':review})]
 for fn,data in items:(dst/fn).write_bytes(elimination.canonical_bytes(data))
 print(json.dumps({'metrics':metrics,'domain':domain_receipt,'projection':review},indent=2))
if __name__=='__main__':
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--source',type=Path,required=True);a.add_argument('--output',type=Path,required=True);a.add_argument('--max-support',type=int,default=16);x=a.parse_args();main(x.source,x.output,x.max_support)
