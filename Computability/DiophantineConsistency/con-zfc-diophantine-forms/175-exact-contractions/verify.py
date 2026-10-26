#!/usr/bin/env python3
"""Independently check every frozen monic contraction and public equation.

Uses only the Python standard library.  It does not search for integer zeros.
"""
from pathlib import Path
import argparse, json, hashlib, importlib.util, subprocess, sys

ROOT=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('independent',ROOT/'code/verify_contractions.py')
CHECK=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CHECK)

def demand(c,m):
 if not c:raise ValueError(m)

def verify_profiles():
 result=[]
 for profile in json.loads((ROOT/'PROFILES.json').read_text()):
  cp=ROOT/profile['certificate'];cert=json.loads(cp.read_text())
  sp=cp.parent/cert['source'];raw=sp.read_bytes();source=json.loads(raw)
  demand(hashlib.sha256(raw).hexdigest()==cert['source_sha256'],'source hash mismatch')
  ep=ROOT/profile['equation'];endpoint=json.loads(ep.read_text())
  xp=ep.parent/'expanded_polynomial.json'
  checked,expanded=CHECK.replay(source,cert,with_expansion=xp.exists())
  live=checked['retained_original_variables'];mapping={old:new for new,old in enumerate(live)}
  def remap(terms):return [[c,[mapping[v] for v in m]] for c,m in terms]
  demand(len(endpoint['variables'])==len(live),'incorrect public arity')
  demand([v['source_index'] for v in endpoint['variables']]==live,'incorrect coordinate map')
  demand(endpoint['domain']=='unrestricted integers','incorrect domain')
  demand(endpoint['polynomial']=='sum(square(row) for row in residuals)','incorrect aggregation')
  demand([r['terms'] for r in endpoint['residuals']]==[remap(r['terms']) for r in cert['rows']],
         'public residuals differ from exact endpoint')
  demand([r['source_row'] for r in endpoint['residuals']]==[r['source_row'] for r in cert['rows']],
         'public residual identities differ')
  demand(hashlib.sha256(ep.read_bytes()).hexdigest()==profile['equation_sha256'],'public hash mismatch')
  metrics=json.loads((ep.parent/'metrics.json').read_text())
  for k,v in checked['metrics'].items():demand(metrics.get(k)==v,'metric mismatch: '+k)
  demand(metrics['polynomial_degree']==2*checked['metrics']['maximum_residual_degree'],'degree mismatch')
  if xp.exists():
   expansion=json.loads(xp.read_text())
   demand(expansion['variables']==len(live),'expanded ambient arity mismatch')
   demand(expansion['terms']==remap(CHECK.serialize(expanded)),'collected coefficient mismatch')
  controls=CHECK.corruption_controls(source,cert)
  result.append({'profile':profile['name'],'metrics':metrics,
                 'unit_projections':len(cert['steps']),'corruptions_rejected':len(controls),
                 'zero_set_bijection':'exact integral polynomial restoration'})
 return result

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--receipt',type=Path)
 ap.add_argument('--components',action='store_true',help='also verify principal92, compact, supporting research, and printed equation')
 args=ap.parse_args();profiles=verify_profiles()
 components=[]
 if args.components:
  for rel in ['principal92/verify.py','compact/verify.py','compact/radix47/verify.py',
              'research/oriented_pooling209/verify.py',
              'research/factored_radix/check_factored_radix.py',
              'research/factored_radix/replay_factored_radical.py',
              'code/check_report.py']:
   p=ROOT/rel
   options=['-O'] if not __debug__ else []
   done=subprocess.run([sys.executable,*options,'-B',str(p)],cwd=p.parent,
                       text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   demand(done.returncode==0,rel+' failed:\n'+done.stdout)
   components.append({'script':rel,'returncode':done.returncode,'output':done.stdout})
 receipt={'status':'pass','profiles':profiles,'components':components,
          'proof_boundary':'Finite exact polynomial verification; inherited unbounded calibration is not re-formalized.'}
 if args.receipt:
  args.receipt.parent.mkdir(parents=True,exist_ok=True)
  args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'status':'pass','profiles':[(p['profile'],p['metrics']['polynomial_degree']) for p in profiles],
                   'component_count':len(components)},indent=2))

if __name__=='__main__':main()
