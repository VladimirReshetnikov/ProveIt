"""Deterministic height-one construction; semantic final certificate is minimal."""
import copy
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import contract
from network_compile import run
from spread import spread
from flow_contract import compress
from guard_dummies import guarded
from anchored_cycles import homogenize

def recontract(a,c,source):
 a=copy.deepcopy(a);c=copy.deepcopy(c)
 keep=[i for i,v in enumerate(a['variables']) if v['kind'] not in ('equality_dummy','unit_dummy')];ren={i:j for j,i in enumerate(keep)}
 a['variables']=[a['variables'][i] for i in keep]
 for v in a['variables']:
  if v['kind']=='alias':v['kind']='private'
 for p in c['products']:p['factors']=[ren[i] for i in p['factors']]
 for e in c['edges']:e['monomial']=[ren[i] for i in e['monomial']]
 c['equality_cycles']=[];c['unit_path']=[]
 contract.build.compile_graph=lambda *args:(a,c)
 b,d=contract.contract(source,len(c['hub_vertices']),0,3)
 b['schema']='network-height-one-quartic-v1';d['schema']='network-height-one-certificate-v1';b['metrics'].update(d['network_pairing'])
 return spread(b,d)

def clean(a,c):
 c={k:v for k,v in c.items() if k in ['schema','source_sha256','normalization','products','vertices','edges','row_blocks','hub_vertices','equality_cycles','unit_path','network_pairing']}
 ms=a['metrics'];drop=['removed_equality_dummies','polarized_products','removed_flow_variables','unit_guard_removed_dummies']
 for k in drop:ms.pop(k,None)
 ms['unit_product_cycle_classes']=sum(x.get('mode')=='unit_product_cycle' for x in c['equality_cycles'])
 ms['quartic_pair_classes']=sum(x.get('mode')=='quartic_pair' for x in c['equality_cycles'])
 ms['equality_dummies']=sum(x['kind']=='equality_dummy' for x in a['variables'])
 return a,c

def build(source,hubs,seed,digest,flow=False,split=False,constant_products=False,scale_chains=False,normalization_profile=None):
 from split_normalize import normalize as split_normalize
 normalizer=split_normalize if split else None
 if constant_products:
  from product_constants import normalize as product_normalize
  normalizer=lambda s:product_normalize(s,split=split,chain=scale_chains)
 if normalization_profile is not None:
  kind=normalization_profile['kind'];params={k:v for k,v in normalization_profile.items() if k!='kind'}
  if kind=='fused':from fused_normalize import normalize as chosen
  elif kind=='inline_constants':from inline_constants import normalize as chosen
  elif kind=='inline_scales':from inline_scales import normalize as chosen
  else:raise ValueError('Unknown normalization profile')
  normalizer=lambda s:chosen(s,split=split,**params)
 a,c=spread(*run(source,hubs,seed,normalizer=normalizer));c['source_sha256']=digest
 stages={'baseline':(copy.deepcopy(a),copy.deepcopy(c))}
 if flow:
  a,c=compress(a,c,policy='support_nonincrease');stages['flow']=(copy.deepcopy(a),copy.deepcopy(c))
  a,c=recontract(a,c,source);stages['recontract']=(copy.deepcopy(a),copy.deepcopy(c))
 a,c=guarded(a,c);stages['guarded']=(copy.deepcopy(a),copy.deepcopy(c))
 a,c=homogenize(a,c);stages['anchored']=(copy.deepcopy(a),copy.deepcopy(c))
 return *clean(a,c),stages
