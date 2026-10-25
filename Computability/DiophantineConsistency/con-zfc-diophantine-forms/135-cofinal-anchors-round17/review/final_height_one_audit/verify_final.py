"""Read-only independent audit of the three frozen Round17 height-one polynomials.
Standard library only; imports neither a producer nor an incoming checker.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
import argparse,hashlib,json,re,sys
from audit_height_one import audit,require
from audit_affine_factor import verify as verify_factor

PINS={
 'compact793':(287,'strict_grouped_centered',793,51982,'5766ff7a2050e3a7eae54ada51a898f6d9e4d42a5c5f34bec036ed4d4e400071','b25b3715a8932bae0db7f88b3efd51950e52aa000b69d038db329091a4d13178'),
 'balanced806':(287,'strict_grouped_centered',806,23719,'5139cac2a11e4391b129e1f7499492b2eae2f63a6bead2ff07ea7d243fc13117','3afdb49e63d6ff16cc2fe5dbf1bbd10250b4017ef0f957c86b832092debbf06f'),
 'sparse994':(309,'strict_sparse_centered',994,11744,'db9a43aae243939c071c48f5c0368688cbac340f7a0bc42a7ae765237fcf8f1f','aabbbe970289aadb1bb9e38adbd4ad4e6858bfed9eb7160fdf874f47393569fe')}
SOURCE_PINS={287:'e342eee770c4d8ec4311fd87d65b02b97171ab39152151c97a64b97c9890b11b',309:'b867f70b15340736a7caaeafacbe9de35adb5422fe7ab36964a444542919333d'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def literal_check(artifact,path):
 lines=path.read_text().splitlines();require(lines[:2]==[f"Integer variables x_1 through x_{len(artifact['variables'])}.",'The following literal polynomial is equal to zero:'],'literal preface')
 require(lines[-1]=='=0','literal zero equation');parsed=[]
 for line in lines[2:-1]:
  require(line and line[0] in '+-','literal term sign');c=1 if line[0]=='+' else -1;body=line[1:];m=[]
  if body!='1':
   for fact in body.split('*'):
    z=re.fullmatch(r'x_([1-9][0-9]*)(?:\^([1-9][0-9]*))?',fact);require(z is not None,'literal monomial grammar');i=int(z.group(1))-1;e=int(z.group(2) or '1');require(i<len(artifact['variables']) and e<=4,'literal coordinate/exponent');m.extend([i]*e)
  parsed.append([c,sorted(m)])
 require(parsed==artifact['terms'],'complete literal equation roundtrip');return len(parsed)
def graph_mutations(source,art,cert,digest):
 out=[]
 def run(name,fn):
  s,a,c=deepcopy(source),deepcopy(art),deepcopy(cert);fn(s,a,c)
  try:audit(s,a,c,digest)
  except (ValueError,KeyError,IndexError,TypeError):out.append(name)
  else:raise ValueError('Accepted mutation '+name)
 run('coefficient_sign',lambda s,a,c:a['terms'][0].__setitem__(0,-a['terms'][0][0]))
 run('source_row',lambda s,a,c:s['residuals'][0]['terms'][0].__setitem__(0,17))
 run('source_digest',lambda s,a,c:c.__setitem__('source_sha256','0'*64))
 run('cross_logical_alias_merge',lambda s,a,c:c['products'][0]['factors'].__setitem__(0,next(i for i,v in enumerate(a['variables']) if v.get('kind')=='alias' and v.get('normalized_variable')!=c['products'][0]['logical_factors'][0])))
 run('missing_normalized_row',lambda s,a,c:c['normalization']['rows'].pop())
 run('missing_edge',lambda s,a,c:c['edges'].pop())
 run('wrong_edge_sign',lambda s,a,c:c['edges'][0].__setitem__('coefficient',-c['edges'][0]['coefficient']))
 run('duplicate_unit_endpoint',lambda s,a,c:c['unit_path'].__setitem__(-1,c['unit_path'][0]))
 run('missing_alias',lambda s,a,c:next(z for z in c['equality_cycles'] if len(z['aliases'])>2)['aliases'].pop())
 run('false_two_cycle',lambda s,a,c:next(z for z in c['equality_cycles'] if z.get('mode')=='quartic_pair').__setitem__('mode','cycle'))
 return out

def factor_mutations(original,lifted,cert):
 out=[]
 def run(name,fn):
  o,n,c=deepcopy(original),deepcopy(lifted),deepcopy(cert);fn(o,n,c)
  try:verify_factor(o,n,c)
  except (ValueError,KeyError,IndexError,TypeError):out.append(name)
  else:raise ValueError('Accepted factor mutation '+name)
 run('changed_affine_definition',lambda o,n,c:n['residuals'][0]['terms'][1].__setitem__(0,999))
 run('changed_original_residual',lambda o,n,c:o['residuals'][-1]['terms'][0].__setitem__(0,999))
 run('missing_refactored_row',lambda o,n,c:n['residuals'].pop())
 run('wrong_affine_record',lambda o,n,c:c['records'][0]['affine'][0].__setitem__(0,999))
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--release',required=True,type=Path);p.add_argument('--direct',required=True,type=Path);p.add_argument('--output',required=True,type=Path);args=p.parse_args();r=args.release;ledger=read(r/'ENDPOINTS.json');require({x['name'] for x in ledger}==set(PINS),'exact three endpoints');results=[];factors={}
 for name,(num,dirname,nvars,nterms,ph,ch) in PINS.items():
  originalpath=r/f'sources/original{num}.json';originalraw=originalpath.read_bytes();directraw=(args.direct/dirname/'equation.json').read_bytes();require(originalraw==directraw and sha(originalraw)==SOURCE_PINS[num],'exact current direct source binding')
  fd=r/f'sources/refactored{num}';sourceraw=(fd/'source.json').read_bytes();source=json.loads(sourceraw);fc=read(fd/'factor_certificate.json');require(fc['source_sha256']==SOURCE_PINS[num],'factor source binding')
  if num not in factors:
   fr=verify_factor(json.loads(originalraw),source,fc);fr.update(original_sha256=sha(originalraw),refactored_sha256=sha(sourceraw),certificate_sha256=sha((fd/'factor_certificate.json').read_bytes()),mutation_rejections=factor_mutations(json.loads(originalraw),source,fc));factors[num]=fr
  ep=r/'endpoints'/name;pb=(ep/'polynomial.json').read_bytes();cb=(ep/'certificate.json').read_bytes();require(sha(pb)==ph and sha(cb)==ch,'frozen endpoint hashes');art=json.loads(pb);cert=json.loads(cb);rc=audit(source,art,cert,sha(sourceraw));require(rc['variables']==nvars and rc['monomials']==nterms,'selected counts');require(rc['degree']==4 and rc['individual_degree']==4 and rc['coefficient_height']==1 and rc['constant']==1,'degree/height domain')
  entry=next(x for x in ledger if x['name']==name);require(entry['polynomial_sha256']==ph and entry['certificate_sha256']==ch and entry['source_sha256']==sha(originalraw) and entry['refactored_source_sha256']==sha(sourceraw),'endpoint ledger binding');require(read(ep/'metrics.json')==art['metrics']==entry['metrics'],'metrics ledger equality')
  for key in ('variables','monomials','degree','individual_degree','constant','coefficient_height'):require(entry['metrics'][key]==rc[key],'independent metric agreement')
  count=literal_check(art,ep/'polynomial.txt');require(sha((ep/'polynomial.txt').read_bytes())==entry['literal_equation_sha256'],'literal digest')
  rc.update(name=name,original_source_sha256=sha(originalraw),refactored_source_sha256=sha(sourceraw),polynomial_sha256=ph,certificate_sha256=ch,literal_terms_roundtripped=count,mutation_rejections=graph_mutations(source,art,cert,sha(sourceraw)));results.append(rc);print(name,'PASS',nvars,nterms,flush=True)
 out={'status':'pass','optimized':bool(sys.flags.optimize),'scope':'Exact frozen-source bindings, all affine row identities, universal symbolic graph lifts, complete coefficient expansions, literal equations, and corruption controls. Strict source semantics are audited separately.','factor_maps':factors,'endpoints':results,'graph_mutations_rejected':sum(len(x['mutation_rejections']) for x in results),'factor_mutations_rejected':sum(len(x['mutation_rejections']) for x in factors.values()),'checker_closure':{p.name:sha(p.read_bytes()) for p in sorted(Path(__file__).resolve().parent.glob('*.py'))}}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'pass','optimized':out['optimized'],'endpoints':len(results),'graph_mutations_rejected':out['graph_mutations_rejected'],'factor_mutations_rejected':out['factor_mutations_rejected']}))
if __name__=='__main__':main()
