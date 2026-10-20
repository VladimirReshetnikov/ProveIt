#!/usr/bin/env python3
"""Exact 12x7 source stacks; no allocator, runtime, or calculus calibration."""
from model import *
import argparse,time
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args();assert __debug__
args.output.mkdir(parents=True,exist_ok=False)
base=HERE.parent/'k219-pivot-fusion/results/membership-protected'
variants=sorted(p for p in base.glob('*/sites.json'))
assert len(variants)==12
accepted=freeze(json.loads((BASE/'new_equality_macro.json').read_text()))
hits=list(map(freeze,json.loads(HITS.read_text())))
assert hits[10]==accepted
D5,D6,I6,C1,C2,B1=('CD',5),('CD',6),('CI',6),('CC',1),('CC',2),('CB',1)
U=((D6,C2),B1);assert hits[11]==(accepted[0],((D5,I6),U))
indices=(0,1,2,3,12,10,11);records=[];parents=[];best=999;started=time.monotonic()
def fast_parse(rows):
 trie={}
 for p,o,r in rows:
  n=trie
  for b in p:
   assert 'leaf' not in n;n=n.setdefault(b,{})
  assert not n;n['leaf']=(o,r)
 def visit(n):
  if 'leaf' in n:assert len(n)==1;return n['leaf']
  assert set(n)=={'0','1'};return visit(n['0']),visit(n['1'])
 t=visit(trie);assert leaves(t)==[tuple(r) for r in rows];return t
for file in variants:
 raw=file.read_bytes();rows=json.loads(raw);tree=fast_parse(rows);parentname=file.parent.name
 assert len(rows)==4791 and graph(rows)==arithmetic_graph(rows)
 parents.append({'name':parentname,'path':str(file.relative_to(REPO)),'sha256':hashlib.sha256(raw).hexdigest(),'metrics':metrics(tree)})
 for index in indices:
  paths=[];new=hits[index]
  def subst(t,p=''):
   if t==accepted:paths.append(p);return new
   return t if leaf(t) else (subst(t[0],p+'0'),subst(t[1],p+'1'))
  changed=subst(tree);assert len(paths)==4
  rr=leaves(changed);g=graph(rr);assert g==arithmetic_graph(rr)
  assert all(0<=j<len(rr) for _,_,ts in g for j in ts)
  if index==10:assert rr==[tuple(r) for r in rows]
  expected=len(rows)+4*(len(leaves(new))-len(leaves(accepted)))
  assert len(rr)==expected
  name=f'{parentname}-eq{index:02d}';out=args.output/name;out.mkdir()
  encoded=(json.dumps(rr,separators=(',',':'))+'\n').encode();(out/'sites.json').write_bytes(encoded)
  m=metrics(changed);record={'name':name,'membership_parent':parentname,'equality_hit':index,'metrics':m,'replaced_paths':paths,'source_sha256':hashlib.sha256(encoded).hexdigest(),'source_file':name+'/sites.json','cfg_leaf_count':len(g),'cfg_guarded_edges':sum(len(ts) for _,_,ts in g),'cfg_resolvers_agree':True,'source_contract':'all-natural clean equality; relative to supplied membership source','membership_calibration':'OPEN','binary_validation':'NOT_RUN'}
  records.append(record)
  if m['dag_nodes']<best:best=m['dag_nodes'];print('BEST',best,name,m,flush=True)
 print(parentname,[(r['equality_hit'],r['metrics']['dag_nodes']) for r in records[-7:]],flush=True)
result={'status':'ALL84_LITERAL_STACKS_AND_CFGS_PASS','scope':'Exact source substitution plus two full CFG constructions. Ordinary equality contract does not discharge membership-calculus calibration; no binary allocation/runtime/startup executed.','parents':parents,'hits_library':{'path':str(HITS.relative_to(REPO)),'sha256':hashlib.sha256(HITS.read_bytes()).hexdigest()},'equality_hits':list(indices),'count':len(records),'best_dag':best,'best_sources':[r['name'] for r in records if r['metrics']['dag_nodes']==best],'records':records,'seconds':time.monotonic()-started,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
assert len(records)==84
(args.output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('parents','records')},indent=2),flush=True)
