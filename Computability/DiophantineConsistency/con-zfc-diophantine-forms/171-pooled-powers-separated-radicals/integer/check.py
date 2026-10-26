#!/usr/bin/env python3
"""Independent finite checker; imports no producer or search code.
The credited check_core and audit_projection use separate verification paths.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys,zipfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from check_core import *
import audit_projection as radical
import check_frame_independent
ROOT=Path(__file__).resolve().parent

def check_beta(old,new,cert):
 rs=rows(old);names={v['name']:i for i,v in enumerate(old['variables'])};m=names['beta.odd_square_multiplier'];w=names['beta.odd_square_root_half'];f=names['crt.growth_majorant_F'];y=names['y'];g=cert['old_guard_row']
 guard=plus(V(m),C(-1),k(-4,V(w)),k(-4,times(V(w),V(w))));edited=plus(V(m),C(-1),k(-2,V(w)));replacement=plus(C(1),k(2,V(w)))
 need(rs[g]==guard==P(cert['old_guard']),'old square multiplier row')
 need(P(cert['edited_guard'])==edited,'new odd-linear guard')
 need(P(cert['replacement'])==replacement,'new multiplier expression')
 need((m,w,f,y)==tuple(cert[s]for s in ['multiplier_coordinate','parameter_coordinate','F_coordinate','stored_y_coordinate']),'beta coordinate binding')
 need(P(cert['actual_y'])==plus(V(y),C(-1)),'actual y is stored minus one')
 product=plus(V(y),C(-1),k(-1,times(V(f),V(m))))
 need(sum(r==product or r==k(-1,product)for r in rs)==1,'beta product identity')
 keep=[i for i in range(len(old['variables']))if i!=m];ren={i:j for j,i in enumerate(keep)};need(keep==cert['retained_coordinates'],'beta retained chart')
 want=[renumber(pull(r,{m:replacement}),ren)for j,r in enumerate(rs)if j!=g]
 require_rows(rows(new),want,'odd-linear contraction')
 namesnew=[dict(old['variables'][i])for i in keep];namesnew[ren[w]]={'name':'beta.odd_linear_parameter','kind':'unrestricted_integer'};need(new['variables']==namesnew,'beta variable chart')
 oldmap=plus(k(2,V(w)),k(2,times(V(w),V(w))));need(P(cert['old_witness_parameter_map'])==oldmap,'old-square witness map')
 need(pull(edited,{m:plus(C(1),k(4,V(w)),k(4,times(V(w),V(w)))),w:oldmap})=={},'old-square map identity')

def check_row_basis(old,new,cert):
 out=radical.row_operations(old,cert);need(out==new,'row basis target')

def run_mutations(old,pool,cert,frame,oldbeta,newbeta,betacert):
 results=[]
 def reject(label,fn):
  try:fn()
  except (ValueError,KeyError,IndexError,TypeError):results.append(label)
  else:raise ValueError('accepted deliberate corruption '+label)
 for field in ['base','T','H','S']:
  c=copy.deepcopy(cert);c['groups'][0][field][0][0]+=1
  reject('pool '+field,lambda c=c:check_pools(old,pool,c,frame))
 c=copy.deepcopy(cert);c['groups'][1]['modulus_expression'][0][0]+=1
 reject('q modulus offset',lambda:check_pools(old,pool,c,frame))
 fr=copy.deepcopy(frame);fr['row_combination'][0][1]+=1
 reject('retained square frame row',lambda:check_pools(old,pool,cert,fr))
 fr=copy.deepcopy(frame);fr['atoms'][0]['terms'][0][0]+=1
 reject('square frame atom',lambda:check_pools(old,pool,cert,fr))
 c=copy.deepcopy(betacert);c['actual_y'][0][0]+=1
 reject('stored y offset',lambda:check_beta(oldbeta,newbeta,c))
 c=copy.deepcopy(betacert);c['replacement'][0][0]+=1
 reject('odd-linear contraction',lambda:check_beta(oldbeta,newbeta,c))
 return results

def main():
 pins=read(ROOT/'SOURCE_BINDINGS.json');need(all(digest(ROOT/p)==h for p,h in pins['local_pins'].items()),'source hashes')
 with zipfile.ZipFile(ROOT/'inherited/ConZFC_Strict_Horizons_2026-10-25.zip') as z:
  for local,member in pins['archive_members'].items():need(z.read(member)==(ROOT/local).read_bytes(),'literal archived source '+local)
 report={'status':'PASS','branches':[],'proof_scope':'Finite identities, literal frames, maps and coefficients; ordinary unbounded proof is in PROOF.md.'}
 for source_n in [235,236]:
  pn=source_n-11;rn=pn-6;bn=rn-1
  paths=[ROOT/'sources'/f'strict{source_n}.json',ROOT/f'pooled{pn}'/'equation.json',ROOT/f'differences{pn}'/'equation.json',ROOT/f'radical{rn}'/'equation.json',ROOT/f'beta{bn}'/'equation.json']
  eq=[read(p)for p in paths];certp=read(paths[1].parent/'pool_certificate.json');certs=read(paths[2].parent/'shear_certificate.json');certr=read(paths[3].parent/'projection_certificate.json');certb=read(paths[4].parent/'beta_certificate.json');frame=read(ROOT/'sources'/f'frame{source_n}.json')
  interface=read(ROOT/'sources'/f'strict{source_n}_interface.json');names={v['name']:i for i,v in enumerate(eq[0]['variables'])}
  if 'add.380'in names:h=V(names['add.380'])
  else:
   rec=next(x for x in interface['projections']if x['name']=='add.380');mapping={i:j for j,i in enumerate(interface['retained_variables'])};h=renumber(P(rec['replacement']),mapping)
  frame['verified_h_binding']=terms(h)
  for e in eq:validate_equation(e)
  need(certp['parent_equation_sha256']==digest(paths[0])==frame['source_sha256'],'pool source pin')
  need(certs['parent_equation_sha256']==digest(paths[1]),'shear source pin')
  need(certb['source_sha256']==digest(paths[3]),'beta source pin')
  frame_audit=check_frame_independent.check(paths[0]);need(frame_audit['atom_count']==34 and len(frame_audit['requests_covered'])==17,'independent all-request frame audit')
  check_pools(eq[0],eq[1],certp,frame);check_shear(eq[1],eq[2],certs)
  need(certs['orientation_row']not in [n for _,n,_ in certs['norm_subtractions']],'row edit cannot subtract itself')
  cur=eq[2]
  for step in certr['steps']:cur=radical.one_step(cur,step)
  need(cur==eq[3],'complete radical composition');need(len(certr['steps'])==6,'six radical steps')
  check_beta(eq[3],eq[4],certb)
  stage_metrics=[]
  for path,e in zip(paths[1:],eq[1:]):
   met,ex=measure(e);mp=path.parent/('metrics.json'if 'radical'in path.parent.name else 'METRICS.json');record=read(mp)
   need(all(record[k]==v for k,v in met.items()),'stage metric '+str(path));need(ex==P(read(path.parent/'expanded_polynomial.json')['terms']),'stage expansion '+str(path));stage_metrics.append(met)
  endpoints=[]
  for name in [f'integer{bn}',f'integer{bn}_sparse']:
   dest=ROOT/name;end=read(dest/'equation.json');cert=read(dest/'row_certificate.json');validate_equation(end);check_row_basis(eq[4],end,cert);met,ex=measure(end);need(ex==P(read(dest/'expanded_polynomial.json')['terms']),'final expansion');need(all(read(dest/'metrics.json')[k]==v for k,v in met.items()),'final metrics');endpoints.append({'name':name,**met})
  controls=run_mutations(eq[0],eq[1],certp,frame,eq[3],eq[4],certb)
  controls+=['radical:'+r['mutation']for r in radical.mutation_controls(eq[2],certr['steps'][0])]
  report['branches'].append({'source':source_n,'frame_atoms':34,'pooled_requests':[11,3],'radical_steps':6,'stages':stage_metrics,'endpoints':endpoints,'rejected_mutations':controls})
 return report
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--receipt',type=Path);a=p.parse_args();result=main();s=json.dumps(result,indent=2)+'\n';print(s,end='')
 if a.receipt:a.receipt.write_text(s)
