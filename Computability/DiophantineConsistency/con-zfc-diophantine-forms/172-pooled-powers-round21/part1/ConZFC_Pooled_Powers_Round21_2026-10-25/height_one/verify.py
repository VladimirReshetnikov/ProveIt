#!/usr/bin/env python3
"""Deterministic independent audit and byte-for-byte replay, normal and -O."""
import argparse,copy,hashlib,json,re,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import check_factor,factor_source,literal
from check_network import audit,require

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def bytesof(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()

def parse_literal(text,n):
 lines=text.splitlines();require(lines[0]==f'Integer variables x_1 through x_{n}.','literal variable header');require(lines[1]=='The following literal polynomial is equal to zero:' and lines[-1]=='=0','literal framing');terms=[]
 for line in lines[2:-1]:
  require(line[:1] in ('+','-'),'literal sign');c=1 if line[0]=='+' else -1;mon=[]
  if line[1:]!='1':
   for f in line[1:].split('*'):
    m=re.fullmatch(r'x_([1-9][0-9]*)(?:\^([1-4]))?',f);require(m is not None,'literal syntax');i=int(m[1])-1;e=int(m[2] or '1');require(0<=i<n,'literal index');mon.extend([i]*e)
  terms.append([c,mon])
 return terms

def mutations(src,art,cert,dg):
 rejected=[]
 for kind in ['coefficient','source_hash','source_row_sign','orientation_sign','constructor_sign','paired_sign','missing_occurrence','repeated_occurrence','edge_boundary','alias_binding','missing_tree_edge','unit_path','metric']:
  a,c=copy.deepcopy(art),copy.deepcopy(cert)
  if kind=='coefficient':a['terms'][-1][0]*=-1
  elif kind=='source_hash':c['source_sha256']='0'*64
  elif kind=='source_row_sign':next(r for r in c['normalization']['rows'] if r['kind']=='source')['terms'][0][0]*=-1
  elif kind=='orientation_sign':next(r for r in c['normalization']['rows'] if r['kind']=='source')['orientation']*=-1
  elif kind=='constructor_sign':next(r for r in c['normalization']['rows'] if r['kind']!='source')['terms'][0][0]*=-1
  elif kind=='paired_sign':next(p for p in c['products'] if len(p['bindings'])==2)['bindings'][1][2]*=-1
  elif kind=='missing_occurrence':next(p for p in c['products'] if len(p['bindings'])==2)['bindings'].pop()
  elif kind=='repeated_occurrence':p=next(p for p in c['products'] if len(p['bindings'])==2);p['bindings'][1]=p['bindings'][0][:]
  elif kind=='edge_boundary':e=next(e for e in c['edges'] if e['kind']=='prescribed' and len(c['products'][e['product']]['bindings'])==2);e['head']=c['hub_vertices'][0]
  elif kind=='alias_binding':p=c['products'][0];p['logical_factors'][0]=(p['logical_factors'][0]+1)%len(c['normalization']['variables']) if p['logical_factors'][0] is not None else 0
  elif kind=='missing_tree_edge':c['edges'].pop(next(i for i,e in enumerate(c['edges']) if e['kind']=='free'))
  elif kind=='unit_path':c['unit_path'].pop()
  else:a['metrics']['monomials']+=1
  try:audit(src,a,c,dg)
  except (ValueError,KeyError,IndexError,TypeError):rejected.append(kind)
  else:raise ValueError('Mutation survived: '+kind)
 return rejected

def guarded_mutations(src,art,cert,dg):
 out=[]
 for kind in ['guard_unit','guard_anchor','guard_mode']:
  a,c=copy.deepcopy(art),copy.deepcopy(cert);g=next(g for g in c['equality_cycles'] if g.get('mode')=='unit_product_cycle')
  if kind=='guard_unit':g['unit']=next(i for i,v in enumerate(a['variables']) if i not in c['unit_path'])
  elif kind=='guard_anchor':g['anchor']=next(i for i in range(len(a['variables'])) if i not in g['aliases'])
  else:g['mode']='quartic_pair'
  try:audit(src,a,c,dg)
  except (ValueError,KeyError,IndexError,TypeError):out.append(kind)
  else:raise ValueError('Guard mutation survived: '+kind)
 return out

def anchored_mutations(src,art,cert,dg):
 out=[]
 for kind in ['anchored_unknown_unit','anchored_wrong_alias','anchored_missing_alias','anchored_form_degree','anchored_mode']:
  a,c=copy.deepcopy(art),copy.deepcopy(cert);g=next(g for g in c['equality_cycles'] if g.get('mode')=='anchored_cycle')
  if kind=='anchored_unknown_unit':next(f for f in g['forms'] if len(f)==2)[1]=g['aliases'][0]
  elif kind=='anchored_wrong_alias':g['forms'][0][0]=c['unit_path'][0]
  elif kind=='anchored_missing_alias':
   for f in g['forms']:f[0]=g['aliases'][0]
  elif kind=='anchored_form_degree':g['forms'][0].extend(c['unit_path'][:2])
  else:g['mode']='quartic_pair'
  try:audit(src,a,c,dg)
  except (ValueError,KeyError,IndexError,TypeError):out.append(kind)
  else:raise ValueError('Anchored mutation survived: '+kind)
 return out

def step_audits(st):
 from check_steps import guard_step,flow_step,anchored_step
 prior=st.get('recontract',st['baseline']);result={'guard':guard_step(*prior,*st['guarded']),'anchored':anchored_step(*st['guarded'],*st['anchored']),'mutations_rejected':[]}
 for kind in ['anchored_record_unit','anchored_record_old_relation','anchored_record_missing','anchored_record_support']:
  a,c=copy.deepcopy(st['anchored']);r=c['anchored_homogenization']['records'][0]
  if kind=='anchored_record_unit':r['new_forms'][1][-1]=-1
  elif kind=='anchored_record_old_relation':r['old_relation']['normalized_variable']=-1
  elif kind=='anchored_record_missing':c['anchored_homogenization']['records'].pop()
  else:r['monomials_after']+=1
  try:anchored_step(*st['guarded'],a,c)
  except (ValueError,KeyError,IndexError,TypeError):result['mutations_rejected'].append(kind)
  else:raise ValueError('Anchored step mutation survived: '+kind)
 for kind in ['guard_record_dummy','guard_record_unit','guard_record_anchor','guard_record_compaction']:
  a,c=copy.deepcopy(st['guarded']);r=c['unit_guard_substitution'];v=r['records_pre_compaction'][0]
  if kind=='guard_record_dummy':v['deleted_dummy']=r['retained_input_indices'][0]
  elif kind=='guard_record_unit':v['unit']=next(i for i in range(len(prior[0]['variables'])) if i not in prior[1]['unit_path'])
  elif kind=='guard_record_anchor':v['anchor']=v['deleted_dummy']
  else:r['retained_input_indices'].reverse()
  try:guard_step(*prior,a,c)
  except (ValueError,KeyError,IndexError,TypeError):result['mutations_rejected'].append(kind)
  else:raise ValueError('Step mutation survived: '+kind)
 if 'flow' in st:
  result['flow']=flow_step(*st['baseline'],*st['flow'])
  if st['flow'][1]['flow_contraction']['records_pre_compaction']:
   for kind in ['flow_record_edge','flow_record_owner','flow_record_compaction']:
    a,c=copy.deepcopy(st['flow']);r=c['flow_contraction'];v=r['records_pre_compaction'][0]
    if kind=='flow_record_edge':v['flow']=0
    elif kind=='flow_record_owner':v['head']=v['tail']
    else:r['retained_input_indices'].reverse()
    try:flow_step(*st['baseline'],a,c)
    except (ValueError,KeyError,IndexError,TypeError):result['mutations_rejected'].append(kind)
    else:raise ValueError('Flow mutation survived: '+kind)
 return result

def single(rebuild=True):
 cfg=read(HERE/'CONFIG.json');sources={};results=[];matched=[];bindings=read(HERE/'SOURCE_BINDINGS.json')
 require({b['local'] for b in bindings}=={p['original'] for p in cfg['sources'].values()},'complete source bindings')
 for b in bindings:require(b['binding']=='byte_identical' and digest(HERE/b['local'])==b['sha256'],'pinned original source bytes')
 for name,p in cfg['sources'].items():
  orig=HERE/p['original'];srcp=HERE/p['refactored']/'source.json';fcp=HERE/p['refactored']/'factor_certificate.json';src,fc=read(srcp),read(fcp)
  check_factor.verify(read(orig),src,fc,digest(orig));sources[name]=(src,digest(srcp))
  if rebuild:
   selected=set(read(HERE/p['selection'])) if p.get('selection') else None;sf,sc=factor_source.factor(read(orig),selected=selected);sc['source_sha256']=digest(orig)
   require(bytesof(sf)==srcp.read_bytes() and bytesof(sc)==fcp.read_bytes(),'deterministic source refactor regeneration')
 summary={r['name']:r for r in read(HERE/'ENDPOINTS.json')}
 for p in cfg['profiles']:
  loc=HERE/'endpoints'/p['name'];a,c=read(loc/'polynomial.json'),read(loc/'certificate.json');src,dg=sources[p['source']];r=audit(src,a,c,dg)
  require(parse_literal((loc/'polynomial.txt').read_text(),len(a['variables']))==a['terms'],'independent literal equation parse');require(read(loc/'metrics.json')==a['metrics'],'metrics file')
  require(summary[p['name']]['source']==p['source'] and all(summary[p['name']][k]==v for k,v in a['metrics'].items()),'endpoint table metrics')
  for filename,h in summary[p['name']]['sha256'].items():require(digest(loc/filename)==h,'endpoint table exact hashes')
  r['mutations_rejected']=mutations(src,a,c,dg)+guarded_mutations(src,a,c,dg)+anchored_mutations(src,a,c,dg);r['name']=p['name'];r['polynomial_sha256']=digest(loc/'polynomial.json');r['certificate_sha256']=digest(loc/'certificate.json')
  if rebuild:
   from pipeline import build
   aa,cc,st=build(src,p['hubs'],p['seed'],dg,p['flow'],p.get('split',False))
   require(bytesof(aa)==(loc/'polynomial.json').read_bytes() and bytesof(cc)==(loc/'certificate.json').read_bytes(),'deterministic polynomial/certificate regeneration');require(literal.render(aa)==(loc/'polynomial.txt').read_text(),'deterministic literal regeneration')
   for sa,sc in st.values():audit(src,sa,sc,dg)
   r['transformation_steps']=step_audits(st)
   from pipeline import clean
   comparison_st=st
   if p.get('split',False):
    oa,oc,comparison_st=build(src,p['hubs'],p['seed'],dg,p['flow'],False)
    for filename,obj in [('polynomial.json',oa),('certificate.json',oc)]:require(hashlib.sha256(bytesof(obj)).hexdigest()==p['cycle_only_sha256'][filename],'exact same-source cycle-only control '+filename)
    require(oa['metrics']==p['cycle_only_metrics'],'exact cycle-only control metrics');audit(src,oa,oc,dg)
    r['normalization_comparison']={'same_original_and_refactored_source':True,'old_normalized_variables':oc['normalization']['original_variables']+len([v for v in oc['normalization']['variables'] if v['kind']!='original']),'new_normalized_variables':len(c['normalization']['variables']),'cycle_only_variables':oa['metrics']['variables'],'cycle_only_monomials':oa['metrics']['monomials'],'split_variables':a['metrics']['variables'],'split_monomials':a['metrics']['monomials'],'exact_cycle_only_control_hashes':'pass','source_pullback_and_monic_coverage':'independently checked for both'}
   ba,bc=clean(*copy.deepcopy(comparison_st['guarded']))
   for filename,obj in [('polynomial.json',ba),('certificate.json',bc)]:require(hashlib.sha256(bytesof(obj)).hexdigest()==p['round20_sha256'][filename],'exact round20 matched baseline '+filename)
   require(ba['metrics']==p['round20_metrics'],'exact round20 baseline metrics')
   matched.append({'baseline':p['name'],'before_variables':ba['metrics']['variables'],'before_monomials':ba['metrics']['monomials'],'after_variables':a['metrics']['variables'],'after_monomials':a['metrics']['monomials'],'historical_baseline_hashes':'pass','same_source_hubs_seed':True,'selected_normalization':'multiplicatively_shared' if p.get('split',False) else 'inherited','selected_anchored_step':r['transformation_steps']['anchored']})
  results.append(r)
 return {'status':'pass','python_optimized':not __debug__,'rebuild':rebuild,'endpoints':results,'matched_source_comparisons':matched}

def main():
 p=argparse.ArgumentParser();p.add_argument('--single',action='store_true');p.add_argument('--skip-rebuild',action='store_true');p.add_argument('--report',type=Path);a=p.parse_args()
 if a.single:result=single(not a.skip_rebuild)
 else:
  results=[]
  for mode in [[],['-O']]:
   cp=subprocess.run([sys.executable,*mode,str(Path(__file__).resolve()),'--single']+(['--skip-rebuild'] if a.skip_rebuild else []),check=True,text=True,capture_output=True);results.append(json.loads(cp.stdout))
  result={'status':'pass','modes':results}
 text=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if a.report:a.report.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
