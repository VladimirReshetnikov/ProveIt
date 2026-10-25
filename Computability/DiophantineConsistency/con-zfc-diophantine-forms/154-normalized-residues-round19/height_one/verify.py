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

def audit_polarization(art,cert):
 p=cert['polarization'];n=len(art['variables']);keep=p['retained_input_indices'];initial=p['input_variables'];records=p['records_pre_compaction']
 require(type(initial)==int and keep==sorted(set(keep)) and len(keep)==n and all(type(i)==int and 0<=i<initial for i in keep),'polarization compaction')
 ren={i:j for j,i in enumerate(keep)};gone=set(range(initial))-set(keep);deleted=[];products=set()
 for r in records:
  k=r['normalized_variable'];ids=r['new_factors'];require(len(ids)==2 and len(set(ids))==2 and all(i in ren and art['variables'][ren[i]]=={'kind':'alias','normalized_variable':k} for i in ids),'polarized logical aliases')
  d=r['deleted_dummy'];require(d in gone and d not in deleted,'deleted equality dummy');deleted.append(d)
  require(len(r['products'])==len(r['old_factors']) and r['products'],'polarized product records')
  for j,old in zip(r['products'],r['old_factors']):
   require(j not in products and 0<=j<len(cert['products']),'unique polarized product');products.add(j);q=cert['products'][j]
   require(len(old)==2 and old[0]==old[1] and old[0] in ids,'old logical square')
   require(q['logical_factors']==[k,k] and q['factors']==[ren[i] for i in ids],'new logical polarized factors')
  cy=next(x for x in cert['equality_cycles'] if x['normalized_variable']==k)
  require(cy['aliases']==[ren[i] for i in ids] and cy['mode']=='quartic_pair','polarized equality pair')
 require(set(deleted)==gone and p['removed_dummies']==len(gone),'complete deleted dummy accounting')
 require(art['metrics']['removed_equality_dummies']==len(gone) and art['metrics']['polarized_products']==len(products),'polarization metrics')
 return {'removed_equality_dummies':len(gone),'polarized_products':len(products),'certificate_records':'pass'}

def polar_mutations(art,cert):
 result=[]
 for kind in ['polarized_old_square','polarized_deleted_dummy','polarized_factor_binding','polarized_metric']:
  a,c=copy.deepcopy(art),copy.deepcopy(cert);p=c['polarization'];r=p['records_pre_compaction'][0]
  if kind=='polarized_old_square':r['old_factors'][0][0]=-1
  elif kind=='polarized_deleted_dummy':r['deleted_dummy']=p['retained_input_indices'][0]
  elif kind=='polarized_factor_binding':r['new_factors'].reverse()
  else:a['metrics']['removed_equality_dummies']+=1
  try:audit_polarization(a,c)
  except (ValueError,KeyError,IndexError,TypeError):result.append(kind)
  else:raise ValueError('Polarization mutation survived: '+kind)
 return result

def single(rebuild=True):
 config=read(HERE/'CONFIG.json');sources={};results=[]
 bindings=read(HERE/'SOURCE_BINDINGS.json')
 require({b['local'] for b in bindings}=={p['original'] for p in config['sources'].values()},'complete original source bindings')
 for b in bindings:require(b['binding']=='byte_identical' and digest(HERE/b['local'])==b['sha256'],'pinned original source bytes')
 for name,s in config['sources'].items():
  origpath=HERE/s['original'];srcpath=HERE/s['refactored']/'source.json';certpath=HERE/s['refactored']/'factor_certificate.json'
  orig,src,fc=read(origpath),read(srcpath),read(certpath);proof=check_factor.verify(orig,src,fc,digest(origpath));sources[name]=(src,digest(srcpath))
  if rebuild:
   selected=None if not s.get('selection') else set(read(HERE/s['selection']));sf,sc=factor_source.factor(orig,selected=selected);sc['source_sha256']=digest(origpath);require(bytesof(sf)==srcpath.read_bytes() and bytesof(sc)==certpath.read_bytes(),'affine deterministic regeneration')
 for p in config['profiles']:
  loc=HERE/'endpoints'/p['name'];art,cert=read(loc/'polynomial.json'),read(loc/'certificate.json');src,dg=sources[p['source']];r=audit(src,art,cert,dg);r['polarization']=audit_polarization(art,cert)
  require(parse_literal((loc/'polynomial.txt').read_text(),len(art['variables']))==art['terms'],'independent literal parse')
  require(read(loc/'metrics.json')==art['metrics'],'metrics file')
  r['mutations_rejected']=mutations(src,art,cert,dg)+polar_mutations(art,cert);r['name']=p['name'];r['polynomial_sha256']=digest(loc/'polynomial.json');r['certificate_sha256']=digest(loc/'certificate.json')
  if rebuild:
   from network_compile import run
   a,c=run(src,p['hubs'],p['seed']);c['source_sha256']=dg
   if 'baseline_sha256' in p:
    require(hashlib.sha256(bytesof(a)).hexdigest()==p['baseline_sha256']['polynomial.json'],'exact historical baseline polynomial')
    require(hashlib.sha256(bytesof(c)).hexdigest()==p['baseline_sha256']['certificate.json'],'exact historical baseline certificate')
   from spread import spread
   a,c=spread(a,c)
   require(bytesof(a)==(loc/'polynomial.json').read_bytes(),'polynomial deterministic regeneration');require(bytesof(c)==(loc/'certificate.json').read_bytes(),'certificate deterministic regeneration');require(literal.render(a)==(loc/'polynomial.txt').read_text(),'literal deterministic regeneration')
  results.append(r)
 matched=[]
 if rebuild:
  from network_compile import run
  from spread import spread
  for p in config.get('matched_profiles',[]):
   src,dg=sources[p['source']];base,bc=run(src,p['hubs'],p['seed']);bc['source_sha256']=dg
   require(hashlib.sha256(bytesof(base)).hexdigest()==p['baseline_sha256']['polynomial.json'],'matched exact baseline polynomial')
   require(hashlib.sha256(bytesof(bc)).hexdigest()==p['baseline_sha256']['certificate.json'],'matched exact baseline certificate')
   audit(src,base,bc,dg);a,c=spread(base,bc);audit(src,a,c,dg);audit_polarization(a,c)
   matched.append({'baseline':p['baseline_name'],'before_variables':base['metrics']['variables'],'before_monomials':base['metrics']['monomials'],'after_variables':a['metrics']['variables'],'after_monomials':a['metrics']['monomials'],'same_source_same_graph_parameters':True,'historical_baseline_hashes':'pass'})
 return {'status':'pass','python_optimized':not __debug__,'rebuild':rebuild,'endpoints':results,'matched_source_comparisons':matched}

def main():
 p=argparse.ArgumentParser();p.add_argument('--single',action='store_true');p.add_argument('--skip-rebuild',action='store_true');p.add_argument('--report',type=Path);a=p.parse_args()
 if a.single:result=single(not a.skip_rebuild)
 else:
  results=[]
  for mode in [[],['-O']]:
   cmd=[sys.executable,*mode,str(Path(__file__).resolve()),'--single']+(['--skip-rebuild'] if a.skip_rebuild else []);cp=subprocess.run(cmd,check=True,text=True,capture_output=True);results.append(json.loads(cp.stdout))
  result={'status':'pass','modes':results}
 text=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if a.report:a.report.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
