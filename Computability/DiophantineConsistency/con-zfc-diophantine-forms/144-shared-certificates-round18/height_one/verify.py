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

def single(rebuild=True):
 config=read(HERE/'CONFIG.json');sources={};results=[]
 for name,s in config['sources'].items():
  origpath=HERE/s['original'];srcpath=HERE/s['refactored']/'source.json';certpath=HERE/s['refactored']/'factor_certificate.json'
  orig,src,fc=read(origpath),read(srcpath),read(certpath);proof=check_factor.verify(orig,src,fc,digest(origpath));sources[name]=(src,digest(srcpath))
  if rebuild:
   selected=None if not s.get('selection') else set(read(HERE/s['selection']));sf,sc=factor_source.factor(orig,selected=selected);sc['source_sha256']=digest(origpath);require(bytesof(sf)==srcpath.read_bytes() and bytesof(sc)==certpath.read_bytes(),'affine deterministic regeneration')
 for p in config['profiles']:
  loc=HERE/'endpoints'/p['name'];art,cert=read(loc/'polynomial.json'),read(loc/'certificate.json');src,dg=sources[p['source']];r=audit(src,art,cert,dg)
  require(parse_literal((loc/'polynomial.txt').read_text(),len(art['variables']))==art['terms'],'independent literal parse')
  require(read(loc/'metrics.json')==art['metrics'],'metrics file')
  r['mutations_rejected']=mutations(src,art,cert,dg);r['name']=p['name'];r['polynomial_sha256']=digest(loc/'polynomial.json');r['certificate_sha256']=digest(loc/'certificate.json')
  if rebuild:
   from network_compile import run
   a,c=run(src,p['hubs'],p['seed']);c['source_sha256']=dg
   require(bytesof(a)==(loc/'polynomial.json').read_bytes(),'polynomial deterministic regeneration');require(bytesof(c)==(loc/'certificate.json').read_bytes(),'certificate deterministic regeneration');require(literal.render(a)==(loc/'polynomial.txt').read_text(),'literal deterministic regeneration')
  results.append(r)
 from compare_matched import check as check_matched
 matched=check_matched()
 return {'status':'pass','python_optimized':not __debug__,'rebuild':rebuild,'endpoints':results,'matched_comparison':matched}

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
