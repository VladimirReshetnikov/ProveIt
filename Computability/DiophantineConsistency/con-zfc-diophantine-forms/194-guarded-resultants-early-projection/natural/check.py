#!/usr/bin/env python3
"""Independent exact checks using exponent-count monomials, not builder code."""
from pathlib import Path
from copy import deepcopy
import argparse, json
import independent_algebra as A
ROOT=Path(__file__).resolve().parent
read=A.read;need=A.need;sha=A.sha;load=A.load;plus=A.plus;coeff=A.coeff;replace=A.replace;atom=A.atom

def source():return read(ROOT/'inherited/inherited/pooled202/equation.json')
def restoration(original,changed,definitions):
 seen=set();rows=[load(r['terms'])for r in original['residuals']]
 for v,j in definitions:
  need(v in changed and v not in seen,'restoration coverage');r=rows[j];need(r.get(((v,1),))==1,'restoration monic');f=plus(atom(v),coeff(-1,r));need(all(c>0 and all(i!=v for i,k in m)for m,c in f.items()),'original polynomial not nonnegative');deps={i for m in f for i,k in m if i in changed};need(deps<=seen,'restoration cyclic');seen.add(v)
 need(seen==changed,'restoration incomplete')
 return len(seen)
def literal_metrics(e,expanded):
 met,ex=A.metrics(e);need({i for m in ex for i,k in m}==set(range(len(e['variables']))),'unused coordinate');need(met==e['metrics'],'literal metrics');need(ex==load(expanded['terms']),'expanded coefficient mismatch');need(expanded['variables']==len(e['variables']),'expansion arity');need(expanded['domain']==e['domain'],'expansion domain');return met

def verify_chart(e,cert,expanded):
 original=source();need(sha(original)==cert['source_sha256'],'chart source digest');need(sha(e)==cert['target_sha256'],'chart target digest');n=len(original['variables']);F={int(v):load(p)for v,p in cert['forward_map'].items()};G={int(v):load(p)for v,p in cert['inverse_map'].items()};changed=set(F);need(set(G)==changed,'chart map supports');need(set(cert['unchanged_variables'])==set(range(n))-changed,'unchanged coordinates')
 for v in range(n):
  need(replace(F.get(v,atom(v)),G)==atom(v),'F after G');need(replace(G.get(v,atom(v)),F)==atom(v),'G after F')
 rows=[load(r['terms'])for r in original['residuals']];needed={str(v)for v in changed};need(set(cert['forward_positivity'])==needed,'forward positivity coverage')
 for v in changed:
  c=cert['forward_positivity'][str(v)];P=load(c['nonnegative_representative']);need(all(a>0 for a in P.values()),'forward representative not nonnegative');need(P==plus(F[v],*[coeff(-k,rows[j])for j,k in c['source_row_combination']]),'forward representative identity')
 restoration(original,changed,cert['original_defining_rows']);expected=[replace(r,G)for r in rows]
 for i,j,k in cert['row_operations']:
  need(type(k)is int and i!=j and 0<=i<len(rows) and 0<=j<len(rows),'invalid row operation');expected[i]=plus(expected[i],coeff(k,expected[j]))
 need(expected==[load(r['terms'])for r in e['residuals']],'chart literal rows');need(e['domain']==original['domain'] and e['variables']==original['variables'],'chart variable domain');return {'metrics':literal_metrics(e,expanded),'forward_positivity_identities':len(changed),'natural_restoration_gates':len(changed),'both_affine_inverse_identities':True,'all_literal_rows_and_coefficients':True}

def verify_contraction(name,src,e,cert,expanded,chart_changed):
 need(sha(src)==cert['source_sha256'],'contraction source digest');need(sha(e)==cert['target_sha256'],'contraction target digest');rows=[load(r['terms'])for r in src['residuals']];labels=[r['label']for r in src['residuals']];kept=list(range(len(src['variables'])));deleted=[]
 for o in cert['operations']:
  v=o['variable'];j=o['row'];need(v in kept and 0<=j<len(rows),'contraction indices');r=rows[j];a=r.get(((v,1),),0);need(abs(a)==1 and all(all(i!=v for i,k in m)for m in r if m!=((v,1),)),'contraction not monic');f=coeff(-a,plus(r,coeff(-a,atom(v))));need(f==load(o['definition']),'contraction defining polynomial');need(o['label']==labels[j],'contraction row label');rows=[replace(q,{v:f})for k,q in enumerate(rows)if k!=j];labels.pop(j);kept.remove(v);deleted.append(v)
 need(kept==cert['retained_indices'],'contraction renumbering');ren={v:atom(i)for i,v in enumerate(kept)};need([replace(r,ren)for r in rows]==[load(r['terms'])for r in e['residuals']],'contraction target rows');need(labels==[r['label']for r in e['residuals']],'contraction labels');need(e['variables']==[src['variables'][v]for v in kept] and e['domain']==src['domain'],'contraction target domain');changed=set(chart_changed)|set(deleted);ng=restoration(source(),changed,cert['original_defining_rows']);return {'metrics':literal_metrics(e,expanded),'exact_monic_eliminations':len(deleted),'natural_restoration_coordinates':ng,'all_literal_rows_and_coefficients':True}

def main(negative=False):
 e=read(ROOT/'chart202/equation.json');cert=read(ROOT/'chart202/certificate.json');ex=read(ROOT/'chart202/expanded_polynomial.json');out={'chart202':verify_chart(e,cert,ex)};profiles=read(ROOT/'PROFILES.json')
 for name,cfg in profiles.items():
  src=e if cfg['source']=='chart202' else read(ROOT/cfg['source']/'equation.json');sc=cert if cfg['source']=='chart202' else read(ROOT/cfg['source']/'chart_certificate.json');out[name]=verify_contraction(name,src,read(ROOT/name/'equation.json'),read(ROOT/name/'contractions.json'),read(ROOT/name/'expanded_polynomial.json'),[int(v)for v in sc['inverse_map']])
 if negative:
  rejected=[]
  def reject(label,fn):
   try:fn()
   except (ValueError,KeyError,IndexError):rejected.append(label);return
   raise ValueError('negative control accepted: '+label)
  q=deepcopy(cert);v=next(iter(q['forward_positivity']));q['forward_positivity'][v]['nonnegative_representative'][0][0]*=-1;reject('negative forward representative',lambda:verify_chart(e,q,ex))
  q=deepcopy(cert);q['original_defining_rows']=list(reversed(q['original_defining_rows']));reject('reversed gate order',lambda:verify_chart(e,q,ex))
  q=deepcopy(ex);q['terms'][0][0]+=1;reject('corrupted expanded coefficient',lambda:verify_chart(e,cert,q))
  name='natural201';c=read(ROOT/name/'contractions.json');q=deepcopy(c);q['operations'][0]['definition'][0][0]+=1;reject('corrupted eliminated definition',lambda:verify_contraction(name,e,read(ROOT/name/'equation.json'),q,read(ROOT/name/'expanded_polynomial.json'),[int(v)for v in cert['inverse_map']]))
  out['negative_controls_rejected']=rejected
 out['status']='PASS';print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--negative',action='store_true');a=ap.parse_args();main(a.negative)
