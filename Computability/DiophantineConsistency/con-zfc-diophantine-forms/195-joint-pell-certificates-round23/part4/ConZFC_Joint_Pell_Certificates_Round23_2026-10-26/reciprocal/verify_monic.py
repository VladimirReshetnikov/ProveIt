#!/usr/bin/env python3
"""Independent finite replay of unit-pivot eliminations and collected SOS arrays.
Imports neither producer nor search. Pure Python standard library; works under -O.
"""
import argparse,hashlib,json,collections,copy
from pathlib import Path

def need(test,msg):
 if not test:raise ValueError(msg)
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def parse(ts,n):
 out={}
 for c,m in ts:
  need(type(c)is int and c!=0,'nonzero integer coefficient');need(m==sorted(m)and all(type(v)is int and 0<=v<n for v in m),'coordinate convention');m=tuple(m);need(m not in out,'duplicate monomial');out[m]=c
 return out
def serial(p):return [[c,list(m)]for m,c in sorted(p.items())if c]
def times(p,q):
 r=collections.defaultdict(int)
 for a,c in p.items():
  for b,d in q.items():r[tuple(sorted(a+b))]+=c*d
 return {m:c for m,c in r.items()if c}
def replace(p,v,f):
 result=collections.defaultdict(int);cache={0:{():1}}
 for mon,c in p.items():
  exp=mon.count(v)
  while exp not in cache:cache[len(cache)]=times(cache[len(cache)-1],f)
  left=tuple(i for i in mon if i!=v)
  for right,d in cache[exp].items():result[tuple(sorted(left+right))]+=c*d
 return {m:c for m,c in result.items()if c}
def replay(source,cert,target):
 n=len(source['variables']);rows={i:parse(r['terms'],n)for i,r in enumerate(source['residuals'])};active=set(range(n));maxdegree=0
 for ordinal,step in enumerate(cert['steps']):
  v,r=step['variable'],step['deleted_row'];need(v in active and r in rows,'live pivot');p=rows[r];c=p.get((v,),0);need(c in(-1,1),'unit coefficient');need(all(v not in m or m==(v,)for m in p),'linear pivot')
  f=parse(step['definition'],n);expected={m:-c*a for m,a in p.items()if m!=(v,)};need(f==expected,'definition identity');need(all(i in active-{v}for m in f for i in m),'definition support')
  need(step['name']==source['variables'][v]['name'],'variable name binding');need(step['row_label']==source['residuals'][r]['label'],'row label binding')
  del rows[r]
  for j in rows:rows[j]=replace(rows[j],v,f)
  active.remove(v);maxdegree=max(maxdegree,max(len(m)for p in rows.values()for m in p))
 keep=sorted(active);need(keep==cert['retained_original_indices'],'retained coordinates');need(sorted(rows)==cert['retained_row_indices'],'retained rows');mp={i:j for j,i in enumerate(keep)}
 need(target['variables']==[source['variables'][i]for i in keep],'variables array');need(len(target['residuals'])==len(rows),'row count')
 for (i,p),r in zip(sorted(rows.items()),target['residuals']):
  expect={tuple(mp[j]for j in m):c for m,c in p.items()};need(r['label']==source['residuals'][i]['label'],'label');need(parse(r['terms'],len(keep))==expect,'literal substituted row')
 return maxdegree

def expand(target):
 n=len(target['variables']);out=collections.defaultdict(int)
 for r in target['residuals']:
  p=parse(r['terms'],n);items=sorted(p.items())
  for i,(m,c)in enumerate(items):
   out[tuple(sorted(m+m))]+=c*c
   for k,d in items[i+1:]:out[tuple(sorted(m+k))]+=2*c*d
 out={m:c for m,c in out.items()if c};used={i for m in out for i in m};need(used==set(range(n)),'all coordinates used')
 return out

def load_expansion(path):
 doc=json.loads(path.read_text())
 if doc.get('schema')!='chunked-sparse-polynomial-v1':
  parse(doc['terms'],doc['variables']);return doc
 terms=[];previous=None
 for item in doc['chunks']:
  rel=Path(item['path']);need(not rel.is_absolute()and '..'not in rel.parts,'safe coefficient chunk path');cp=path.parent/rel;need(hashlib.sha256(cp.read_bytes()).hexdigest()==item['sha256'],'coefficient chunk hash');ch=json.loads(cp.read_text());need(ch['schema']=='sparse-polynomial-chunk-v1','coefficient chunk schema');ts=ch['terms'];need(len(ts)==item['terms'],'coefficient chunk count')
  need(ts and ts[0][1]==item['first_monomial']and ts[-1][1]==item['last_monomial'],'chunk endpoints')
  for coefficient,monomial in ts:
   need(type(coefficient)is int and coefficient!=0 and type(monomial)is list and monomial==sorted(monomial)and all(type(v)is int and 0<=v<doc['variables']for v in monomial),'chunk literal coefficient types and indices');key=tuple(monomial);need(previous is None or previous<key,'strict global monomial order');previous=key
  terms.extend(ts)
 need(len(terms)==doc['total_terms'],'total chunk coefficient count')
 return {'schema':'sparse-polynomial-v1','variables':doc['variables'],'terms':terms}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--profile',type=Path,required=True);ap.add_argument('--write',action='store_true');ap.add_argument('--residual-only',action='store_true');args=ap.parse_args();source=json.loads(args.source.read_text());cert=json.loads((args.profile/'certificate.json').read_text());target=json.loads((args.profile/'equation.json').read_text())
 need(hashlib.sha256(args.source.read_bytes()).hexdigest()==cert['source_sha256'],'source SHA256');maxdegree=replay(source,cert,target);p=expand(target)
 expansion={'schema':'sparse-polynomial-v1','variables':len(target['variables']),'terms':serial(p)};metric={'variables':len(target['variables']),'residuals':len(target['residuals']),'degree':max(map(len,p)),'collected_terms':len(p),'coefficient_height':max(map(abs,p.values())),'residual_terms':sum(len(r['terms'])for r in target['residuals']),'maximum_residual_degree':max(len(m)for r in target['residuals']for c,m in r['terms']),'maximum_intermediate_residual_degree':maxdegree,'deleted_unit_definitions':len(cert['steps']),'all_coordinates_used':True}
 if args.write:
  (args.profile/'expanded_polynomial.json').write_bytes(raw(expansion));(args.profile/'metrics.json').write_bytes(raw(metric))
 else:
  if args.residual_only:need(not (args.profile/'expanded_polynomial.json').exists(),'control explicitly has no delivered collected array')
  else:need(load_expansion(args.profile/'expanded_polynomial.json')==expansion,'every collected coefficient')
  need(json.loads((args.profile/'metrics.json').read_text())==metric,'metrics')
 corrupt=copy.deepcopy(cert);d=corrupt['steps'][0]['definition'];constant=next((i for i,(c,m)in enumerate(d)if not m),None)
 if constant is None:d.append([1,[]])
 else:
  c,m=d[constant];d[constant]=[c+1,m]if c!=-1 else[2,m]
 try:replay(source,corrupt,target)
 except ValueError:rejected=True
 else:rejected=False
 need(rejected,'deliberate certificate corruption rejected')
 print(json.dumps({'status':'PASS','independent_producer_imports':False,'source_sha256':cert['source_sha256'],'profile':str(args.profile),**metric,'corruption_rejected':True},sort_keys=True))
if __name__=='__main__':main()
