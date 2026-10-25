#!/usr/bin/env python3
"""Independent complete forward AND inverse row-basis and expansion checker."""
import copy,hashlib,json
from pathlib import Path
from check import ROOT,read,need,decode,add,mul

def inspect(name,overrides=None):
 p=ROOT/name;cert=read(ROOT/'certificates'/(name+'.json'));out={fn:read(p/(fn+'.json'))for fn in ['equation','expanded_polynomial','METRICS','RESTORATION','row_certificate']}
 if overrides:out.update(overrides)
 need(out['row_certificate']==cert,'frozen row certificate')
 src=ROOT/cert['source']/'equation.json';need(hashlib.sha256(src.read_bytes()).hexdigest()==cert['source_sha256'],'source hash')
 old=read(src);eq=out['equation'];need(eq['domain']=='unrestricted integers' and eq['variables']==old['variables'],'unchanged integer lattice')
 need(len(eq['residuals'])==len(old['residuals']),'row count')
 source=[decode(r['terms'])for r in old['residuals']];rows=copy.deepcopy(source)
 for i,j,k in cert['operations']:
  need(type(i)is int and type(j)is int and type(k)is int and i!=j and k!=0 and 0<=i<len(rows)and 0<=j<len(rows),'invertible elementary operation')
  rows[i]=add(rows[i],{m:k*c for m,c in rows[j].items()})
 need(rows==[decode(r['terms'])for r in eq['residuals']],'all forward rows')
 for i,j,k in reversed(cert['operations']):rows[i]=add(rows[i],{m:-k*c for m,c in rows[j].items()})
 need(rows==source,'all inverse rows')
 need(out['RESTORATION']==read(ROOT/cert['source']/'RESTORATION.json'),'complete affine restoration retained')
 total={};rowh=0
 for r in eq['residuals']:
  row=decode(r['terms']);need(max(map(len,row),default=0)<=2,'quadratic rows');rowh=max(rowh,*map(abs,row.values()));total=add(total,mul(row,row))
 need(decode(out['expanded_polynomial']['terms'])==total,'complete expansion')
 need({v for m in total for v in m}==set(range(len(eq['variables']))),'all coordinates live')
 met={'variables':len(eq['variables']),'rows':len(rows),'degree':max(map(len,total)),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':rowh}
 need(met==out['METRICS'],'all metrics')
 return {'metrics':met,'forward_and_inverse_operations':len(cert['operations'])}
def mutations(name):
 p=ROOT/name;cases=[]
 c=read(p/'row_certificate.json');c['operations'][0][2]+=1;cases.append({'row_certificate':c})
 e=read(p/'equation.json');e['residuals'][0]['terms'][0][0]+=1;cases.append({'equation':e})
 e=read(p/'expanded_polynomial.json');e['terms'][0][0]+=1;cases.append({'expanded_polynomial':e})
 r=read(p/'RESTORATION.json');r['coordinates'][0][0][0]+=1;cases.append({'RESTORATION':r})
 for c in cases:
  try:inspect(name,c)
  except ValueError:pass
  else:raise ValueError('row-basis corruption accepted')
 return len(cases)
if __name__=='__main__':
 result={}
 for c in sorted((ROOT/'certificates').glob('*.json')):result[c.stem]={**inspect(c.stem),'rejected_corruptions':mutations(c.stem)}
 print(json.dumps({'status':'pass','endpoints':result},indent=2,sort_keys=True))
