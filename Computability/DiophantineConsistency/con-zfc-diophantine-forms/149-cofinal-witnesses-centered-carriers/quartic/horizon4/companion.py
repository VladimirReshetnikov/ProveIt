#!/usr/bin/env python3
"""Optional t>=4 companions. Main recommended endpoints remain t>=16.

The source edit and quartic deltas are independently checked exactly.
The unbounded justification is PROOF.md and the exhaustive t=4,5 certificate.
"""
import argparse,copy,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;sys.path.insert(0,str(ROOT));import build as B

def need(x,m):
 if not x:raise ValueError(m)
def run(output=None):
 source=json.loads((ROOT/'sources/common_remainders250_odd.json').read_text());changed=json.loads((HERE/'source250.json').read_text());wanted=copy.deepcopy(source)
 need(wanted['residuals'][161]['label']=='cofinal.horizon' and wanted['residuals'][161]['terms']==[[-16,[]],[1,[0]],[-1,[219,219]]],'literal cofinal row')
 wanted['residuals'][161]['terms'][0][0]=-4;wanted['variant']+=':horizon4';need(changed==wanted,'only allowed source change')
 results={}
 for name,item in json.loads((ROOT/'ENDPOINTS.json').read_text())['endpoints'].items():
  cert=json.loads((ROOT/item['certificate']).read_text());eq,new,m=B.construct(changed,cert);old=json.loads((ROOT/name/'expanded_polynomial.json').read_text());pold=B.decode(old['terms']);pnew=B.decode(new['terms']);names={v['name']:i for i,v in enumerate(eq['variables'])};t=names['t0'];h=names['cofinal.horizon_root']
  delta={(t,):24,(h,h):-24,():-240};need(B.plus(pold,delta)==pnew,'three coefficient universal delta')
  oldeq=json.loads((ROOT/name/'equation.json').read_text());different=[]
  for i,(r0,r1) in enumerate(zip(oldeq['residuals'],eq['residuals'])):
   if r0!=r1:
    need(B.plus(B.decode(r0['terms']),{():12})==B.decode(r1['terms']),'only horizon residual increases by12');different.append(i)
  need(len(different)==1,'exactly one changed residual')
  total0=sum(abs(c) for c in pold.values());total1=sum(abs(c) for c in pnew.values());need(total0-total1==288,'exact L1 improvement')
  results[name]={k:m[k] for k in ['variables','rows','degree','monomials','height']};results[name].update({'changed_residual':different[0],'coefficient_L1_t16':total0,'coefficient_L1_t4':total1,'exact_quartic_delta':B.encode(delta)})
  if output:
   d=output/name;d.mkdir(parents=True,exist_ok=True)
   for file,obj in [('equation.json',eq),('expanded_polynomial.json',new),('METRICS.json',m)]:B.dump(d/file,obj)
 return {'status':'pass','recommendation':'Optional arithmetic strengthening only; main variable/support/height metrics unchanged.','source_sha256':hashlib.sha256((HERE/'source250.json').read_bytes()).hexdigest(),'universal_delta':'P4-P16=24*t-24*horizon_root^2-240','endpoints':results,'scope':'Exact source and polynomial delta; unbounded t>=4 justification is PROOF.md.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path);p.add_argument('--receipt',type=Path);a=p.parse_args();res=run(a.output);text=json.dumps(res,indent=2)+'\n'
 if a.receipt:a.receipt.write_text(text)
 print(text,end='')
