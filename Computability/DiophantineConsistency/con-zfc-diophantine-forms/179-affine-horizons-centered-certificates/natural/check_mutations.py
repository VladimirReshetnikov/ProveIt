#!/usr/bin/env python3
"""Negative controls for the independently verified natural chart certificate."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy,json,shutil
import check
ROOT=Path(__file__).resolve().parent

def main():
 cert=json.loads((ROOT/'chart202/chart_certificate.json').read_text());trials=[]
 c=copy.deepcopy(cert);c['operations'][0]['addition'][0][0]=-1;trials.append(('negative forward addition',c,None))
 c=copy.deepcopy(cert);v=next(iter(c['inverse_map']));c['inverse_map'][v][0][0]+=1;trials.append(('incorrect inverse map',c,None))
 c=copy.deepcopy(cert);v=next(iter(c['forward_map']));c['forward_map'][v][0][0]+=1;trials.append(('incorrect forward map',c,None))
 c=copy.deepcopy(cert);c['original_defining_rows']=list(reversed(c['original_defining_rows']));trials.append(('reversed restoration dependency',c,None))
 c=copy.deepcopy(cert);c['original_defining_rows'].pop();trials.append(('missing nonnegative gate restoration',c,None))
 trials.append(('incorrect expanded coefficient',copy.deepcopy(cert),'coefficient'))
 rejected=[]
 with TemporaryDirectory(prefix='round22-chart-negative-') as tmp:
  root=Path(tmp);(root/'inherited/pooled202').mkdir(parents=True);(root/'chart202').mkdir()
  shutil.copyfile(ROOT/'inherited/pooled202/equation.json',root/'inherited/pooled202/equation.json');shutil.copyfile(ROOT/'chart202/equation.json',root/'chart202/equation.json')
  for label,c,mode in trials:
   shutil.copyfile(ROOT/'chart202/expanded_polynomial.json',root/'chart202/expanded_polynomial.json')
   if mode:
    p=json.loads((root/'chart202/expanded_polynomial.json').read_text());p['terms'][0][0]+=1;(root/'chart202/expanded_polynomial.json').write_text(json.dumps(p))
   (root/'chart202/chart_certificate.json').write_text(json.dumps(c))
   try:check.verify_chart(root,202)
   except (ValueError,IndexError,KeyError) as e:rejected.append({'mutation':label,'rejection':str(e)})
   else:raise ValueError('accepted corrupted chart: '+label)
 print(json.dumps({'status':'PASS','negative_controls':rejected},indent=2))
if __name__=='__main__':main()
