#!/usr/bin/env python3
"""Evaluate a supplied integer tuple, or restore its source coordinates."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent

def value(terms,point):
 total=0
 for coefficient,indices in terms:
  term=coefficient
  for i in indices:term*=point[i]
  total+=term
 return total

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('profile');ap.add_argument('tuple',help='JSON array file, or - for stdin')
 ap.add_argument('--residuals',action='store_true');ap.add_argument('--restore',action='store_true')
 args=ap.parse_args()
 profiles={p['name']:p for p in json.loads((ROOT/'PROFILES.json').read_text())}
 if args.profile not in profiles:raise ValueError('unknown profile')
 profile=profiles[args.profile];eq=json.loads((ROOT/profile['equation']).read_text())
 point=json.loads(sys.stdin.read() if args.tuple=='-' else Path(args.tuple).read_text())
 if not isinstance(point,list) or len(point)!=len(eq['variables']) or any(type(x) is not int for x in point):
  raise ValueError('expected a JSON array of exactly the declared number of integers')
 residuals=[value(r['terms'],point) for r in eq['residuals']]
 answer={'profile':args.profile,'value':sum(v*v for v in residuals)}
 if args.residuals:answer['residuals']=residuals
 if args.restore:
  cp=ROOT/profile['certificate'];cert=json.loads(cp.read_text())
  source=json.loads((cp.parent/cert['source']).read_text())
  lifted=[None]*len(source['variables'])
  for v,x in zip(eq['variables'],point):lifted[v['source_index']]=x
  for step in reversed(cert['steps']):
   lifted[step['variable']]=value(step['restoration'],lifted)
  answer['restored_source_tuple']=lifted
  source_value=sum(value(r['terms'],lifted)**2 for r in source['residuals'])
  if source_value!=answer['value']:raise ValueError('restoration failed value preservation')
  answer['restored_source_value']=source_value
 print(json.dumps(answer))

if __name__=='__main__':main()
