#!/usr/bin/env python3
"""Exact pool-witness maps, integral on the proved corresponding zero sets."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads((ROOT/p).read_text())
def value(ts,x):
 total=0
 for c,m in ts:
  for i in m:c*=x[i]
  total+=c
 return total

def checked(x,n):
 if type(x)is not list or len(x)!=n or any(type(v)is not int for v in x):raise ValueError('exact integer tuple required')

def project(x):
 cert=read('equations/certificate.json');checked(x,cert['new_variable_original_index']);keep=cert['retained_old_indices'];return[x[i]for i in keep]+[sum(x[g['L']]for g in cert['groups'])]

def lift(x):
 cert=read('equations/certificate.json');keep=cert['retained_old_indices'];checked(x,len(keep)+1);out=[0]*cert['new_variable_original_index'];parent=read('stages/pool_parent.json')
 for i,v in zip(keep,x):out[i]=v
 for g in cert['groups']:
  E,T=value(g['E'],out),value(g['T'],out)
  if T==0 or E%T:raise ValueError('pool restoration is integral only on its proved domain')
  out[g['L']]=E//T
  aggregate=parent['residuals'][g['aggregate_row']]['terms'];M=[[c,m]for c,m in aggregate if g['K']not in m and g['L']not in m]
  out[g['K']]=-value(g['a'],out)*out[g['L']]-value(M,out)
 if sum(out[g['L']]for g in cert['groups'])!=x[-1]:raise ValueError('point fails reciprocal quotient identity')
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('direction',choices=['project','lift']);ap.add_argument('point',type=Path);args=ap.parse_args();point=json.loads(args.point.read_text());print(json.dumps((project if args.direction=='project'else lift)(point)))
if __name__=='__main__':main()
