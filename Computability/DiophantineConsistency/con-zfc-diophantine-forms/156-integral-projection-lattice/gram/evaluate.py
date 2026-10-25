#!/usr/bin/env python3
"""Evaluate a supplied integer tuple; this is not a Diophantine solver."""
import argparse,json,pathlib

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--variant',choices=['balanced','lowheight'],default='balanced')
 parser.add_argument('point',type=pathlib.Path,help='JSON array of 240 integers')
 args=parser.parse_args();root=pathlib.Path(__file__).resolve().parent
 equation=json.loads((root/args.variant/'expanded_polynomial.json').read_text())
 point=json.loads(args.point.read_text());n=len(equation['variables'])
 if not isinstance(point,list) or len(point)!=n or any(type(v) is not int for v in point):
  raise ValueError('Expected a JSON array of exactly '+str(n)+' integers')
 result=0
 for coefficient,monomial in equation['terms']:
  term=coefficient
  for index in monomial:term*=point[index]
  result+=term
 print(result)

if __name__=='__main__':main()
