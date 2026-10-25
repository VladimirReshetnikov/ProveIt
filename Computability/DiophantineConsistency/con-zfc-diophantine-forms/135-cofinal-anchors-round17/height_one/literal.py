#!/usr/bin/env python3
"""Render every collected coefficient into an ordinary literal equation."""
from collections import Counter
import argparse,json
from pathlib import Path

def render(artifact):
 n=len(artifact['variables']);out=[f'Integer variables x_1 through x_{n}.','The following literal polynomial is equal to zero:']
 for c,m in artifact['terms']:
  if c not in (-1,1): raise ValueError('Expected unit coefficients')
  counts=Counter(m)
  term='*'.join(f'x_{v+1}'+(f'^{e}' if e>1 else '') for v,e in sorted(counts.items())) or '1'
  out.append(('+' if c>0 else '-')+term)
 out.append('=0')
 return '\n'.join(out)+'\n'
def main():
 p=argparse.ArgumentParser();p.add_argument('polynomial',type=Path);p.add_argument('output',type=Path);a=p.parse_args();a.output.write_text(render(json.loads(a.polynomial.read_text())))
if __name__=='__main__':main()
