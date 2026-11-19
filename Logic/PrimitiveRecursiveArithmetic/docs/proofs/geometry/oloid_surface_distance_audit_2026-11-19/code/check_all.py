"""Replay the numerical proof using Python's standard library."""
import csv
import json
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory

from geometry import POINTS, SCALE, xyz_box
from verify_roots import contact_rectangle

code = Path(__file__).resolve().parent
root = code.parent
data = root/'data'

def run(name,*args):
    subprocess.run([sys.executable, str(code/(name+'.py')), *map(str,args)],check=True)

def paper_inputs():
    rows = (data/'point_rows.tex').read_text().splitlines()
    if len(rows)!=len(POINTS):
        raise ValueError('point count')
    for i,(line,(name,(h,s,y,z))) in enumerate(zip(rows,POINTS.items()),1):
        fields = re.findall(r'\$([^$]+)\$',line)
        signs = '('+('+' if y==1 else '-')+','+('+' if z==1 else '-')+')'
        if fields[:4] != [f'P_{{{i}}}',str(h),str(s),signs]:
            raise ValueError('point inputs '+name)
        for (lo,hi),printed in zip(xyz_box(name),fields[4:],strict=True):
            endpoints = [round(Fraction(v*10**6,SCALE)) for v in (lo,hi)]
            if endpoints != [Fraction(printed)*10**6]*2:
                raise ValueError('spatial coordinate '+name)
    seed = json.loads((data/'contacts.json').read_text())
    boxes = {}
    for r in csv.DictReader((data/'distances.csv').open()):
        key = r['from']+'-'+r['to']
        if key in seed:
            b = contact_rectangle(map(Fraction,r['upper_gate_parameters'].split()))
            for t,(lo,hi) in zip(map(Fraction,seed[key]),b,strict=True):
                if min(t-lo,hi-t)<=Fraction(1,10000):
                    raise ValueError('seed clearance')
            boxes[(int(r['from'][1:]),int(r['to'][1:]))] = (r['upper_route'],[int(x*4096) for x,_ in b])
    tab = re.findall(r'\$(\d+),(\d+)\$ & ([ABLR]+) & (\d+(?:, \d+)?)', (root/'roots.tex').read_text())
    quoted = {(int(i),int(j)):(w,[int(n) for n in a.split(', ')]) for i,j,w,a in tab}
    if quoted!=boxes or len(tab)!=20:
        raise ValueError('printed contact isolating intervals')
    print('All ten point definitions, 30 printed spatial coordinates, and 20 root boxes verified.')

def main():
    if not __debug__:
        raise SystemExit('Run Python without -O so all interval assertions are active.')
    paper_inputs()
    for name in ('verify','straight_routes','verify_roots','close_competitor'):
        run(name)
    with TemporaryDirectory() as tmp:
        fresh = Path(tmp)/'refined_distances.csv'
        run('precise_distances','--output',fresh)
        if fresh.read_bytes()!=(data/'refined_distances.csv').read_bytes():
            raise ValueError('refined certificate CSV differs from regeneration')
    run('symbolic')
    run('audit_printed')
    print('All distance checks passed.')

if __name__=='__main__':
    main()
