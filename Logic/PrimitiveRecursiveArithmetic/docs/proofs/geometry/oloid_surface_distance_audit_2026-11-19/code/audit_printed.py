"""Check all rounded distances printed in the original TeX table."""
import csv
import re
from fractions import Fraction as Q
from pathlib import Path


def main():
    data = Path(__file__).resolve().parents[1]/'data'
    text = (data/'original_distance_rows.tex').read_text()
    rows = re.findall(r'\$(\d+),(\d+)\$ & \$(\d+\.\d+)\$ & \\textcolor\{teal\}\{([^}]+)\}', text)
    saved = {(i,j):(v,r) for i,j,v,r in rows}
    if len(saved)!=45 or len(rows)!=45:
        raise ValueError('wrong number of printed pairs')
    with (data/'refined_distances.csv').open(newline='') as stream:
        for r in csv.DictReader(stream):
            pair = tuple(r[k][1:] for k in ('from','to'))
            expected,label = saved.pop(pair)
            word = 'direct' if label=='---' else label
            lo,hi = (Q(r[k]) for k in ('lower','upper'))
            rounded = [(x*10**8+Q(1,2)).__floor__() for x in (lo,hi)]
            if not (rounded[0]==rounded[1]==Q(expected)*10**8 and word==r['word']):
                raise ValueError('printed row failed '+str(pair))
    if saved:
        raise ValueError('missing pairs')
    print('All 45 distances and crossing words in the original printed table match.')

if __name__=='__main__':
    main()
