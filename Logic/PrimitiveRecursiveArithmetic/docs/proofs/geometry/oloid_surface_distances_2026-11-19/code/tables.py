"""Derive the reader's tables from exact endpoint boxes and the verified CSV."""
from pathlib import Path
from decimal import Decimal as D
import csv
from geometry import POINTS, xyz_box, SCALE

root = Path(__file__).resolve().parents[1]
def latexfrac(x):
    return str(x)
def rounding(v,places):
    return f"{D(v):.{places}f}"
def mathrow(cells):
    return " & ".join(cells) + r" \\" + "\n"

pointrows=[]
for label,(h,s,ey,ez) in POINTS.items():
    coords=[]
    for a,b in xyz_box(label):
        low, high=[rounding(D(k)/SCALE,6) for k in (a,b)]
        assert low==high
        coords.append(low)
    sg=lambda k: '+' if k==1 else '-'
    pointrows.append(mathrow([f'$P_{{{label[1:]}}}$',f'${latexfrac(h)}$',f'${latexfrac(s)}$',
                              f'$({sg(ey)},{sg(ez)})$',*[f'${x}$' for x in coords]]))
(root/'data'/'point_rows.tex').write_text("".join(pointrows))
rows=list(csv.DictReader((root/'data'/'distances.csv').open()))
vals=[]
for a in rows:
    low,high=[rounding(a[k],8) for k in ['lower','upper']]
    assert low==high
    route=a['upper_route']
    vals.append([f"${a['from'][1:]},{a['to'][1:]}$", f"${low}$",
                 r'\textcolor{teal}{'+('---' if route=='direct' else route)+'}'])
(root/'data'/'distance_rows.tex').write_text("".join(
    mathrow(vals[i]+vals[15+i]+vals[30+i]) for i in range(15)))
