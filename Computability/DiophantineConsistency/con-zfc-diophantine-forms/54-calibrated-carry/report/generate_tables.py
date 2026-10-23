from pathlib import Path
import json
R=Path(__file__).resolve().parent;B=R.parent
num=lambda x:f'{x:,}'.replace(',','\\,')
nine=json.loads((B/'nine/METRICS.json').read_text());positive=[r for r in nine if r['domain']=='positive integers'];integer=json.loads((B/'integer/METRICS.json').read_text())
def front(rows,degree):
 return sorted([r for r in rows if not any(s['operations']<=r['operations'] and s[degree]<=r[degree] and (s['operations'],s[degree])!=(r['operations'],r[degree]) for s in rows)],key=lambda r:(r['operations'],r[degree]))
def uniq(rows,degree):
 out=[];seen=set()
 for r in rows:
  key=r['operations'],r[degree]
  if key not in seen:out.append(r);seen.add(key)
 return out
nf=uniq(front(positive,'degree'),'degree');ii=uniq(front(integer,'degree_upper_bound'),'degree_upper_bound')
bal=next(r for r in positive if r['file']=='nine_170_selective12_packed_shifted_quotient2048_positive.json')
(R/'metrics.tex').write_text('\\newcommand{\\NineOps}{'+str(bal['operations'])+'}\n\\newcommand{\\NineDegree}{'+num(bal['degree'])+'}\n')
out=r'''\begin{center}\small
\begin{tabular}{llrr}
\toprule
Domain & Construction & Operations & Exact degree\\\midrule
$\Pos^9$ & Incoming cheapest, previous iteration &548&$15\,502\,748$\\
$\Pos^9$ & Incoming balanced, previous iteration &603&$10\,486\,092$\\
$\Pos^9$ & Incoming lower degree, previous iteration &655&$10\,127\,484$\\
$\Pos^9$ & Incoming Selective Quadratic &738&$7\,344\,328$\\\midrule
'''
for r in nf:
 label='New balanced'if r['file']==bal['file']else 'New '+('packed'if'packed'in r['file']else'regular')+' '+r['majorant'].replace('quotient2048','quotient').replace('support2048','support').replace('simple64','simple')
 out+=f"$\\Pos^9$ & {label} & {r['operations']}&${num(r['degree'])}$\\\\\n"
out+=r'''\midrule
$\Z^{10}$ & Incoming cheapest, previous iteration &582&$50\,822\,936$\\
$\Z^{10}$ & Incoming balanced, previous iteration &637&$34\,378\,296$\\
$\Z^{10}$ & Incoming Selective Quadratic &659&$21\,111\,400$\\\midrule
'''
for r in ii:
 label='New balanced'if r['operations']==554 else'New lower cost'if r['operations']<554 else'New lower degree'
 out+=f"$\\Z^{{10}}$ & {label}&{r['operations']}&${num(r['degree_upper_bound'])}$\\\\\n"
out+=r'''\bottomrule
\end{tabular}
\end{center}
Each displayed new low-variable point is nondominated within its delivered
family. The incoming rows are the actual reviewed eight-archive frontier,
not just a comparison against this report's own older points.
Archive gate counts were independently recounted; inherited exact-degree
claims retain their supplied mathematical proof boundary. The full review
also records the other arrivals and their nonfrontier variants.

One paid operation means one live binary addition, subtraction or
multiplication. Squaring is a multiplication; scalar multiplication is not
free. Constants, input leaves and register reuse are free under this
convention. All variable exponentiation and division are excluded from the
literal evaluation graphs. These are arithmetic-circuit costs, not bit
complexity, coefficient height, or expanded polynomial length.

The new balanced nine-positive equation reduces the best reviewed incoming
nine-positive degree from $7\,344\,328$ to $4\,400\,764$, about $40.1\%$,
and its operation count from 738 to 564, about $23.6\%$.
The new balanced integer equation reduces $21\,111\,400$ to
$14\,699\,152$, about $30.4\%$, while reducing 659 operations to 554,
about $15.9\%$. These are meaningful finite-catalogue improvements, not
claims of a worldwide or global optimum.

The eleven-positive $113/954$ and twelve-positive $108/897$ equations from
the preceding iteration remain useful when trading a few more variables
for low degree. This iteration does not improve those particular families.
For fifteen positive variables, the short frontier below is often simpler
than the low-variable equations if evaluation cost and total degree matter
more than the number of unknowns.
'''
(R/'comparison.tex').write_text(out)
# Literal vectors for three primary position systems, avoiding unreadable single displays.
v=r'''\subsection{Literal positional data}
The ordered positions below use the 31-coordinate order of the quadratic
parent. The complete nine JSON certificates also give every reversed
coefficient and its exponent, so these lists and the source equations
uniquely specify the positional codes.
'''
for stem,title in [('163_selective12_regular','Operation-oriented regular layout'),('170_selective12_packed_shifted','Balanced shared-homogeneous layout'),('170_selective12_packed','Degree-oriented odd-threshold layout')]:
 o=json.loads((B/f'packing/CERTIFICATE_{stem}.json').read_text())
 v+='\\paragraph{'+title+'}\n'
 v+=f"$W={o['maximum_weight']}$, $p={o['padding_exponent']}$, $d={o['Dmax']}$, $K_c={o['Kcode']}$; "
 signs=o['coefficient_signs'];minus=[str(i+1)for i,s in enumerate(signs)if s<0]
 v+=('all row signs are positive.'if not minus else 'negative row signs: '+', '.join(minus)+'.')+'\n'
 for label,vals in [('w',o['weights']),('H',o['target_exponents'])]:
  v+='\\[\\begin{aligned}\n'
  for i in range(0,len(vals),11):
   part=','.join(map(str,vals[i:i+11]));v+=f'({label}_{{{i+1}}},\\ldots,{label}_{{{min(i+11,len(vals))}}})&=({part})'+('\\\\\n'if i+11<len(vals)else'.\n')
  v+='\\end{aligned}\\]\n'
(R/'vectors.tex').write_text(v)
print('nine frontier',[(r['operations'],r['degree'])for r in nf]);print('integer frontier',[(r['operations'],r['degree_upper_bound'])for r in ii])
