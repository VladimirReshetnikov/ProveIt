"""Build a source-linked inventory from the report's actual theorem blocks."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ORDER = ['foundations', 'affine_metric', 'conics', 'coordinates', 'tangency']
TOPIC = {
 'foundations': ['ProveIt iPRA framework'],
 'affine_metric': ['Cartesian coordinate system', 'Euclidean space'],
 'conics': ['Conic section'],
 'coordinates': ['Coordinate system'],
 'tangency': ['Tangent', 'Parametric equation'],
}
OVERRIDES = {
 'geo:line':['Line (geometry)'], 'geo:slope':['Slope','Line (geometry)'],
 'geo:two-lines':['Line (geometry)','Intersection (geometry)'],
 'geo:area':['Cartesian coordinate system'], 'geo:section':['Line (geometry)'],
 'geo:centroid':['Affine coordinates'], 'geo:affine':['Cartesian coordinate system'],
 'geo:lagrange':['Dot product'], 'geo:cauchy':['Dot product'],
 'geo:pythagoras':['Euclidean space','Dot product'], 'geo:metric':['Euclidean space'],
 'geo:cosine':['Angle','Dot product'], 'geo:projection':['Line (geometry)','Dot product'],
 'geo:hyperplane':['Plane (geometry)','Dot product'], 'geo:reflection':['Cartesian coordinate system'],
 'geo:isometries':['Cartesian coordinate system'], 'geo:cross':['Cross product'],
 'geo:plane':['Plane (geometry)'], 'geo:line-plane':['Plane (geometry)','Line (geometry)'],
 'geo:two-planes':['Plane (geometry)'], 'geo:skew':['Line (geometry)','Cross product'],
 'geo:circle':['Circle'], 'geo:line-circle':['Circle','Intersection (geometry)'],
 'geo:circle-circle':['Circle','Intersection (geometry)'], 'geo:circumcenter':['Circle'],
 'geo:orthocenter':['Circle'], 'geo:ninepoint':['Circle'], 'geo:power':['Circle'],
 'geo:shoelace':['Cartesian coordinate system'], 'geo:sphere-plane':['Quadric surface','Plane (geometry)'],
 'con:roots':['Quadratic equation'], 'con:ellipse-foci':['Ellipse'],
 'con:hyperbola-foci':['Hyperbola'], 'con:parabola-foci':['Parabola'],
 'con:directrix':['Conic section','Polar coordinate system'],
 'con:ellipse-reflection':['Ellipse'], 'con:parabola-reflection':['Parabola'],
 'con:asymptotes':['Hyperbola'],
 'con:quadric-reduction':['Quadric surface'], 'con:quadric-types':['Quadric surface'],
 'con:sphere-param':['Quadric surface','Parametric equation'],
 'con:rulings':['Quadric surface'], 'con:ellipsoid-support':['Quadric surface','Dot product'],
 'coord:tail':['Polar coordinate system'], 'coord:addition':['Polar coordinate system','Rotation of axes'],
 'coord:derivatives':['Polar coordinate system','Tangent'], 'coord:polar':['Polar coordinate system'],
 'coord:cylindrical':['Cylindrical coordinate system'], 'coord:spherical':['Spherical coordinate system'],
 'coord:gram-metric':['Cartesian coordinate system','Dot product'],
 'coord:locus-transform':['Analytic geometry','Rotation of axes'],
 'coord:jacobians':['Polar coordinate system','Cylindrical coordinate system','Spherical coordinate system'],
}
REGIMES = {
 'foundations':'Arithmetic foundation; fixed PR-family schemas where stated',
 'affine_metric':'Exact rational inputs; constructed square-root outputs where required; guarded fixed-family extensions',
 'conics':'Rational coefficient decisions; explicit algebraic outputs; guarded fixed-family identities',
 'coordinates':'Fixed PR-family observations; rational branches for inverse coordinates',
 'tangency':'Rational polynomial data; explicit fixed-family quantitative outputs',
}
SUPPLEMENTARY={'geo:orthocenter','geo:ninepoint','tan:implicit','tan:implicit-tangent','tan:arclength'}
pattern=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}\[([^\]]+)\]\s*\\label\{([^}]+)\}')
items=[]
for section in ORDER:
    text=(ROOT/'sections'/f'{section}.tex').read_text()
    for kind,title,label in pattern.findall(text):
        status='Complete human-readable argument; new Lean formalization incomplete/uncompiled'
        domain=REGIMES[section]
        if label=='found:no-zero-test':
            status='External computability obstruction; not claimed as an internal iPRA consistency theorem'
        items.append({'id':label,'kind':kind,'title':title,'section_file':f'sections/{section}.tex',
                      'source_topics':OVERRIDES.get(label,TOPIC[section]),'interpretation':domain,
                      'status':status,'role':'supporting foundation' if section=='foundations' else 'supplementary deduction in linked topic' if label in SUPPLEMENTARY else 'linked-topic result'})
assert len(items)==78
assert len({x['id'] for x in items})==len(items)
data={'total_named_results':len(items),'geometry_analysis_results':sum(not x['id'].startswith('found:') for x in items),
      'foundational_results':sum(x['id'].startswith('found:') for x in items),
      'external_obstruction_results':1,'new_lean_compiled':False,'results':items}
(ROOT/'artifacts'/'theorem_inventory.json').write_text(json.dumps(data,indent=2)+'\n')

def escape(s):
    return s.replace('&',r'\&').replace('_',r'\_').replace('%',r'\%')
rows=[]
for x in items:
    topics='; '.join(x['source_topics'])
    rows.append(r'\ref{'+x['id']+r'} & '+escape(x['title'])+r' & '+escape(topics)+r' \\')
(ROOT/'sections'/'theorem_ledger.tex').write_text(r'''\small
\begin{longtable}{p{.08\linewidth}p{.55\linewidth}p{.28\linewidth}}
\toprule Result & Statement group & Source topic \\ \midrule
\endfirsthead
\toprule Result & Statement group & Source topic \\ \midrule
\endhead
\bottomrule\endfoot
'''+ '\n'.join(rows) + '\n'+r'\end{longtable}\normalsize'+'\n')
print(json.dumps({k:v for k,v in data.items() if k!='results'},indent=2))
