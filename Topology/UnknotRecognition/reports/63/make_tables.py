"""Regenerate article tables from the recorded JSON data (no timings rerun)."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
D=ROOT/'data';OUT=ROOT/'docs'/'tables';OUT.mkdir(exist_ok=True)
def read(name):return json.loads((D/name).read_text())
def write(name,headers,rows,align):
    text='\\begin{tabular}{@{}'+align+'@{}}\n\\toprule\n'+' & '.join(headers)+r' \\'+'\n\\midrule\n'
    text+='\n'.join(' & '.join(map(str,row))+r' \\' for row in rows)+'\n\\bottomrule\n\\end{tabular}\n'
    (OUT/name).write_text(text)
a=read('braid_audit.json');b=read('benchmark.json');s=read('sieve_followup.json');t=read('test_summary.json')
labels={'circle':'Zero-crossing circle','two-strand-exhaustive':'Two-strand, exhaustive','three-strand-exhaustive':'Three-strand, exhaustive','seeded-four-five':'Four/five-strand, seeded'}
rows=[]
for k,c in a['cohorts'].items():rows.append([labels[k],c['cases'],c['unknots'],c['positive_probe'],c['positive_beyond_power_only']])
rows.append(['Total',a['cases'],sum(c['unknots'] for c in a['cohorts'].values()),sum(c['positive_probe'] for c in a['cohorts'].values()),sum(c['positive_beyond_power_only'] for c in a['cohorts'].values())])
write('audit.tex',['Source class','Inputs','Unknots','Certified','New$^*$'],rows,'lrrrr')
rows=[]
for z in b['graphs']:
 rows.append([z['kind'].replace('-',' '),z['vertices'],z['nominal_bits'],f"{z['medians']['rational-A']*1000:.3f}",f"{z['medians']['modular-A']*1000:.3f}",f"{z['paired_rational_over_modular']:.3f}"])
write('graph_original.tex',['Family','$r$','$b$','Exact ms','Sieve ms','Paired ratio'],rows,'lrrrrr')
rows=[]
for z in s['cycle_cases']:
 rows.append([z['vertices'],z['nominal_bits'],f"{z['medians']['rational-A']*1000:.3f}",f"{z['medians']['modular-A']*1000:.3f}",f"{z['ratio']:.3f}",f"{z['rational_AA']:.3f}",f"{z['modular_AA']:.3f}"])
write('sieve.tex',['$r$','$b$','Exact ms','Sieve ms','Ratio','Exact A/A','Sieve A/A'],rows,'rrrrrrr')
rows=[]
for z in s['capacity_cases']:rows.append([z['pairs'],z['bits_parameter'],z['coefficient_bits'],z['killed'],f"{z['median']*1000:.3f}"])
write('capacity.tex',['Pairs $k$','$b$','Coefficient bits','Deleted','Median ms'],rows,'rrrrr')
rows=[]
for z in b['braids']:
 rows.append([z['name'].replace('-',' '),len(z['braid']),'yes' if z['unknot'] else 'no',f"{z['medians']['cube-A']*1000:.3f}",f"{z['medians']['probe-A']*1000:.3f}",f"{z['paired_cube_over_probe']:.3f}"])
write('pipeline.tex',['Source','$n$','Unknot','Cube ms','Probe+cube ms','Ratio'],rows,'lrlrrr')
keys=[('graph_oracle_cases','Graph/valuation-oracle cases'),('literal_donor_oracles','Exhaustive short-word donor cases'),('constructed_donor_oracles','Constructed donor cases'),('random_braid_homology_comparisons','Additional random homology comparisons'),('source_convention_comparisons','Independent Artin reconstructions'),('random_minor_blocks','Random minor-gcd blocks'),('binary_unit_pair_checks','Large binary unit-pair checks')]
write('tests.tex',['Check','Count'],[(name,t['counts'][key]) for key,name in keys],'lr')
(OUT/'metrics.tex').write_text('\\newcommand{\\TestCount}{'+str(t['tests'])+'}\n\\newcommand{\\AuditCount}{'+str(a['cases'])+'}\n')
print('Wrote',len(list(OUT.glob('*.tex'))),'tables/metrics')
