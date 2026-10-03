#!/usr/bin/env python3
"""Traverse old/new five-counter startup rows and sum whole-prime CA clocks."""
from pathlib import Path
import json
from clock_verify import ca_clock, grouped, require, PRIMES
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
from verify_pins import verify_inputs
from baseline_support import regenerated_baseline

def compare(baseline):
    verify_inputs()
    results=[]
    for name in ('literal-reversible-source-20261003','reversible-initialization-optimization-20261003'):
        root = baseline if name == 'literal-reversible-source-20261003' else ROOT
        machine=json.loads((root/'reversible5.json').read_text())
        groups=grouped(machine['rows']);q='START';v=[0]*5;theta=steps=0
        while q!='tm_A0_pop0':
            es=[e for e in groups[q] if e['symbol'] not in 'ZP-' or
                (v[e['counter']]==0 if e['symbol']=='Z' else v[e['counter']]>0)]
            require(len(es)==1,('enabled operation',q,v));e=es[0];n=1
            for p,h in zip(PRIMES,v):n*=p**h
            theta+=ca_clock(e['symbol'],PRIMES[e['counter']],n,36684691)
            steps+=1;v[e['counter']]+={'+':1,'-':-1}.get(e['symbol'],0);q=e['target']
            require(steps<1000,'startup step bound')
        results.append(dict(source=name,five_counter_rows_executed=steps,
                            final_counters=v,predicted_CA_microedges=theta,
                            scope='Actual five-counter rows executed; whole-prime formula summed; neither full literal expansion nor CA orbit executed'))
    require(results[0]['predicted_CA_microedges']==126594455831808973674445902,'old empty startup clock')
    require(results[1]['predicted_CA_microedges']==1394018396,'new empty startup clock')
    receipt=dict(status='PASS',cases=results)
    (HERE/'old-new-empty-startup-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
def main():
    with regenerated_baseline() as baseline:
        compare(baseline)

if __name__=='__main__':main()
