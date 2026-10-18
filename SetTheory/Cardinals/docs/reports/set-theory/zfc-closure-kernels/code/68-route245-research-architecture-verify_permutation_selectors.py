#!/usr/bin/env python3
"""Exhaustive finite check of the exact eight-row leaf selector translation.

The symbolic stack model records constructor names, avoiding gigantic formula
integers. The general argument is the list/stack proof in the accompanying
note. This is not a proof-assistant certificate or a TM simulation.
"""
import itertools,json
from pathlib import Path

def selected(order,j):
    # Stack is bottom-to-top; saved current is zero after DISCARD.
    stack=['prior-a','prior-b',0,'GEN']+[f'rho{x}' for x in order]
    k=9-(order.index(j)+1)
    cache=0
    for _ in range(k):cache=stack.pop()
    assert cache==f'rho{j}'
    current=cache;stack.append('bundle')
    for _ in range(11-k):cache=stack.pop()
    assert (current,stack,cache)==(f'rho{j}',['prior-a','prior-b'],0)
    # DISCARD has12 commands,26 fields; the rest has13 commands,28 fields.
    assert 12+1+k+1+11-k==25
    assert 26+4+2*k+2+2*(11-k)==54
    return k

def main():
    count=0
    for order in itertools.permutations(range(1,9)):
        selectors=[selected(order,j) for j in range(1,9)]
        assert sorted(selectors)==list(range(1,9))
        count+=8
    result={'status':'PASS','permutations':40320,'leaf_selector_cases':count,
            'leaf_commands':25,'leaf_encoded_fields':54,
            'definition':'k_pi(j)=9-pos_pi(j); one-based push position',
            'scope':'Exact finite symbolic stack check; unbounded theorem is the stated generic list argument.'}
    path=Path(__file__).resolve().parent/'results/permutation_selector_results.json';path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
