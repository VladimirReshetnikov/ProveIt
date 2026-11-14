#!/usr/bin/env python3
"""Verify all 6! * 2^3 generated AX variants by exact expression arithmetic.

This proves their macro expression contracts by finite symbolic computation.
The propositional exchange theorem relating the swapped heads is separate.
"""
import itertools,json,sys,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
import permute as p
import ax_head_reorder as a

def main():
    result=a.run(a.ops);token={v:k for k,v in a.atom_for.items()}
    d=result['d'];h=result['h'];c=result['a']
    def expression(t):
        if t==1:return ('succ',a.ZERO)
        if isinstance(t,str):return {p.D:d,p.H:h,p.A:c}[t]
        if t[0]=='S':return ('succ',expression(t[1]))
        assert t[0]=='I';return ('im',expression(t[1]),expression(t[2]))
    checked=0;word_hashes=[]
    for mask in range(8):
        heads=p.heads.copy()
        for bit,k in enumerate((2,3,5)):
            if mask>>bit&1:
                t=heads[k];heads[k]=p.I(t[2][1],p.I(t[1],t[2][2]))
        words=[p.compile(t) for t in heads]
        for order in itertools.permutations(range(6)):
            word=p.prefix+sum([words[j] for j in order],[])+p.suffix
            assert len(word)==200 and word[-2:]==['node142','x65']
            operations=[op for name in word[:-2] for op in a.expansion[token[name]]]
            actual=a.run(operations)
            want={**result,'stack':[expression(heads[j]) for j in reversed(order)]+result['stack'][6:]}
            assert actual==want,(mask,order)
            checked+=1;word_hashes.append(hashlib.sha256(json.dumps(word,separators=(',',':')).encode()).hexdigest())
    report=dict(variants=checked,unique_words=len(set(word_hashes)),all_symbolic_macro_contracts_pass=True,
                head_permutations=720,antecedent_choices=8,swappable_heads=[3,4,6],
                unchanged_scalar_registers=True,unchanged_gate_expression=True,unchanged_fields_tail=True,
                unchanged_older_stack_entries=True,
                scope='Finite symbolic arithmetic-expression evaluation. Native proof interderivability of swapped heads, source binding and literal runtime are separate obligations.')
    (HERE.parent/'results/head_variants_symbolic.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
