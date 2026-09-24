#!/usr/bin/env python3
"""Reconstruct the 13 rational templates from their fixed matrix words.

Discovery helper: requires SymPy. The proof verifier reconstructs them
independently, using fractions.Fraction only.
"""
from pathlib import Path
import json
import sympy as s

U=s.Matrix([[1,0,2],[-1,0,2],[0,1,0]])
V=s.Matrix([[0,1,0],[0,-1,0],[1,0,0]])
WORDS=['','0','00','10','110','1100','100','1110',
       '0110','11100','11110','011110','1011110']

def main():
    templates=[]
    for word in WORDS:
        product=s.eye(3)
        for letter in word:
            product=product*(U if letter=='1' else V)
        templates.append(product*U**(-len(word)))
    data=Path(__file__).resolve().parents[1]/'data'
    data.mkdir(exist_ok=True)
    obj={'words':WORDS, 'L':[[[str(x) for x in row] for row in a.tolist()]
                            for a in templates]}
    (data/'template_matrices.json').write_text(json.dumps(obj,indent=2)+'\n')
    print('Reconstructed all 13 rational template matrices.')

if __name__=='__main__':
    main()
