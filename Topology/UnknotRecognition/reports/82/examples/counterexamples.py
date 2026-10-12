#!/usr/bin/env python3
"""Reproduce the corner, order, and orientation counterexamples. MIT-0."""
from corner_kernel import Surface, Edge, Gluing, make_kernel, glue, signature
from corner_kernel.bundles import orientation_bundle_summary

def outcome(words, surfaces, pairs):
    return signature(glue(make_kernel(surfaces, words), pairs).kernel)

def separated(word):
    return [e for x in word for e in (Edge(x), Edge())]

def main():
    disk = [Surface(1,1)]
    examples = {
        'adjacent two-port disk -> sphere': outcome([(0,[Edge('a'),Edge('b')])],disk,[Gluing('a','b')]),
        'separated two-port disk -> annulus': outcome([(0,separated('ab'))],disk,[Gluing('a','b')]),
        'separated disk, other sign -> Mobius': outcome([(0,separated('ab'))],disk,[Gluing('a','b',0)]),
        'alternating pairing -> punctured torus': outcome([(0,separated('abcd'))],disk,[Gluing('a','c'),Gluing('b','d')]),
        'nonalternating pairing -> pair of pants': outcome([(0,separated('acbd'))],disk,[Gluing('a','c'),Gluing('b','d')]),
        'annulus loop ports -> torus': outcome([(0,[Edge('a')]),(0,[Edge('b')])],[Surface(0,2)],[Gluing('a','b')]),
        'annulus loop ports -> Klein bottle': outcome([(0,[Edge('a')]),(0,[Edge('b')])],[Surface(0,2)],[Gluing('a','b',0)]),
    }
    for name, value in examples.items():
        print(f'{name}: {value}  (chi, boundary count, orientable)')
    print('Certified orientation bundle over RP2:',
          orientation_bundle_summary(Surface(1,0,False)))

if __name__ == '__main__':
    main()
