#!/usr/bin/env python3
"""Compile a boundary with 16,385-bit path lengths without expansion. MIT-0."""
from corner_kernel import Surface
from corner_kernel.compiler import Port, compile_boundary
from corner_kernel.oracles import SingletonOracle, BlockOracle

def main():
    p, length = 12, 1 << 16384
    blocks = [(i*(length+1),(i+1)*(length+1)) for i in range(p)]
    residual = BlockOracle(blocks)
    vertex = SingletonOracle(residual.n)
    ports = [Port(f'p{i:02}',0,blocks[(i-1)%p][1]-1,blocks[i][0]) for i in range(p)]
    kernel, evidence = compile_boundary([Surface(1,1)],ports,vertex,residual)
    print('Path length bits:', length.bit_length())
    print('Universe bits:', residual.n.bit_length())
    print('Ports:', len(kernel.ports))
    print('Kernel edges:', sum(len(c.edges) for c in kernel.cycles))
    print('Count calls:', evidence.queries)
    print('Maximum extra singleton pairs:', evidence.maximum_extra_pairings)
    print('Oracle: analytic block partition; this is not a general AHT benchmark.')

if __name__ == '__main__':
    main()
