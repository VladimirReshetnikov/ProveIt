"""Research bridge to preserved report 113; never imported by the recognizer."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'reports/113'))
from projective_ports import Block, Prepared
from projective_ports.source import Source, compile_two_block, extreme_witness
from projective_ports.verify import verify_vector, verify_synchronized
from projective_ports.fixtures import matching, euler
from fastunknot.port_subspace import PortBlock, compress_common_ports


class IntrinsicPrepared:
    def __init__(self, blocks, **kwargs):
        self.original = tuple(blocks)
        self.reduction = compress_common_ports(
            tuple(PortBlock(b.n, b.equations, b.ports, b.conflicts) for b in blocks),
            check=kwargs.get('check', lambda: None))
        self.prepared = Prepared(tuple(Block(b.n, b.equations, b.ports, b.conflicts)
                                       for b in self.reduction.blocks), **kwargs)

    def solve(self, costs, *, master=None, zeros=None, **kwargs):
        master = (0,)*self.original[0].d if master is None else master
        answer = self.prepared.solve(costs, master=self.reduction.reduce_master(master),
                                     zeros=zeros, **kwargs)
        if answer['port'] is not None:
            answer['port'] = self.reduction.lift_port(answer['port'])
        return answer


def encode(value):
    if isinstance(value, Fraction):
        return str(value)
    raise TypeError(type(value).__name__)


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, default=encode)+'\n')


def source_hashes():
    files = [ROOT/'fast/fastunknot/port_subspace.py']
    for folder in ('reports/113/projective_ports', 'reports/113/experiments',
                   'fast/projective_port_research'):
        files.extend(sorted((ROOT/folder).glob('*.py')))
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in files}
