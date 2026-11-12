"""Reproduce the untrusted arity/uniform-predecessor producer adaptation."""
import ast
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def generated():
    uniform=ast.parse((ROOT/'reference/producer_uniform_original.py').read_text())
    arity=ast.parse((ROOT/'reference/producer_arity_original.py').read_text())
    uc=next(n for n in uniform.body if isinstance(n,ast.ClassDef) and n.name=='Emitter')
    ac=next(n for n in arity.body if isinstance(n,ast.ClassDef) and n.name=='Emitter')
    methods={n.name:n for n in ac.body if isinstance(n,ast.FunctionDef) and n.name in ('term','formula')}
    uc.body=[methods.get(n.name,n) if isinstance(n,ast.FunctionDef) else n for n in uc.body]
    return ast.unparse(uniform).replace('[1, major[1]]','[3, major[1]]')+'\n'

if __name__=='__main__':
    expected=generated()
    if (ROOT/'tests/producer.py').read_text()!=expected:
        raise SystemExit('Producer does not match the documented adaptation.')
    print('Producer adaptation verified.')
