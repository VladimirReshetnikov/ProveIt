"""Produce standalone bounded variants; generated modules are fully counted."""
from pathlib import Path
import ast

ROOT = Path(__file__).resolve().parent


def build(name):
    source = ROOT / 'code' / (name + '.py')
    tree = ast.parse(source.read_text())
    tick = ast.parse('''
def tick():
    global fuel
    fuel -= 1
    need(fuel >= 0)
''').body[0]
    tree.body.insert(2, tick)
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in ('walk', 'prove'):
            node.body.insert(0, ast.parse('tick()').body[0])
        if (isinstance(node, ast.Assign)
                and isinstance(node.targets[0], ast.Tuple)
                and [n.id for n in node.targets[0].elts] == ['goal', 'proof']):
            node.targets[0].elts.append(ast.Name(id='fuel', ctx=ast.Store()))
            index = tree.body.index(node)
            tree.body.insert(index + 1, ast.parse(
                'need(type(fuel) is int and fuel >= 0)').body[0])
            break
    ast.fix_missing_locations(tree)
    target = source.with_name(name + '_fuel.py')
    target.write_text(ast.unparse(tree) + '\n')
    print(target.relative_to(ROOT))


if __name__ == '__main__':
    build('checker_explicit')
    build('checker_deterministic')
