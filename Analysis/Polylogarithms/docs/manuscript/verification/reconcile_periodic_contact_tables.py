"""Compare independent delivered contact tables without regenerating originals."""
from pathlib import Path
import ast,json
import sympy as s
V=Path(__file__).resolve().parent
def expression(text):
    """Read exact pi/zeta/rational arithmetic, with no period independence."""
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value)==int:return s.Integer(node.value)
        if isinstance(node,ast.Name):
            if node.id=='pi':return s.pi
            if node.id.startswith('zeta_') and node.id[5:].isdigit():return s.zeta(int(node.id[5:]))
        if isinstance(node,ast.UnaryOp):
            value=visit(node.operand)
            if isinstance(node.op,ast.USub):return -value
            if isinstance(node.op,ast.UAdd):return value
        if isinstance(node,ast.BinOp):
            left,right=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return left+right
            if isinstance(node.op,ast.Sub):return left-right
            if isinstance(node.op,ast.Mult):return left*right
            if isinstance(node.op,ast.Div):return left/right
            if isinstance(node.op,ast.Pow):return left**right
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='zeta' and len(node.args)==1 and not node.keywords:
            value=visit(node.args[0]);assert value.is_Integer and value>=2
            return s.zeta(value)
        raise ValueError('Not an exact contact coefficient: '+ast.dump(node))
    return visit(ast.parse(text,mode='eval').body)
left=json.loads((V/'twelfth-replay/collisions/data/contact_coefficients.json').read_text())['formulas']
right=json.loads((V/'twelfth-replay/contact/data/contact_coefficients.json').read_text())
key=lambda row:tuple(row[k] for k in ['m','n','p','q'])
l={key(row):expression(row['coefficient']) for row in left}
r={key(row):expression(row['delta']) for row in right}
common=sorted(l.keys()&r.keys());assert len(common)==315
for k in common:assert s.expand(l[k]-r[k])==0,k
assert l[0,0,0,0]==s.pi**2/3
assert s.simplify(l[0,0,0,0]-(r[0,0,0,0]+1))!=0
assert s.simplify(l[0,0,1,0]+r[0,0,1,0])!=0
result=dict(status='PASS',left_table_formulas=len(left),right_table_formulas=len(right),
  common_exact_coefficients=len(common),corruption_controls=2,
  fixed_coordinate_base_contact=str(l[0,0,0,0]),
  scope='Compare 315 overlapping coefficients from two separately replayed original implementations, converting symbolic zeta coordinates to exact SymPy expressions. Reject an additive constant corruption and a derivative-sign corruption. Agreement tests normalization; the all-index law rests on the analytic proof, and no arithmetic independence is inferred.')
(V/'periodic-contact-table-comparison.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(json.dumps(result,indent=2))
