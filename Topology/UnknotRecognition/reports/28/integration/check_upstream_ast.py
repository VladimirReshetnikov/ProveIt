"""Compare retained fixture algorithms with a user-supplied local fast checkout.
No network, no writes to that checkout. This is an integration check, not an
assertion that the full upstream package has been reproduced here.
"""
import ast, hashlib, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class Strip(ast.NodeTransformer):
    def generic_visit(self,node):
        node=super().generic_visit(node)
        if hasattr(node,'body') and isinstance(node.body,list) and node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):
            node.body=node.body[1:]
        return node

def main():
    if len(sys.argv)!=2: raise SystemExit('usage: check_upstream_ast.py /path/to/fast')
    fast=Path(sys.argv[1]); rows=[]; good=True
    pins={'scan_fast.py':'6c731d0f4d2c2c8bbe513e6b7495cf5dbdc8dc88','planar.py':'1078526e7e7dbaf0b7267728105d870d94136769'}
    for name,pin in pins.items():
        raw=(fast/'fastunknot'/name).read_bytes(); blob=hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()
        source=ast.dump(Strip().visit(ast.parse(raw)),include_attributes=False)
        fixture=ast.dump(Strip().visit(ast.parse((ROOT/'reference_upstream/fastunknot'/name).read_text())),include_attributes=False)
        same=source==fixture; good &= same
        rows.append(dict(file=name,actual_blob=blob,expected_blob=pin,pin_matches=blob==pin,executable_ast_matches=same))
    print(json.dumps(rows,indent=2)); return 0 if good else 1
if __name__=='__main__': sys.exit(main())
