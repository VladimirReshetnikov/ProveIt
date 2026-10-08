"""Fetch pinned Git objects and compare source-derived executable ASTs.

Requires network access. This audit was NOT run in the artifact-producing runtime.
No credentials are written; an optional GITHUB_TOKEN is read from the environment.
"""
from pathlib import Path
import ast,base64,difflib,hashlib,json,os,urllib.request

ROOT=Path(__file__).resolve().parents[1]
PINS={
 'scan_fast.py':'6c731d0f4d2c2c8bbe513e6b7495cf5dbdc8dc88',
 'planar.py':'1078526e7e7dbaf0b7267728105d870d94136769',
 'geometry.py':'96acc160dbf2df7981b2db98b602311712a01531',
}
class StripDocs(ast.NodeTransformer):
    def generic_visit(self,node):
        node=super().generic_visit(node)
        if isinstance(node,(ast.Module,ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef)):
            body=node.body
            if body and isinstance(body[0],ast.Expr) and isinstance(body[0].value,ast.Constant) and isinstance(body[0].value.value,str):
                node.body=body[1:]
        return node

def normalized(text,filename):
    tree=StripDocs().visit(ast.parse(text))
    if filename=='geometry.py':
        tree.body=[node for node in tree.body if
                   (isinstance(node,ast.ClassDef) and node.name=='ScanLimit') or
                   (isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='SMOOTHINGS' for t in node.targets))]
    return ast.dump(tree,include_attributes=False,indent=2)

def main():
    failed=False
    for name,pin in PINS.items():
        url=f'https://api.github.com/repos/VladimirReshetnikov/ProveIt/git/blobs/{pin}'
        headers={'Accept':'application/vnd.github+json','User-Agent':'ProveIt-disk-frontier-audit'}
        if os.getenv('GITHUB_TOKEN'):headers['Authorization']='Bearer '+os.environ['GITHUB_TOKEN']
        with urllib.request.urlopen(urllib.request.Request(url,headers=headers),timeout=30) as response:
            payload=json.load(response)
        if payload.get('encoding')!='base64':raise RuntimeError('unexpected Git blob encoding')
        raw=base64.b64decode(payload['content'])
        actual=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if actual!=pin:raise RuntimeError(f'{name}: Git blob hash mismatch')
        upstream=normalized(raw.decode(),name)
        fixture=normalized((ROOT/'reference_upstream'/'fastunknot'/name).read_text(),name)
        if upstream==fixture:print(f'{name}: pinned source and scoped executable AST agree')
        else:
            failed=True
            print(''.join(difflib.unified_diff(upstream.splitlines(True),fixture.splitlines(True),
                                             fromfile=f'upstream/{name}',tofile=f'fixture/{name}')))
    if failed:raise SystemExit('AST differences require review; do not assume source equivalence')

if __name__=='__main__':main()
