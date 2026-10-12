"""Exact component-gauge cut atlases for edge-owned graph grammars.

Standard-library reference implementation. This module does NOT recognize knots.
All graph edges have positive integral capacities. Repeated child references
create fresh graph occurrences; only listed terminal vertices are identified.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations, product
from math import comb
from typing import Any, Iterable

Row = tuple[int, int, tuple[int, ...], int]  # exact cost, parity mask, tags, hidden
SCHEMA = "component-gauge-cut-atlas-v1"

class BudgetExceeded(RuntimeError):
    """Inconclusive query, never evidence that a cut does not exist."""

@dataclass
class Budget:
    limit: int | None = None
    used: int = 0
    def tick(self, amount: int = 1) -> None:
        self.used += amount
        if self.limit is not None and self.used > self.limit:
            raise BudgetExceeded("candidate-work budget exhausted")

class ParityDSU:
    """find(x) returns (representative, x XOR representative)."""
    def __init__(self, n: int):
        self.parent = list(range(n)); self.rank = [0]*n; self.parity = [0]*n
    def find(self, x: int) -> tuple[int, int]:
        # Iterative, so grammar/interface depth does not become Python recursion.
        y, total = x, 0
        while self.parent[y] != y:
            total ^= self.parity[y]; y = self.parent[y]
        root, y, prefix = y, x, 0
        while self.parent[y] != y:
            nxt, edge = self.parent[y], self.parity[y]
            self.parent[y], self.parity[y] = root, total ^ prefix
            prefix ^= edge; y = nxt
        return root, total
    def union(self, a: int, b: int, parity: int = 0) -> bool:
        ra, pa = self.find(a); rb, pb = self.find(b)
        if ra == rb: return (pa ^ pb) == parity
        shift = pa ^ pb ^ parity
        if self.rank[ra] < self.rank[rb]: ra, rb = rb, ra
        self.parent[rb] = ra; self.parity[rb] = shift
        if self.rank[ra] == self.rank[rb]: self.rank[ra] += 1
        return True

def flip(mask: int, bit: int) -> int:
    return ((mask & 1) << 1) | ((mask & 2) >> 1) if bit else mask

def groups(part: Iterable[int]) -> list[list[int]]:
    out: list[list[int]] = []
    for i, c in enumerate(part):
        while len(out) <= c: out.append([])
        out[c].append(i)
    return out

def canonical_partition(keys: Iterable[Any]) -> tuple[int, ...]:
    ids: dict[Any, int] = {}; out = []
    for x in keys:
        if x not in ids: ids[x] = len(ids)
        out.append(ids[x])
    return tuple(out)

def _integer(x: Any, name: str, minimum: int = 0) -> int:
    if type(x) is not int or x < minimum: raise ValueError(f"invalid {name}")
    return x

def validate(grammar: dict[str, Any]) -> None:
    """Validate explicit inventories and acyclic, terminal-only source semantics."""
    if not isinstance(grammar, dict) or set(grammar) != {"k", "nodes"}:
        raise ValueError("grammar fields must be exactly k and nodes")
    _integer(grammar["k"], "threshold")
    nodes = grammar["nodes"]
    if not isinstance(nodes, list) or not nodes: raise ValueError("empty grammar")
    widths: list[int] = []
    for i, node in enumerate(nodes):
        if not isinstance(node, dict): raise ValueError("invalid node")
        op = node.get("op")
        if op == "leaf":
            if set(node) != {"op", "vertices", "edges", "terminals"}:
                raise ValueError("invalid leaf fields")
            vertices = node["vertices"]
            # Actual list, not a binary vertex-count declaration.
            if not isinstance(vertices, list) or any(type(v) is not int or v != j
                                                    for j, v in enumerate(vertices)):
                raise ValueError("vertices must explicitly list 0,...,n-1")
            n = len(vertices)
            terminals = node["terminals"]
            if not isinstance(terminals, list) or any(type(t) is not int or not 0 <= t < n for t in terminals):
                raise ValueError("bad terminal")
            if len(set(terminals)) != len(terminals): raise ValueError("duplicate terminals")
            if not isinstance(node["edges"], list): raise ValueError("bad edge list")
            for e in node["edges"]:
                if not isinstance(e, list) or len(e) != 3: raise ValueError("bad edge")
                u, v, c = e
                if any(type(t) is not int or not 0 <= t < n for t in (u,v)):
                    raise ValueError("bad endpoint")
                _integer(c, "capacity", 1)
            widths.append(len(terminals))
        elif op in ("map", "join"):
            if set(node) != {"op", "children", "maps", "keep"}: raise ValueError("bad rule fields")
            arity = 1 if op == "map" else 2
            ch, maps, keep = node["children"], node["maps"], node["keep"]
            if not isinstance(ch,list) or len(ch) != arity or any(type(j) is not int or not 0 <= j < i for j in ch):
                raise ValueError("children must strictly precede their parent")
            if not isinstance(maps,list) or len(maps) != arity: raise ValueError("invalid quotient maps")
            labels = set()
            for j, mp in zip(ch, maps):
                if not isinstance(mp,list) or len(mp) != widths[j] or any(type(v) is not int or v < 0 for v in mp):
                    raise ValueError("bad terminal map")
                labels.update(mp)
            # Compact explicit namespace; no unlisted quotient vertices.
            if labels != set(range(len(labels))): raise ValueError("quotient labels must be dense")
            if not isinstance(keep,list) or len(set(keep)) != len(keep) or any(type(v) is not int or v not in labels for v in keep):
                raise ValueError("bad retained terminal list")
            widths.append(len(keep))
        else: raise ValueError("unsupported grammar operation")

def leaf_metadata(node: dict[str, Any]) -> dict[str, Any]:
    n = len(node["vertices"]); uf = ParityDSU(n); degrees = [0]*n
    for u,v,_ in node["edges"]:
        uf.union(u,v); degrees[u] += 1; degrees[v] += 1
    keys = [uf.find(v)[0] for v in range(n)]; terminals = node["terminals"]
    visible = {keys[t] for t in terminals}; ts = set(terminals)
    return {"part": canonical_partition(keys[t] for t in terminals),
            "vertices": n, "edges": len(node["edges"]),
            "hidden_components": len(set(keys) - visible),
            "degrees": tuple(min(4,degrees[t]) for t in terminals),
            "private_cubic": all(degrees[v] == 3 for v in range(n) if v not in ts)}

def join_metadata(node: dict[str, Any], children: list[dict[str, Any]]) -> dict[str, Any]:
    maps, keep = node["maps"], node["keep"]
    q = len(set(x for mp in maps for x in mp)); uf = ParityDSU(q); deg = [0]*q
    for m, mp in zip(children,maps):
        for grp in groups(m["part"]):
            for j in grp[1:]: uf.union(mp[grp[0]],mp[j])
        for j,x in enumerate(mp): deg[x] = min(4,deg[x]+m["degrees"][j])
    roots = [uf.find(v)[0] for v in range(q)]; active = {roots[x] for x in keep}; ks = set(keep)
    return {"part": canonical_partition(roots[x] for x in keep),
            "vertices": sum(m["vertices"]-len(mp) for m,mp in zip(children,maps))+q,
            "edges": sum(m["edges"] for m in children),
            "hidden_components": sum(m["hidden_components"] for m in children)+len(set(roots)-active),
            "degrees": tuple(deg[x] for x in keep),
            "private_cubic": all(m["private_cubic"] for m in children) and all(deg[x] == 3 for x in range(q) if x not in ks)}

def _hidden_choices(start: int, masks: Iterable[int]) -> set[int]:
    states = {start}
    for tag in masks:
        states = {h | a for h in states for a in (tag,flip(tag,1))}
    return states

def leaf_atlas(node: dict[str, Any], k: int, budget: Budget) -> dict[Row, dict[str, Any]]:
    """Enumerate forest switches, but NEVER the independent component root bits."""
    n = len(node["vertices"]); edges = node["edges"]; ts = node["terminals"]
    uf = ParityDSU(n); forest = [[] for _ in range(n)]; ft: list[int] = []
    for i,(u,v,_) in enumerate(edges):
        if uf.find(u)[0] != uf.find(v)[0]:
            uf.union(u,v); j=len(ft); ft.append(i); forest[u].append((v,j)); forest[v].append((u,j))
    roots = [uf.find(v)[0] for v in range(n)]; keys = sorted(set(roots))
    visible = []; first = {}
    for t in ts:
        r = roots[t]
        if r not in first: first[r]=t; visible.append(r)
    hidden = [r for r in keys if r not in first]
    # Preorder permits one pass of XOR propagation for every switch set.
    order=[]; seen=set()
    for v in range(n):
        if v in seen: continue
        seen.add(v); stack=[(v,-1,-1)]
        while stack:
            u,pa,edge = stack.pop(); order.append((u,pa,edge))
            for w,j in forest[u]:
                if w not in seen: seen.add(w); stack.append((w,u,j))
    out: dict[Row, dict[str, Any]]={}
    for h in range(min(k,len(ft))+1):
        for switches in combinations(range(len(ft)),h):
            budget.tick(); sw=set(switches); x=[0]*n
            for v,pa,e in order:
                if pa >= 0: x[v]=x[pa] ^ (e in sw)
            cost=0; tags={r:0 for r in keys}; cut=[]
            for i,(u,v,c) in enumerate(edges):
                if x[u] != x[v]: cost += c; cut.append(i)
                else: tags[roots[u]] |= 1 << x[u]
            if cost > k: continue
            p=sum((x[t]^x[first[roots[t]]]) << j for j,t in enumerate(ts))
            mt=tuple(flip(tags[r],x[first[r]]) for r in visible)
            for mask in _hidden_choices(0,(tags[r] for r in hidden)):
                row=(cost,p,mt,mask)
                out.setdefault(row,{"cut_edges":cut})
    return out

def compose_rows(node: dict[str, Any], child_meta: list[dict[str, Any]],
                 rows: tuple[Row, ...]) -> list[Row]:
    """Solve quotient XOR constraints, transport marks, eliminate hidden gauges."""
    maps, keep=node["maps"],node["keep"]
    q=len(set(x for mp in maps for x in mp)); uf=ParityDSU(q)
    for row,meta,mp in zip(rows,child_meta,maps):
        for grp in groups(meta["part"]):
            base=mp[grp[0]]
            for j in grp:
                if not uf.union(base,mp[j],(row[1]>>j)&1): return []
    labels=[uf.find(v) for v in range(q)]
    marks={r:0 for r,_ in labels}; fixed=0
    for row,meta,mp in zip(rows,child_meta,maps):
        fixed |= row[3]
        for i,grp in enumerate(groups(meta["part"])):
            root,bit=labels[mp[grp[0]]]
            marks[root] |= flip(row[2][i],bit)
    first={}; vis=[]; p=0
    for j,v in enumerate(keep):
        root,bit=labels[v]
        if root not in first: first[root]=bit; vis.append(root)
        p |= (bit^first[root]) << j
    mt=tuple(flip(marks[r],first[r]) for r in vis)
    cost=sum(row[0] for row in rows)
    return [(cost,p,mt,h) for h in sorted(_hidden_choices(fixed,(marks[r] for r in marks if r not in first)))]

def encode_row(row: Row) -> list[Any]:
    return [row[0],row[1],list(row[2]),row[3]]

def decode_row(value: Any) -> Row:
    if not isinstance(value,list) or len(value)!=4 or not isinstance(value[2],list): raise ValueError("bad row")
    if any(type(value[j]) is not int for j in (0,1,3)) or any(type(t) is not int for t in value[2]): raise ValueError("noninteger row")
    return value[0],value[1],tuple(value[2]),value[3]

def _json_meta(meta: dict[str,Any]) -> dict[str,Any]:
    return {k:list(v) if isinstance(v,tuple) else v for k,v in meta.items()}

def compile_grammar(grammar: dict[str, Any], *, work_limit: int | None = None) -> dict[str, Any]:
    validate(grammar)
    if work_limit is not None: _integer(work_limit,"work limit")
    k=grammar["k"]; budget=Budget(work_limit); atlases=[]; metadata=[]; stats=[]; entries=[]
    for node in grammar["nodes"]:
        before=budget.used
        if node["op"] == "leaf":
            meta=leaf_metadata(node); atlas=leaf_atlas(node,k,budget)
        else:
            children=node["children"]; cms=[metadata[j] for j in children]
            meta=join_metadata(node,cms); atlas={}
            if len(children)==1:
                for ri,row in enumerate(atlases[children[0]]):
                    budget.tick()
                    for out in compose_rows(node,cms,(row,)):
                        atlas.setdefault(out,{"child_rows":[ri]})
            else:
                left,right=children; buckets: dict[int,list[tuple[int,Row]]]={}
                for ri,row in enumerate(atlases[right]): buckets.setdefault(row[0],[]).append((ri,row))
                for li,a in enumerate(atlases[left]):
                    for bcost in sorted(buckets):
                        if a[0]+bcost > k: break
                        for ri,b in buckets[bcost]:
                            budget.tick()
                            for out in compose_rows(node,cms,(a,b)):
                                atlas.setdefault(out,{"child_rows":[li,ri]})
        sorted_rows=sorted(atlas)
        atlases.append(sorted_rows); metadata.append(meta)
        entries.append({"metadata":_json_meta(meta),"rows":[encode_row(r) for r in sorted_rows],
                        "origins":[atlas[r] for r in sorted_rows]})
        stats.append({"states":len(atlas),"candidate_work":budget.used-before})
    return {"schema":SCHEMA,"grammar":grammar,"atlases":entries,"statistics":stats,
            "candidate_work":budget.used,"query":closed_query(metadata[-1],atlases[-1])}

def closed_query(meta: dict[str,Any], rows: Iterable[Row]) -> dict[str,Any]:
    if meta["part"]: return {"status":"OPEN_INTERFACE"}
    costs=[r[0] for r in rows if r[3]==3]
    return {"status":"MARKED_CUT" if costs else "NO_MARKED_CUT",
            "minimum_cost":min(costs) if costs else None,
            "scope":"abstract graph query only; no knot verdict"}

def query_assignment(meta: dict[str,Any], rows: Iterable[Row], terminal_mask: int) -> dict[int,int]:
    """Exact original marked minimum response at ONE supplied boundary coloring."""
    r=len(meta["part"])
    if type(terminal_mask) is not int or not 0 <= terminal_mask < 1<<r: raise ValueError("invalid coloring")
    grps=groups(meta["part"]); out={}
    for cost,p,tags,hidden in rows:
        flags=hidden; valid=True
        for c,grp in enumerate(grps):
            base=(terminal_mask>>grp[0])&1
            if any((((terminal_mask>>j)&1)^base) != ((p>>j)&1) for j in grp):
                valid=False; break
            flags |= flip(tags[c],base)
        if valid: out[flags]=min(cost,out.get(flags,cost))
    return out

def extract_cut_addresses(packet: dict[str,Any], row_index: int) -> list[dict[str,Any]]:
    """At most k grammar-edge addresses, after independent complete replay.

This exports cut edges, NOT an oriented shore coloring or an embedded noose.
"""
    nodes=packet["grammar"]["nodes"]; tabs=packet["atlases"]; root=len(nodes)-1
    if type(row_index) is not int or not 0 <= row_index < len(tabs[root]["rows"]): raise ValueError("bad row index")
    result=[]; stack=[(root,row_index,())]
    while stack:
        i,ri,path=stack.pop(); row=tabs[i]["rows"][ri]
        if row[0]==0: continue
        node=nodes[i]; origin=tabs[i]["origins"][ri]
        if node["op"]=="leaf":
            for e in origin["cut_edges"]:
                result.append({"path":list(path),"leaf_edge":e,"capacity":node["edges"][e][2]})
        else:
            for branch,(j,c) in reversed(list(enumerate(zip(node["children"],origin["child_rows"])))):
                stack.append((j,c,path+(branch,)))
    return result

def row_bound(k: int, r: int) -> int:
    return 4*(k+1)**2*max(1,8*r)**k

def pair_bound(k: int, width: int) -> int:
    return 16*comb(k+4,4)*max(1,8*width)**k
