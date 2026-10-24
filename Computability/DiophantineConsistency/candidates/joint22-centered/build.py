#!/usr/bin/env python3
"""Exact finite certificate for the centered 22-integer, degree14,119-gate form.

Only the Python standard library is used. No Lean command or consistency
search is performed. The universal witness-map proof is in PROOF.md.
"""
import argparse
import ast
from collections import Counter
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.setrecursionlimit(20000)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value,indent=2,sort_keys=True)+"\n").encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Ring:
    def __init__(self, names):
        self.names = list(names)
        self.index = {n:i for i,n in enumerate(names)}
        self.zero = (0,)*len(names)

    def constant(self, c):
        return {self.zero:c} if c else {}

    def symbol(self, name):
        need(name in self.index,"undeclared symbol "+name)
        mon = list(self.zero)
        mon[self.index[name]] = 1
        return {tuple(mon):1}

    def add(self, a, b, sign=1):
        out = dict(a)
        for mon,c in b.items():
            out[mon] = out.get(mon,0)+sign*c
            if not out[mon]:
                del out[mon]
        return out

    def mul(self, a, b):
        out = {}
        for m,c in a.items():
            for n,d in b.items():
                mon = tuple(x+y for x,y in zip(m,n))
                out[mon] = out.get(mon,0)+c*d
        return {m:c for m,c in out.items() if c}

    def power(self, a, n):
        out = self.constant(1)
        while n:
            if n & 1:
                out = self.mul(out,a)
            n //= 2
            if n:
                a = self.mul(a,a)
        return out

    def parse(self, expression):
        def go(n):
            if isinstance(n,ast.Constant) and type(n.value) is int:
                return self.constant(n.value)
            if isinstance(n,ast.Name):
                return self.symbol(n.id)
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
                return {m:-c for m,c in go(n.operand).items()}
            if isinstance(n,ast.BinOp):
                a = go(n.left)
                if isinstance(n.op,ast.Pow):
                    need(isinstance(n.right,ast.Constant) and type(n.right.value) is int
                         and 0 <= n.right.value <= 32,"fixed nonnegative exponent")
                    return self.power(a,n.right.value)
                b = go(n.right)
                if isinstance(n.op,ast.Add):
                    return self.add(a,b)
                if isinstance(n.op,ast.Sub):
                    return self.add(a,b,-1)
                if isinstance(n.op,ast.Mult):
                    return self.mul(a,b)
            raise ValueError("nonpolynomial syntax: "+ast.dump(n))
        return go(ast.parse(expression,mode="eval").body)

    def degree(self, p, witnesses):
        indices = [self.index[n] for n in witnesses]
        return max((sum(mon[i] for i in indices) for mon in p),default=-1)

    def leading(self, p, witnesses, degree):
        indices = [self.index[n] for n in witnesses]
        return {m:c for m,c in p.items() if sum(m[i] for i in indices)==degree}


def symbols(expression):
    return {n.id for n in ast.walk(ast.parse(expression,mode="eval")) if isinstance(n,ast.Name)}


def substitute_y(expression, inverse=False):
    replacement = ast.parse("y-f*o" if inverse else "y+f*o",mode="eval").body
    class Substitute(ast.NodeTransformer):
        def visit_Name(self,n):
            return copy.deepcopy(replacement) if n.id=="y" else n
    return ast.unparse(Substitute().visit(ast.parse(expression,mode="eval")))


def dependencies(source, roots, stops=()):
    needed = set(roots)
    for name,op,x,y in reversed(source):
        if name in needed and name not in stops:
            needed.update((x,y))
    return needed


def evaluate(graph, roots, ring, atoms):
    source = graph["source"]
    needed = dependencies(source,roots,atoms)
    values = dict(atoms)
    for name,op,x,y in source:
        if name not in needed or name in values:
            continue
        def value(a):
            return ring.constant(a) if type(a) is int else values[a]
        a,b = value(x),value(y)
        values[name] = ring.mul(a,b) if op=="*" else ring.add(a,b,-1 if op=="-" else 1)
    return [values[root] for root in roots]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args = parser.parse_args()
    pins = json.loads((ROOT/"provenance/PINS.json").read_text())
    for name,h in pins["files"].items():
        need(sha((ROOT/"provenance"/name).read_bytes())==h,"parent provenance "+name)
    parent = json.loads((ROOT/"provenance/parent.json").read_text())
    old_graph = json.loads((ROOT/"provenance/parent_dag.json").read_text())
    need(parent["variables"]==old_graph["witnesses"],"parent variable agreement")
    need(len(parent["variables"])==22 and len(parent["residuals"])==10,"parent dimensions")
    need([i for i,row in enumerate(parent["residuals"]) if "y" in symbols(row)]==[8],"private auxiliary root")
    names = parent["variables"]+parent["fixed_numerals"]
    need(len(names)==len(set(names)),"distinct witness and fixed symbols")
    need(parent["fixed_numerals"]==old_graph["fixed_numerals"],"parent fixed leaf agreement")
    need(all(symbols(row)<=set(names) for row in parent["residuals"]),"closed parent rows")
    ring = Ring(names)
    old_aux = "(a**2+4*a+3)*(f**2-1)*((f*o-c)**2-y**2)+y**2-1"
    new_aux = "(f*o+y)**2-(a**2+4*a+3)*(f**2-1)*(c+y)*(2*f*o+y-c)-1"
    need(ring.parse(parent["residuals"][8])==ring.parse(old_aux),"literal parent auxiliary binding")
    need(ring.parse(substitute_y(old_aux))==ring.parse(new_aux),"exact centered auxiliary identity")
    need(ring.parse(substitute_y(substitute_y("y"),inverse=True))==ring.parse("y"),"inverse shear left")
    need(ring.parse(substitute_y(substitute_y("y",inverse=True)))==ring.parse("y"),"inverse shear right")
    rows = list(parent["residuals"])
    rows[8] = new_aux
    for i,(old,new) in enumerate(zip(parent["residuals"],rows)):
        need(ring.parse(substitute_y(old))==ring.parse(new),"full forward row map "+str(i))
        need(ring.parse(substitute_y(new,inverse=True))==ring.parse(old),"full inverse row map "+str(i))
    packet = {"name":"joint22_centered_degree14","domain":"unrestricted integers",
        "variables":parent["variables"],"variable_count":22,"residuals":rows,"residual_count":10,
        "single_polynomial":"sum of the squares of the listed residuals","exact_degree":14,
        "fixed_numerals":parent["fixed_numerals"],"coefficient_binding":"coefficients/BINDING.json",
        "witness_map":{"to_parent":"all coordinates unchanged except y_old=y+f*o",
                       "from_parent":"all coordinates unchanged except y=y_old-f*o"},
        "parent_sha256":sha((ROOT/"provenance/parent.json").read_bytes()),
        "exact_leading_form":"4*a**4*f**6*o**2*(c+y)**2",
        "degree_witness":{"monomial":{"a":4,"f":6,"o":2,"y":2},"coefficient":4},
        "proof_boundary":"Ordinary integral shear and exact finite certificates; inherits the parent's native/Pell/refutation calibration. No new Lean or object-ZFC derivation."}
    graph = copy.deepcopy(old_graph)
    old_source = old_graph["source"]
    need([row for row in old_source if row[0]=="fo"]==[["fo","*","f","o"]],"shared fo gate")
    need([row for row in old_source if "y" in row[2:]]==[["y2","*","y","y"]],"single y square gate")
    need("centered_y" not in {row[0] for row in old_source},"fresh node")
    source = []
    for name,op,x,y in old_source:
        if name=="y2":
            source.append(["centered_y","+","fo","y"])
        source.append([name,op,"centered_y" if x=="y" else x,"centered_y" if y=="y" else y])
    graph.update(name=packet["name"],source=source,source_polynomial="equation.json",
        source_sha256=sha(encoded(packet)),exact_degree=14,operations=len(source),
        coefficient_binding="coefficients/BINDING.json")
    graph["named_registers"]["centered_y"]="centered_y"
    known = set(names)
    for name,op,x,y in source:
        need(name not in known and op in {"+","-","*"},"fresh binary operation")
        need(all(type(a) is int or a in known for a in (x,y)),"acyclic references")
        known.add(name)
    live = dependencies(source,[graph["output"]])
    need(all(row[0] in live for row in source) and set(names)<=live,"all inputs and gates live")
    need(len(source)==119,"119 live binary gates")
    graph["operation_breakdown"]=dict(Counter(row[1] for row in source))
    graph["system_operations"]=sum(row[0] in dependencies(source,graph["residuals"]) for row in source)
    atoms = {name:ring.symbol(name) for name in names}
    actual = evaluate(graph,graph["residuals"],ring,atoms)
    expected = [ring.parse(row) for row in rows]
    need(actual==expected,"all ten complete literal residual identities")
    cuts = Ring(graph["residuals"])
    final = evaluate(graph,[graph["output"]],cuts,{n:cuts.symbol(n) for n in graph["residuals"]})[0]
    wanted = {}
    for n in graph["residuals"]:
        wanted = cuts.add(wanted,cuts.power(cuts.symbol(n),2))
    need(final==wanted,"exact universal sum-of-squares finalizer")
    degrees = [ring.degree(p,parent["variables"]) for p in expected]
    need(max(degrees)==7 and degrees[8]==7 and all(d<=6 for i,d in enumerate(degrees) if i!=8),"unique degree-seven residual")
    top = ring.power(ring.leading(expected[8],parent["variables"],7),2)
    need(top==ring.parse(packet["exact_leading_form"]),"complete exact degree-fourteen form")
    witness = [0]*len(names)
    for name,e in packet["degree_witness"]["monomial"].items():
        witness[ring.index[name]]=e
    need(top.get(tuple(witness))==4,"specialization-independent nonzero head")
    binding_bytes = (ROOT/"coefficients/BINDING.json").read_bytes()
    need(sha(binding_bytes)==pins["coefficient_binding_sha256"],"pinned whole coefficient binding")
    binding = json.loads(binding_bytes)
    parent_binding = json.loads((ROOT/"provenance/PARENT_COEFFICIENT_BINDING.json").read_text())
    need(binding["tuple"]==parent_binding["backend"],"unchanged coherent source tuple")
    need(set(binding["payloads"])==set(parent["fixed_numerals"]),"whole six-port tuple")
    for name,item in binding["payloads"].items():
        for key in ("bits","raw_bytes","raw_sha256","gzip_sha256"):
            need(item[key]==parent_binding["payloads"][name][key],"parent coefficient binding "+name+" "+key)
        compressed = (ROOT/"coefficients"/item["file"]).read_bytes()
        need(sha(compressed)==item["gzip_sha256"],"compressed coefficient "+name)
        raw = gzip.decompress(compressed)
        need(sha(raw)==item["raw_sha256"] and len(raw)==item["raw_bytes"],"raw coefficient "+name)
        value = int.from_bytes(raw,"little")
        need(value.bit_length()==item["bits"] and raw[-1]!=0,"minimal coefficient "+name)
        if name=="beta":need(value==2**1064921-1,"authentic beta")
        if name=="cone_A":need(value==2**1113,"authentic A scale")
        if name=="cone_B":need(value==2**666104,"authentic B scale")
    for name,value in [("equation.json",packet),("circuit.json",graph)]:
        if args.check:
            need((ROOT/name).read_bytes()==encoded(value),"deterministic mathematical artifact "+name)
        else:
            (ROOT/name).write_bytes(encoded(value))
    receipt={"status":"PASS","python_optimization":sys.flags.optimize,"variables":22,"domain":"unrestricted integers",
        "residuals":10,"residual_degrees":degrees,"exact_degree":14,"operations":119,
        "operation_breakdown":graph["operation_breakdown"],"system_operations":graph["system_operations"],
        "all_forward_and_inverse_rows_equal":True,"all_literal_DAG_residuals_equal":True,
        "universal_SOS_finalizer_equal":True,"complete_leading_form_equal":True,
        "coefficient_raw_bytes":binding["total_raw_bytes"],
        "all_coefficient_payloads_authenticated":True,
        "equation_sha256":sha(encoded(packet)),"circuit_sha256":sha(encoded(graph)),
        "scope":"Exact finite algebra, complete inverse witness maps, literal circuit and fixed tuple. No Lean or consistency test."}
    (ROOT/("VERIFY.optimized.json" if sys.flags.optimize else "VERIFY.normal.json")).write_bytes(encoded(receipt))
    print(json.dumps(receipt,indent=2))


if __name__=="__main__":
    main()
