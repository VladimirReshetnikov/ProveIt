#!/usr/bin/env python3
"""Independent exact audit of the batched Pell semantic arithmetic graph.

This module imports neither the builder nor its polynomial implementation.
It expands only local DAG regions, treating explicitly checked interfaces as
independent atoms. The proof of the infinite certificate theorem is separate.
"""
import argparse
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path


class AuditError(Exception):
    pass


def need(condition, message):
    if not condition:
        raise AuditError(message)


class Poly:
    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {(): terms}
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @classmethod
    def atom(cls, label):
        return cls({(label,): 1})

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        other = Poly.coerce(other)
        t = dict(self.terms)
        for m, c in other.terms.items():
            t[m] = t.get(m, 0) + c
        return Poly(t)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly.coerce(other)

    def __rsub__(self, other):
        return Poly.coerce(other) + -self

    def __mul__(self, other):
        other = Poly.coerce(other)
        t = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                mn = tuple(sorted(m + n))
                t[mn] = t.get(mn, 0) + c * d
        need(len(t) < 20000, "unexpected expansion beyond a local interface")
        return Poly(t)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        need(isinstance(exponent, int) and exponent >= 0, "polynomial exponent")
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == Poly.coerce(other).terms


class GraphAudit:
    def __init__(self, data):
        self.data = data
        self.nodes = data["nodes"]
        self.names = data["variable_names"]
        self.signed = set(data["unrestricted_inputs"])
        self.batch = data["batch"]
        self.equalities = data["equalities"]
        self.checks = []
        self.var_nodes = {}
        self.lower = []
        need(data["format"] == "mixed-integer-arithmetic-dag-v1", "graph format")
        for i, node in enumerate(self.nodes):
            op = node[0]
            if op == "v":
                need(len(node) == 2 and 0 <= node[1] < len(self.names), "variable node")
                need(node[1] not in self.var_nodes, "duplicate primitive variable node")
                self.var_nodes[node[1]] = i
                bound = None if node[1] in self.signed else 0
            elif op == "c":
                need(len(node) == 2 and isinstance(node[1], int), "constant node")
                bound = node[1]
            else:
                need(op in ("a", "s", "m") and len(node) == 3, "arithmetic opcode")
                need(all(isinstance(k, int) and 0 <= k < i for k in node[1:]), "DAG topology")
                x, y = node[1:]
                lx, ly = self.lower[x], self.lower[y]
                if op == "a":
                    bound = None if lx is None or ly is None else min(10**9, lx + ly)
                elif op == "m":
                    bound = None if lx is None or ly is None or min(lx, ly) < 0 else min(10**9, lx * ly)
                else:
                    bound = lx - self.nodes[y][1] if lx is not None and self.nodes[y][0] == "c" else None
            self.lower.append(bound)
        need(set(self.var_nodes) == set(range(len(self.names))), "all variables represented")
        self.by_label = {}
        for position, (left, right, label) in enumerate(self.equalities):
            need(0 <= left < len(self.nodes) and 0 <= right < len(self.nodes), "equality root")
            if position >= self.batch["prefix_equalities"]:
                need(label not in self.by_label, "duplicate batch equality label")
                self.by_label[label] = (left, right)

    def atom(self, node_id):
        node = self.nodes[node_id]
        return Poly(node[1]) if node[0] == "c" else Poly.atom("node:" + str(node_id))

    def eval(self, root, boundaries=()):
        stop = set(boundaries)
        cache = {}

        def visit(i):
            if i in cache:
                return cache[i]
            node = self.nodes[i]
            if node[0] == "c":
                result = Poly(node[1])
            elif i in stop:
                result = self.atom(i)
            elif node[0] == "v":
                result = Poly.atom("var:" + str(node[1]))
            else:
                x, y = visit(node[1]), visit(node[2])
                result = x+y if node[0] == "a" else x-y if node[0] == "s" else x*y
            cache[i] = result
            return result

        return visit(root)

    def identity(self, name, root, expected, boundaries=()):
        need(self.eval(root, boundaries) == expected, "identity failed: " + name)
        self.checks.append(name)

    def residual(self, label, expected, boundaries=()):
        need(label in self.by_label, "missing residual: " + label)
        left, right = self.by_label[label]
        actual = self.eval(left, boundaries) - self.eval(right, boundaries)
        need(actual == expected, "residual failed: " + label)
        self.checks.append(label)

    def primitive(self, node_id, signed, description):
        node = self.nodes[node_id]
        need(node[0] == "v", "primitive expected: " + description)
        need((node[1] in self.signed) == signed, "wrong variable domain: " + description)
        return self.atom(node_id)

    def named(self, prefix, signed):
        matches = [i for i, name in enumerate(self.names) if name == prefix or name.startswith(prefix + ".")]
        need(len(matches) == 1, "nonunique named primitive: " + prefix)
        node = self.var_nodes[matches[0]]
        self.primitive(node, signed, prefix)
        return node

    def affine(self, root):
        """Collect linear arithmetic; nonlinear nodes are independent atoms."""
        cache = {}
        def visit(i):
            if i in cache:
                return cache[i]
            op,*args=self.nodes[i]
            if op == "c":
                result=Poly(args[0])
            elif op == "v":
                result=Poly.atom("primitive:"+str(args[0]))
            elif op in ("a","s"):
                x,y=(visit(k) for k in args)
                result=x+y if op == "a" else x-y
            elif self.nodes[args[0]][0] == "c":
                result=self.nodes[args[0]][1]*visit(args[1])
            elif self.nodes[args[1]][0] == "c":
                result=self.nodes[args[1]][1]*visit(args[0])
            else:
                result=Poly.atom("nonlinear:"+str(i))
            cache[i]=result
            return result
        return visit(root)

    def run(self):
        b = self.batch
        powers = b["powers"]
        indices = b["indices"]
        need(bool(powers) and bool(indices), "nonempty power batch")
        pkeys = [(p["base"], p["exponent"], p["output"]) for p in powers]
        calls = [(c["arguments"][0], c["arguments"][1], c["result"]) for c in self.data["call_ledger"] if c["kind"] == "deferred_positive_power"]
        need(Counter(calls) == Counter(pkeys), "power batch exhausts deferred calls")
        need(len(set(pkeys)) == len(pkeys), "duplicate power call")
        tags = {d["tag"]: d for d in indices}
        seeds = [d for d in indices if d.get("certificate", "seed") == "seed"]
        derived = [d for d in indices if d.get("certificate", "seed") == "recurrence"]
        need(len(seeds)+len(derived)==len(indices), "known index certificate type")
        if "seed_indices" in b:
            need(b["seed_indices"] == seeds, "seed metadata agrees with full indices")
        need(len(tags) == len(indices), "unique index tags")
        need({p["index_tag"] for p in powers} == set(tags), "every index used")
        need(len({d["k"] for d in indices}) == len(indices), "exponents deduplicated")
        for p in powers:
            need(tags[p["index_tag"]]["k"] == p["exponent"], "exponent-to-index binding")
            for field in ("base", "exponent", "output"):
                lb = self.lower[p[field]]
                need(lb is not None and lb > 0, "structural positivity: " + p["tag"] + "." + field)
        self.checks.append("all positive-call invariants proved before using any power equality")

        input_nodes = {x for key in pkeys for x in key}
        W,A,Z,P,U,V,v,B = (b[s] for s in ("W","A","Z","P","U","V","v","B"))
        w,a,z,pp,u,vv,vp,bb = (self.atom(i) for i in (W,A,Z,P,U,V,v,B))
        g = b["gap"]
        self.primitive(g, False, "global output gap")
        self.primitive(Z, True, "bootstrap quotient")
        self.primitive(v, True, "common ordinate quotient")
        self.identity("W is sum of all base and exponent ports", W,
                      sum((self.atom(p["base"])+self.atom(p["exponent"]) for p in powers), Poly()), input_nodes)
        self.identity("A is two plus sum outputs plus one gap", A,
                      2+sum((self.atom(p["output"]) for p in powers), Poly())+self.atom(g), input_nodes|{g})
        self.residual("batch.bootstrap_norm", a*a-((w+1)**2-1)*(w*z)**2-1, (W,A,Z))

        all_y = []
        for d in seeds:
            tag = d["tag"]
            x0 = self.named(tag+".X_minus_one", False)
            y0 = self.named(tag+".ordinate_gap", False)
            self.identity(tag+" positive abscissa", d["X"], self.atom(x0)+1, (x0,))
            self.identity(tag+" lower index bound", d["Y"], self.atom(d["k"])+self.atom(y0), (d["k"],y0))
            all_y.append(d["Y"])
        product = Poly(1)
        for y in all_y:
            product *= self.atom(y)
        self.identity("P is product of all seed positive ordinates", P, product, all_y)
        u0 = self.named("batch.U_minus_two", False)
        bp = self.named("batch.base_progression", False)
        self.identity("U lower bound", U, self.atom(u0)+2, (u0,))
        self.identity("V contains four times P squared", V, 4*pp*pp*vp, (P,v))
        self.identity("B progression one modulo four P", B, 1+4*pp*(self.atom(bp)+1), (P,bp))
        self.residual("batch.common_auxiliary_norm", u*u-(a*a-1)*vv*vv-1, (U,A,V))
        qb = self.named("batch.base_congruence.signed_q", True)
        self.residual("batch.base_congruence", bb+u*self.atom(qb)-a, (B,U,A,qb))

        expected_labels = {"batch.bootstrap_norm", "batch.common_auxiliary_norm", "batch.base_congruence"}
        for d in seeds:
            tag = d["tag"]
            X,Y,S,R,k,sq,rq = (d[s] for s in ("X","Y","S","R","k","sq","rq"))
            xx,yy,ss,rr,kk = (self.atom(i) for i in (X,Y,S,R,k))
            self.primitive(sq, True, tag+" signed abscissa progression")
            self.primitive(rq, True, tag+" signed ordinate progression")
            self.identity(tag+" S progression", S, xx+u*self.atom(sq), (X,U,sq))
            self.identity(tag+" R progression", R, kk+4*yy*self.atom(rq), (k,Y,rq))
            self.residual(tag+".main_norm", xx*xx-(a*a-1)*yy*yy-1, (X,Y,A))
            self.residual(tag+".index_norm", ss*ss-(bb*bb-1)*rr*rr-1, (S,R,B))
            expected_labels.update((tag+".main_norm",tag+".index_norm"))

        by_exp={d["k"]:d for d in indices}
        done={d["k"] for d in seeds}
        active=set()
        def verify_derived(d):
            if d["k"] in done:
                return
            need(d["k"] not in active, "acyclic recurrence derivation")
            active.add(d["k"])
            need(d["parent_exponent"] in by_exp, "known parent exponent")
            parent=by_exp[d["parent_exponent"]]
            verify_derived(parent)
            shift=d["shift"]
            need(isinstance(shift,int) and 1<=shift<=16, "bounded positive recurrence shift")
            need(self.affine(d["k"])-self.affine(parent["k"]) == shift, "literal exponent shift identity")
            xp,yp=self.atom(parent["X"]),self.atom(parent["Y"])
            for _ in range(shift):
                xp,yp=a*xp+(a*a-1)*yp,xp+a*yp
            bounds=(A,parent["X"],parent["Y"])
            self.identity(d["tag"]+" derived X recurrence",d["X"],xp,bounds)
            self.identity(d["tag"]+" derived Y recurrence",d["Y"],yp,bounds)
            active.remove(d["k"])
            done.add(d["k"])
        for d in derived:
            verify_derived(d)
        if "recurrence_records" in b:
            expected={(d["k"],d["parent_exponent"],d["shift"]) for d in derived}
            actual={(d["exponent"],d["parent_exponent"],d["shift"]) for d in b["recurrence_records"]}
            need(actual==expected,"recurrence record coverage")

        for p in powers:
            tag = p["tag"]
            d = tags[p["index_tag"]]
            n,m,T,X,Y = p["base"],p["output"],p["modulus"],d["X"],d["Y"]
            nn,mm,tt,xx,yy = (self.atom(i) for i in (n,m,T,X,Y))
            self.identity(tag+" modulus", T, 2*a*nn-nn*nn-1, (A,n))
            quotient = self.named(tag+".residue.signed_q", True)
            self.residual(tag+".residue", xx+yy*nn+tt*self.atom(quotient)-yy*a-mm, (X,Y,n,T,quotient,A,m))
            expected_labels.add(tag+".residue")
        actual_labels = {e[2] for e in self.equalities[b["prefix_equalities"]:]}
        need(actual_labels == expected_labels, "batch equality set is exactly the theorem's residuals")
        return {"status":"PASS", "power_calls":len(powers), "distinct_exponents":len(indices),
                "seed_indices":len(seeds), "derived_indices":len(derived),
                "exact_symbolic_identities":len(self.checks), "checked_identities":self.checks,
                "batch_equalities":len(actual_labels), "variable_domains_checked":True,
                "source_input_positivity":"structural lower bounds without assuming any macro result equality",
                "scope":"Exact local polynomial identities and domain checks for the emitted batch; unbounded semantics are established by BATCHED_PELL_THEOREM.md."}


def audit(data):
    return GraphAudit(data).run()


def pell(base, index):
    x,y=1,0
    for _ in range(index):
        x,y=base*x+(base*base-1)*y,x+base*y
    return x,y


def finite_signed_checks():
    """Finite controls supplement, and do not replace, the signed-index proof."""
    fixtures=[]
    for a,i,n in ((2,2,8),(3,1,1)):
        x,y=pell(a,i)
        u,v=pell(a,n)
        need(v%(y*y)==0,"fixture squared divisibility")
        b=next(a+u*t for t in range(4*y) if (a+u*t)%(4*y)==1)
        if b<2:
            b+=4*y*u
        for es in (-1,1):
            for er in (-1,1):
                found=None
                for h in range(4*n):
                    sh,rh=pell(b,h)
                    S,R=es*sh,er*rh
                    if (S-x)%u or (R-i)%(4*y):
                        continue
                    need(S*S-(b*b-1)*R*R==1,"fixture signed norm")
                    need(b%u==a%u and b%(4*y)==1,"fixture base congruences")
                    found=h
                    break
                need(found is not None,"all four sign combinations represented")
                fixtures.append({"A":a,"true_index":i,"auxiliary_index":n,"Y":y,
                                 "S_sign":es,"R_sign":er,"comparison_index":found})
    residue_cases=0
    for a in range(2,7):
        for n in range(1,9):
            modulus=pell(a,n)[0]
            values=[pell(a,h)[0] for h in range(4*n)]
            for i in range(1,n+1):
                for h,xh in enumerate(values):
                    if (xh-values[i])%modulus==0 or (xh+values[i])%modulus==0:
                        need((h-i)%(2*n)==0 or (h+i)%(2*n)==0,"signed residue implication")
                        residue_cases+=1
    interval_cases=0
    for Y in range(1,33):
        for i in range(1,Y+1):
            for k in range(1,Y+1):
                if (i-k)%(2*Y)==0 or (i+k)%(2*Y)==0:
                    need(i==k,"short-interval sign recovery")
                    interval_cases+=1
    # Without squared divisibility the assertion is false, even with the
    # weaker divisibility Y|V. This control validates the exact hypothesis.
    a,i,n,h,k,b=2,3,6,9,9,39181
    x,y=pell(a,i);u,v=pell(a,n);sb,rb=pell(b,h);S,R=-sb,rb
    need(1<=k<=y and u>=2 and b>=2,"bad fixture bounds")
    need(x*x-(a*a-1)*y*y==u*u-(a*a-1)*v*v==S*S-(b*b-1)*R*R==1,"bad fixture norms")
    need((b-a)%u==0 and (b-1)%(4*y)==0 and (S-x)%u==0 and (R-k)%(4*y)==0,"bad fixture congruences")
    need(v%y==0 and v%(y*y)!=0 and k!=i,"squared divisibility is essential")
    return {"all_four_sign_fixtures":fixtures,"signed_abscissa_residue_cases":residue_cases,
            "short_interval_cases":interval_cases,"squared_divisibility_negative_control":{
                "A":a,"true_index":i,"false_target":k,"auxiliary_index":n,
                "comparison_index":h,"Y":y,"V":v,"B":b,
                "rejected_reason":"Y squared does not divide V"},
            "scope":"Finite implementation controls; universal correctness uses the displayed signed-index proof."}


def negatives(data):
    cases = []
    b = data["batch"]
    for label in ("batch.bootstrap_norm", "batch.common_auxiliary_norm", "batch.base_congruence",
                  b["indices"][0]["tag"]+".main_norm", b["indices"][0]["tag"]+".index_norm",
                  b["powers"][0]["tag"]+".residue"):
        changed=copy.deepcopy(data)
        row=next(e for e in changed["equalities"] if e[2]==label)
        row[1]=next(i for i,n in enumerate(changed["nodes"]) if n==["c",1])
        cases.append(("replace zero by one in "+label,changed))
    for field in ("B","V","W","A","P"):
        changed=copy.deepcopy(data)
        node=changed["batch"][field]
        changed["nodes"][node]=["c",0]
        cases.append(("erase shared "+field,changed))
    for suffix in ("X_minus_one","ordinate_gap"):
        changed=copy.deepcopy(data)
        prefix=changed["batch"]["indices"][0]["tag"]+"."+suffix+"."
        vid=next(i for i,name in enumerate(changed["variable_names"]) if name.startswith(prefix))
        changed["unrestricted_inputs"].append(vid)
        cases.append(("remove necessary "+suffix+" nonnegativity",changed))
    changed=copy.deepcopy(data)
    changed["batch"]["powers"][0]["modulus"]=changed["batch"]["A"]
    cases.append(("replace power modulus by A",changed))
    changed=copy.deepcopy(data)
    changed["batch"]["powers"]=changed["batch"]["powers"][1:]
    cases.append(("drop a deferred power call",changed))
    derived=[d for d in b["indices"] if d.get("certificate") == "recurrence"]
    if derived:
        changed=copy.deepcopy(data)
        changed["nodes"][derived[0]["X"]]=["c",0]
        cases.append(("erase a derived Pell abscissa",changed))
        changed=copy.deepcopy(data)
        next(d for d in changed["batch"]["indices"] if d["tag"]==derived[0]["tag"])["shift"]+=1
        cases.append(("corrupt a derived exponent shift",changed))
    outcomes=[]
    for name,changed in cases:
        try:
            audit(changed)
        except AuditError as error:
            outcomes.append({"mutation":name,"rejected":True,"reason":str(error)})
        else:
            raise AuditError("negative control accepted: "+name)
    return outcomes


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("certificate",type=Path)
    ap.add_argument("--output",type=Path)
    ap.add_argument("--negative-controls",action="store_true")
    args=ap.parse_args()
    raw=args.certificate.read_bytes()
    data=json.loads(raw)
    result=audit(data)
    result["finite_signed_index_checks"]=finite_signed_checks()
    result["certificate_sha256"]=hashlib.sha256(raw).hexdigest()
    if args.negative_controls:
        result["negative_controls"]=negatives(data)
    text=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    print(json.dumps({k:v for k,v in result.items() if k not in ("checked_identities","negative_controls","finite_signed_index_checks")},indent=2))
    if args.negative_controls:
        print("Negative controls rejected:",len(result["negative_controls"]))


if __name__=="__main__":
    main()
