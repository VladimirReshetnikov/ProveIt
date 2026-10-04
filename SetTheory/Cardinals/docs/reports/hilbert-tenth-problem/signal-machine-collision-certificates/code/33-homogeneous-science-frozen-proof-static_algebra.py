"""Fresh static algebra only: no earlier module, physical simulator, or word replay.

This source is displayed and inspected before execution. SymPy checks symbolic
identities and fixed-dimensional exact LP vertices. Fractions check finite
translation-corner fixtures. The emitted DAGs evaluate integer polynomials;
they are not physical signal-machine schedules.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sympy as sp

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
checks = []

def require(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

def equal(name, left, right):
    if isinstance(left, sp.MatrixBase) or isinstance(right, sp.MatrixBase):
        require(name, all(sp.cancel(v) == 0 for v in (left - right)))
    else:
        require(name, sp.cancel(left - right) == 0)

def T(a, b):
    return sp.Matrix([[1, 0, 0], [a, 1, 0], [b, 0, 1]])

D, t, e = sp.symbols("D t e")
u, tp, h = t/(1-e), t+e*D, e/(2-e)
equal("anchor_scale_restoration", t+h*(t+u), u)
equal("reflector_restoration", u+h*(2*D-tp-u), tp)
equal("internal_endpoint_difference_1", u-t, e*t/(1-e))
equal("internal_endpoint_difference_2", tp-u, e*(D-tp)/(1-e))
equal("target_speed_lower_margin", h+1, 2/(2-e))
equal("target_speed_upper_margin", 1-h, 2*(1-e)/(2-e))
s = sp.symbols("s")
times = [u, s, D, 2*D-s, 2*D-tp, 2*D]
flights = [times[0]] + [times[i]-times[i-1] for i in range(1, 6)]
equal("reflector_flight_vector", sp.Matrix(flights),
      sp.Matrix([u, s-u, D-s, D-s, s-tp, tp]))
equal("reflector_duration", sum(flights), 2*D)
dx, dy, x, y = sp.symbols("dx dy x y")
left_time = 2*(x+x/(1-dx))+2*D
right_time = 2*((D-y)+(D-y)/(1+dy))+2*D
equal("26_event_step_duration", left_time+D+right_time+D,
      6*D+2*(1+1/(1-dx))*x+2*(1+1/(1+dy))*(D-y))
equal("reflected_translation_sign", D-((D-y)-dy*D), y+dy*D)
equal("coordinate_update_step", T(0, dy)*T(dx, 0), T(dx, dy))
a1, a2, b1, b2 = sp.symbols("a1 a2 b1 b2")
equal("translation_addition", T(a1, a2)*T(b1, b2), T(a1+b1, a2+b2))

H = sp.Matrix([[sp.Rational(1,3),1,0],
               [sp.Rational(1,3),-1,1],
               [sp.Rational(1,3),0,-1]])
Hi = sp.Matrix([[1,1,1],[sp.Rational(2,3),sp.Rational(-1,3),sp.Rational(-1,3)],
                [sp.Rational(1,3),sp.Rational(1,3),sp.Rational(-2,3)]])
equal("gap_conjugacy_inverse", H*Hi, sp.eye(3))
equal("gap_coordinate_definition", H*sp.Matrix([D,x-D/3,y-2*D/3]),
      sp.Matrix([x,y-x,D-y]))
S, B = 3*H, 3*Hi
equal("cleared_conjugacy_identity", S*B, 9*sp.eye(3))
equal("cleared_conjugacy_reverse", B*S, 9*sp.eye(3))

nn = sp.symbols("n00 n01 n02 n10 n11 n12 n20 n21 n22")
N = sp.Matrix(3, 3, nn)
p1, p2 = sp.symbols("p1 p2")
ep = sp.Matrix([1,p1,p2])
out = N*ep
scale = out[0]
q1, q2 = out[1]/scale, out[2]/scale
N0 = T(-q1,-q2)*N*T(p1,p2)
equal("normalization_first_column", N0[:,0], sp.Matrix([scale,0,0]))
equal("normalization_top_right", N0[0,1:3], N[0,1:3])
equal("normalization_lower_block", N0[1:3,1:3],
      N[1:3,1:3]-sp.Matrix([q1,q2])*N[0,1:3])
equal("physical_composite_exact_N", T(q1,q2)*N0*T(-p1,-p2), N)
equal("normalization_determinant", sp.det(N0), sp.det(N))
equal("lower_block_determinant", sp.det(N0[1:3,1:3])*scale, sp.det(N))
equal("cleared_conjugacy_determinant", sp.det(S*N*B), 729*sp.det(N))

def gaps(w):
    return (Q(1,3)+w[0], Q(1,3)+w[1]-w[0], Q(1,3)-w[1])

def normalized_shape(g):
    total = sum(g)
    g = [Q(i,total) for i in g]
    return (g[0]-Q(1,3),g[0]+g[1]-Q(2,3))

def translation_fixture(p, q):
    margin = min(gaps(p)+gaps(q))
    delta_total = (q[0]-p[0],q[1]-p[1])
    ratio = 2*max(abs(v) for v in delta_total)/margin
    n = max(1, (ratio.numerator+ratio.denominator-1)//ratio.denominator)
    delta = tuple(v/n for v in delta_total)
    assert max(abs(v) for v in delta) <= margin/2
    assert max(abs(v) for v in delta) <= Q(1,6)
    least_corner = None
    for k in range(n):
        start = tuple(p[j]+k*delta[j] for j in range(2))
        corner = (start[0]+delta[0],start[1])
        end = tuple(start[j]+delta[j] for j in range(2))
        assert min(gaps(start)) >= margin and min(gaps(end)) >= margin
        assert min(gaps(corner)) >= margin/2
        least_corner = min(gaps(corner)) if least_corner is None else min(least_corner,*gaps(corner))
        # These are endpoint identities, not trajectory advancement.
        xx, yy = Q(1,3)+start[0], Q(2,3)+start[1]
        xx1 = xx+delta[0]
        internal_x = xx/(1-delta[0])
        assert min(xx,xx1) <= internal_x <= max(xx,xx1) < yy
        rr = 1-yy
        rr1 = rr-delta[1]
        internal_r = rr/(1+delta[1])
        assert 0 < min(rr,rr1) <= internal_r <= max(rr,rr1) < 1-xx1
    assert tuple(p[j]+n*delta[j] for j in range(2)) == q
    return {"p": list(map(str,p)), "q": list(map(str,q)), "n":n,
            "minimum_endpoint_gap":str(margin),"minimum_corner_gap":str(least_corner),
            "event_count":26*n,"temporary_labels":4*n,"guard_rows":6*n+3}

shapes = [normalized_shape(g) for g in [(1,1,1),(1,2,3),(1,19,1),(19,1,1),(1,1,19),(7,11,13)]]
translation_evidence = []
for i,p in enumerate(shapes):
    for j,q in enumerate(shapes):
        translation_evidence.append(translation_fixture(p,q))
        require(f"translation_margin_fixture_{i}_{j}", True)

def exact_lp(K):
    # Every inequality is row*v >= rhs. No floating-point optimization.
    rows = []
    for i in range(3):
        row = [sp.Integer(int(j == i)) for j in range(3)]+[-1]
        rows.append((row,0))
    rows += [([K[i,j] for j in range(3)]+[-1],0) for i in range(3)]
    rows += [([0,0,0,1],0),([0,0,0,-1],-1)]
    candidates = []
    for active in combinations(range(8),3):
        mat = sp.Matrix([[1,1,1,0]]+[rows[i][0] for i in active])
        if mat.det() == 0:
            continue
        rhs = sp.Matrix([1]+[rows[i][1] for i in active])
        v = mat.inv()*rhs
        if all(sum(row[j]*v[j] for j in range(4)) >= rhs for row,rhs in rows):
            candidates.append(v)
    if not candidates:
        return None
    return max(candidates,key=lambda v:v[3])

positive = sp.Matrix([[1,1,1],[1,2,1],[1,1,3]])
swap = sp.Matrix([[0,1,0],[1,0,0],[0,0,1]])
escape = sp.Matrix([[1,0,0],[0,1,0],[-1,0,1]])
lp_fixtures = [("identity",sp.eye(3),sp.Rational(1,3)),
               ("positive_no_rational_eigenray",positive,sp.Rational(1,3)),
               ("negative_determinant_swap",swap,sp.Rational(1,3)),
               ("invertible_negative_identity",-sp.eye(3),None),
               ("only_boundary_feasible",sp.diag(1,1,-1),0),
               ("singular_positive_matrix",sp.ones(3,3),sp.Rational(1,3)),
               ("compatible_but_no_infinite_positive_orbit",escape,sp.Rational(1,4))]
lp_evidence = []
for name,K,wanted in lp_fixtures:
    v = exact_lp(K)
    require("LP_"+name, (v is None) if wanted is None else (v is not None and v[3] == wanted))
    lp_evidence.append({"name":name,"matrix":[list(map(str,K.row(i))) for i in range(3)],
                        "determinant":str(K.det()),"optimum":None if v is None else str(v[3]),
                        "vertex":None if v is None else list(map(str,v))})

uncovered_N = Hi*positive*H
expected_N = sp.Matrix([[4,-1,-1],[sp.Rational(-1,3),sp.Rational(1,3),sp.Rational(1,3)],
                        [sp.Rational(-1,3),sp.Rational(-1,3),sp.Rational(5,3)]])
equal("previously_uncovered_centered_N",uncovered_N,expected_N)
uncovered_q = (sp.Rational(-1,12),sp.Rational(-1,12))
uncovered_N0 = T(-uncovered_q[0],-uncovered_q[1])*uncovered_N
expected_N0 = sp.Matrix([[4,-1,-1],[0,sp.Rational(1,4),sp.Rational(1,4)],
                         [0,sp.Rational(-5,12),sp.Rational(19,12)]])
equal("previously_uncovered_N0",uncovered_N0,expected_N0)
equal("previously_uncovered_det",uncovered_N.det(),2)
equal("previously_uncovered_lower_det",uncovered_N0[1:3,1:3].det(),sp.Rational(1,2))
lam = sp.symbols("lambda")
equal("previously_uncovered_cubic",positive.charpoly(lam).as_expr(),lam**3-6*lam**2+8*lam-2)
require("previously_uncovered_no_rational_root",all(positive.charpoly(lam).as_expr().subs(lam,r)!=0 for r in [-2,-1,1,2]))
require("previously_uncovered_suffix_one_step",translation_fixture((Q(0),Q(0)),(Q(-1,12),Q(-1,12)))["n"] == 1)
equal("escape_nilpotent_square",(escape-sp.eye(3))**2,sp.zeros(3))

class DAG:
    def __init__(self, positive_inputs=False):
        self.nodes=[]
        self.positive_inputs=positive_inputs
        self.matrix={}
        for i in range(1,4):
            for j in range(1,4):
                name=f"k{i}{j}"
                self.matrix[(i,j)] = self.op("sub",f"a{i}{j}",f"c{i}{j}",name) if positive_inputs else name
    def op(self,op,lhs,rhs,name=None):
        name=name or f"v{len(self.nodes)+1:02d}"
        self.nodes.append({"id":name,"op":op,"left":lhs,"right":rhs})
        return name
    def build(self):
        k=self.matrix
        residuals=[]
        for i in range(1,4):
            terms=[self.op("mul",k[(i,j)],f"g{j}") for j in range(1,4)]
            dot=self.op("add",self.op("add",terms[0],terms[1]),terms[2])
            residuals.append(self.op("sub",dot,f"h{i}"))
        minors=[]
        for j,(a,b,c,d) in enumerate([(2,2,3,3),(2,1,3,3),(2,1,3,2)],start=1):
            # a,c are rows; b,d are columns. The crossed product completes each minor.
            minor=self.op("sub",self.op("mul",k[(a,b)],k[(c,d)]),
                           self.op("mul",k[(a,d)],k[(c,b)]))
            minors.append(self.op("mul",k[(1,j)],minor))
        determinant=self.op("add",self.op("sub",minors[0],minors[1]),minors[2])
        sign=self.op("sub",self.op("mul",2,"b"),3)
        residuals.append(self.op("sub",determinant,self.op("mul",sign,"d")))
        residuals.append(self.op("mul",self.op("sub","b",1),self.op("sub","b",2)))
        squares=[self.op("mul",r,r) for r in residuals]
        out=squares[0]
        for term in squares[1:]:
            out=self.op("add",out,term)
        self.output=out
        return self
    def evaluate(self,values):
        env=dict(values)
        for node in self.nodes:
            l=node["left"] if isinstance(node["left"],int) else env[node["left"]]
            r=node["right"] if isinstance(node["right"],int) else env[node["right"]]
            env[node["id"]] = l*r if node["op"]=="mul" else l+r if node["op"]=="add" else l-r
        return env[self.output]
    def counts(self):
        return dict(Counter(n["op"] for n in self.nodes))
    def serialize(self):
        return {"purpose":"Integer polynomial arithmetic only; not a physical schedule",
                "matrix_input_domain":"eighteen positive integers aij,cij" if self.positive_inputs else "nine signed integers kij",
                "positive_witnesses":["g1","g2","g3","h1","h2","h3","b","d"],
                "constants":[1,2,3],"operations":self.counts(),"total_operations":len(self.nodes),
                "nodes":self.nodes,"output":self.output}

native_dag=DAG().build()
positive_dag=DAG(True).build()
require("native_DAG_exact_gate_count",native_dag.counts()=={"mul":26,"add":11,"sub":11} and len(native_dag.nodes)==48)
require("positive_input_DAG_exact_gate_count",positive_dag.counts()=={"mul":26,"add":11,"sub":20} and len(positive_dag.nodes)==57)

k_symbols=sp.symbols("k11 k12 k13 k21 k22 k23 k31 k32 k33")
Ksymbol=sp.Matrix(3,3,k_symbols)
g_symbols=sp.symbols("g1 g2 g3")
h_symbols=sp.symbols("h1 h2 h3")
bsym,dsym=sp.symbols("b d")
res=[(Ksymbol*sp.Matrix(g_symbols))[i]-h_symbols[i] for i in range(3)]
res += [Ksymbol.det()-(2*bsym-3)*dsym,(bsym-1)*(bsym-2)]
F=sum(r*r for r in res)
symbol_env={str(s):s for s in k_symbols+g_symbols+h_symbols+(bsym,dsym)}
equal("native_DAG_equals_displayed_polynomial",native_dag.evaluate(symbol_env),F)
require("native_polynomial_exact_degree_six",sp.Poly(F,*symbol_env.values()).total_degree()==6)
pos_env={}
substitutions={}
for i in range(1,4):
    for j in range(1,4):
        av,cv=sp.symbols(f"a{i}{j} c{i}{j}")
        pos_env[str(av)]=av
        pos_env[str(cv)]=cv
        substitutions[sp.Symbol(f"k{i}{j}")]=av-cv
pos_env.update({str(s):s for s in g_symbols+h_symbols+(bsym,dsym)})
equal("positive_DAG_explicit_input_substitution",positive_dag.evaluate(pos_env),F.subs(substitutions))
require("positive_input_polynomial_exact_degree_six",sp.Poly(F.subs(substitutions),*pos_env.values()).total_degree()==6)

diophantine_evidence=[]
for name,K in [("identity",sp.eye(3)),("swap",swap),("positive",positive),("escape",escape)]:
    gv=sp.Matrix([1,1,2]) if name=="escape" else sp.ones(3,1)
    hv=K*gv
    det=int(K.det())
    vals={f"k{i+1}{j+1}":int(K[i,j]) for i in range(3) for j in range(3)}
    vals.update({f"g{i+1}":int(gv[i]) for i in range(3)})
    vals.update({f"h{i+1}":int(hv[i]) for i in range(3)})
    vals.update({"b":2 if det>0 else 1,"d":abs(det)})
    require("Diophantine_native_fixture_"+name,native_dag.evaluate(vals)==0)
    positives={key:val for key,val in vals.items() if not key.startswith("k")}
    for i in range(1,4):
        for j in range(1,4):
            v=vals[f"k{i}{j}"]
            positives[f"a{i}{j}"]=max(v,0)+1
            positives[f"c{i}{j}"]=max(-v,0)+1
    require("Diophantine_positive_fixture_"+name,positive_dag.evaluate(positives)==0)
    scaled=dict(vals)
    for key in [f"{letter}{i}" for letter in ["g","h"] for i in range(1,4)]:
        scaled[key]*=7
    require("Diophantine_scaling_fiber_"+name,native_dag.evaluate(scaled)==0)
    diophantine_evidence.append({"name":name,"signed_values":vals,"positive_input_values":positives})

centered_integer=3*uncovered_N
cleared=S*centered_integer*B
equal("centered_fixture_cleared_gap_matrix",cleared,27*positive)
equal("centered_fixture_det_multiplier",cleared.det(),729*centered_integer.det())

source_paths={
    "fixed_center_PROOF.md":"/workspace/shared/projective-signal-shears62-20261004/PROOF.md",
    "fixed_center_REVIEW.md":"/workspace/shared/audit-projective-signal-shears62-20261004/REVIEW.md",
    "invertibility_PROOF.md":"/workspace/shared/fixed-word-invertibility61-20261004/PROOF.md",
    "positive_planar_PROOF.md":"/workspace/shared/projective-signal-shears62-20261004/dependencies/positive_planar_PROOF.md",
}
sources=[]
for copied,original in source_paths.items():
    original_bytes=Path(original).read_bytes()
    copied_bytes=(ROOT/"dependencies"/copied).read_bytes()
    require("dependency_copy_"+copied,original_bytes==copied_bytes)
    sources.append({"original":original,"copy":"dependencies/"+copied,
                    "sha256":hashlib.sha256(original_bytes).hexdigest(),"bytes":len(original_bytes)})

EVIDENCE.mkdir(exist_ok=True)
for name,obj in [("translation_fixtures.json",translation_evidence),
                 ("exact_lp_fixtures.json",lp_evidence),
                 ("diophantine_fixtures.json",diophantine_evidence)]:
    (EVIDENCE/name).write_text(json.dumps(obj,indent=2)+"\n")
(ROOT/"CERTIFICATE_DAG_SIGNED.json").write_text(json.dumps(native_dag.serialize(),indent=2)+"\n")
(ROOT/"CERTIFICATE_DAG_POSITIVE.json").write_text(json.dumps(positive_dag.serialize(),indent=2)+"\n")
report={"result":"PASS","named_check_count":len(checks),"checks":checks,
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sympy_version":sp.__version__,"source_binding":sources,
        "translation_fixture_count":len(translation_evidence),"LP_fixture_count":len(lp_evidence),
        "execution_boundary":"Fresh exact symbolic algebra, rational LP vertex enumeration, endpoint fixtures and integer polynomial DAG evaluation only; no upstream code, collision simulation or saved physical schedule."}
(EVIDENCE/"static_checks.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"result":"PASS","named_check_count":len(checks),
                  "native_DAG_operations":len(native_dag.nodes),
                  "positive_DAG_operations":len(positive_dag.nodes)}))
