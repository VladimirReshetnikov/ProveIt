# Independent review: forced-w natural 79-operation graph

The [candidate](../../research/ordinary14-natural-forced-w79/README.md) has the stated external zero-existence equivalence to the 80-operation parent under `beta>0` and `K0>=0`, with arbitrary integer MC and MF, conditional on the reviewed parent factor and endpoint results. Its graph has 14 natural inputs and 79 live binary operations; exact specialized degree 107 follows from the inherited parent upper bound and the independently checked ray. This is an upper bound on an explicit graph, not a minimality claim or a Lean/iPRA theorem.

The checker compares every surviving graph row to the pinned parent after deleting `w=n_w+1` and substituting `n_w` at each use; this establishes the affine polynomial identity by structural congruence. It checks the exact graph shapes used below, all inputs/ports/gates are live, and exhausts the modulo-four exclusions for the other three restricted factors. It independently rehashes the P72 raw and gzip payloads against the P72/P115 binding records and obtains the degree-107 ray coefficient `419359493` using finite differences modulo 1,000,000,007. The matching degree upper bound is inherited from the reviewed parent, not independently rederived here.

For the unbounded zero map, suppose a candidate zero has `w=0`. The graph gives `X=ell=0`, making the first factor `r²`. Since the five integer factors multiply to 1, `r²=1`; the three reviewed residue exclusions make the remaining restricted factors `+1`, hence the guard is `+1`. If `J=0`, the graph gives `qF=-n_F<=0`, `C=qF-alpha<=-1`, and guard `C*K0-n_F<=0` using `K0>=0`, a contradiction. Thus `J>0`, and positive beta gives `q>=2`; the still-shifted `s` gives `Y=q³*s>=q³>0`.

Put `a=Y`, `H=4Y+3` and `U=Yq²`. The positive main factor gives `Dstar²=U²*(1+(a²+H)c²)`. Since `U>0`, integer square divisibility yields `Dstar=U*d` for some signed integer `d`. The literal graph gives `Dstar=U*a*c+H*shift`, so `H` divides `U*(d-a*c)`; the norm gives `(d-a*c)(d+a*c)=1+H*c²`. Multiplying the latter by `U` and using the former shows `H` divides `U`. The exact identity `4U=(H-3)q²` then makes `H` divide `3q²`, impossible because `0<3q²<H=4Y+3`. This proves `w>0`; predecessor/increment maps give both zero-existence directions. No sign of the main root or gamma is assumed. This paragraph is an ordinary unbounded mathematical argument; finite executable checks do not replace it.

The stated local assumptions are sufficient for the w argument, while the inherited 80-to-consistency chain uses its separately documented stronger port/rank conditions. The result does not establish Lean elaboration, an iPRA derivation, physical coefficient/PDF binding, or provider closure.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w79-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w79-independent/result.json
```
