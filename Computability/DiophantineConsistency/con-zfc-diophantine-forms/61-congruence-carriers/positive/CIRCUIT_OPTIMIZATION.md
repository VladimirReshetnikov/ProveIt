# Archive path convention

The final archive names the optimized files build13.py, check13.py,
p13_degree34.json, build12.py, check12.py, p12_product_split2.json, and
p12_sos_split2.json. The original packets are under reference/ with
their original gate counts in the filenames. The research names in
the retained note below describe the same verified rewrites.

# Closed literal gate optimizations

These transformations preserve the complete polynomial for every integer
assignment. They change neither the solution set nor any semantic proof.
The original research files and the assembled archive have not been edited.

## P13: 95 to 93 gates

Cache `f2m=f^2-1`, already needed by `Kaux=Delta*f2m`, and evaluate
`As=f2m-Delta*I^2`. This saves one subtraction.

Cache `y2=(V+u)^2`, and evaluate

    Aa=y2-Kaux*(y2-V^2)-1.

The identity `y2-V^2=u*(2*V+u)` shows equality with the previous residual.
This saves one gate. The resulting complete graph has 93 gates:
52 multiplications, 24 additions, 17 subtractions; its four-residual core
has 86 gates. The exact degree remains 34, with residual degrees 15,17,13,14.

Files: `build13_optimized.py`, `p13_degree34_optimized.json`,
`check13_optimized.py`, `CHECK13_OPTIMIZED.json`.

The checker compares each residual against the original 95-gate graph and
the independent mathematical specification. It also checks both actual
sum-of-squares finalizers over independent residual indeterminates.

## P12: 105 to 104 gates (product); 104 to 103 (SOS)

The main carrier already computes `Delta*c^2`. Set `ic=i*c` and evaluate

    D=1+(Delta*c^2)*ic^2,
    Caux=Delta*ic,
    Maux=Caux*c^2.

The identity `(Delta*c^2)*(i*c)^2=Delta*(i*c^2)^2` preserves D, while the
shared `ic` saves one multiplication in Caux. The mathematical abbreviation
I=i*c^2 remains valid; it is no longer a live register in the optimized graph.

The product graph has 104 gates: 60 multiplications, 26 additions,
18 subtractions. The SOS graph has 103 gates: 61 multiplications,
25 additions, 17 subtractions. Their residual core has 98 gates.
Their exact degrees remain 118 and 172, respectively.

Files: `build12_optimized.py`, `p12_product_split2_optimized.json`,
`p12_sos_split2_optimized.json`, `check12_optimized.py`,
`CHECK12_OPTIMIZED.json`.

The checker verifies the original and optimized prefix polynomials, norm
suffixes over independent cut registers, and both product/SOS finalizers.
It certifies exact polynomial equality and the existing nonzero leading
forms. The source coefficients and unbounded semantic dependencies are
unchanged. No claim that 93 or 104 gates is optimal is made.
