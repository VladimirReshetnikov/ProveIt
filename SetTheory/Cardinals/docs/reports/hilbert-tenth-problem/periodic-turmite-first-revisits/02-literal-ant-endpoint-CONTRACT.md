# Exact endpoint attachment contract

## Parent history assumptions

The parent supplies integer values W, FinalHead and FinalSignPlus. Its proved history relation guarantees integers w,h,j with

    w odd, w >= 3; h even, h >= 2;
    W = 3^w; Q = W^h;
    0 <= j < w*h; FinalHead = 3^j < Q.

The canonical coordinates are x=j mod w and y=floor(j/w), with x east and y south. The final snapshot is after the certified positive number of ordinary ant steps and before the next turn/flip/move. The heading sign is FZ/FinalHead, where FZ=FinalSignPlus-1 is either zero or FinalHead. On a white square (x+y odd), sign zero means east; on a black square sign zero means north. No width-period divisibility is assumed.

The checkerboard parity is a geometric convention, unrelated to the cell's binary ant color. Color zero turns right and flips to one; color one turns left and flips to zero. The finite history has no edge wrapping or reflection and stays entirely in its board.

The 174-operation parent component has five positive parameter ports, 61 positive unknowns and 48 equations. W is reused from its existing witnesses; FinalHead and FinalSignPlus are existing parameter ports. This packet re-proves none of those upstream counts and does not execute its source. It adds only the sources and witnesses listed below. Source multiplication gates are charged M; addition/subtraction gates are charged A. Fixed literals and wire aliases are free. An asserted equality costs no arithmetic gate unless its sides are explicitly built by an operation.

## Fixed values and formulas

Set

    u=481238074400, x0=481225262775,
    v=576000, y0=29948,
    K=3^x0, C=3^u-1, D=C-1,
    A=W^v, T=W^y0.

u,v are even, x0 is odd, and y0 is even. All residues are canonical. K,C,D are fixed prescribed integers, never existential witnesses. In the strict source their construction is paid by 57 multiplications and two subtractions; in the free-fixed-numeral source the recipes are exact specifications of constant ports. Numeric expansions are unnecessary for the exact source description.

Three-witness form: supply positive HxPlus,HyPlus,BoundCol, compute

    U=C*HxPlus-D = 1+C*(HxPlus-1),
    V=1+(A-1)*(HyPlus-1),
    Col=K*U,

and assert

    Col+BoundCol=W,
    (Col*T)*V=FinalHead,
    FinalSignPlus=1.

Five-witness form: supply positive U,V,Uq,Vq,BoundCol and assert

    U+D=C*Uq,
    (V-1)+(A-1)=(A-1)*Vq,
    K*U+BoundCol=W,
    ((K*U)*T)*V=FinalHead,
    FinalSignPlus=1.

All arithmetic intermediates are expressions over the ports and supplied witnesses. They need not themselves be positive; in particular HxPlus-1 and HyPlus-1 may be zero. Positivity of U and V in the first form follows from the displayed formulas; the first two equations force the same values in the second form. The strict column slack prevents row carry. The parent FinalHead<Q bound supplies the row bound. The proof in ENDPOINT_AUDIT.md establishes equivalence to x congruent x0 modulo u and y congruent y0 modulo v, and the parity plus FinalSignPlus=1 establishes heading east.

## Exact variable and degree conventions

There are three inherited expression ports and either three or five new quantified positive witnesses. The free-fixed-numeral ports are coefficients, not arbitrary parameters. New gate names introduce no independent variables. The canonical expanded endpoint equations have total degrees, in the inherited ports and new witnesses:

    three-witness: 1, 605950, 1;
    five-witness:  1, 576001, 1, 29950, 1.

The three-witness head equation has leading coefficient K*C > 0 at the monomial W^(v+y0)*HxPlus*HyPlus; its degree is v+y0+2=605950. The five-witness vertical equation has leading coefficient -1 at W^v*Vq; its degree is v+1=576001. Its head equation has degree y0+2=29950. These are exact endpoint degrees with W regarded as an existing port, before substituting any parent expression or combining equations. They are neither final polynomial degrees nor counts for a combined universal system.

## Relation to the literal acceptance port

The frozen literal interface uses periods (576000,481238074400), fixed initial head (288650,75,E), and pre-departure heading S at either residue pair (546702,240606225650) or (258702,481225262850). Its global proof establishes that only the second clause can occur on valid primary U15 loads.

The orientation-preserving quarter-turn and translation

    X=y-75, Y=288650-x

put the initial head at (0,0,N), swap the two periods, and send the second clause exactly to (481225262775,29948,E). This affine normalization flips the parity of the original coordinate sum, putting the original east-facing start at the black north-facing origin. The displayed normalized acceptance residues have odd coordinate sum and hence are white. Further translations by integer multiples of the respective even periods preserve the residue predicate and the black north-facing start. Fitting a finite prefix inside an odd-width/even-height rectangle and encoding that translated board are still separate input obligations; they are not free conversions supplied by this endpoint.

On valid loads, the literal interface proves that initialization, routing and incomplete-layer visits do not satisfy its predicate before source halt, and that the whole infinite physical ant trajectory visits each cell at most twice. This endpoint algebra only recognizes the parent history's final configuration. It does not replace those global simulation proofs or implement any arbitrary-program-to-U15-pair compiler.

## Provenance and scope

Pinned parent history note:
https://github.com/VladimirReshetnikov/ProveIt/blob/5883b08b7af362077f13bb4afa97a23a90ae4cf8/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md

Downloaded-note SHA256:
9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656

The parent note was inspected read-only, especially sections 1, 6, 7 and 10. No upstream program or schedule was run. This packet states all assumptions it uses and proves the new attachment relative to them. Its own-code replay requires no upstream file.

Frozen literal-interface v2 ZIP SHA256:
70a2a87ddb1ab018ec8c795dad56d053f66855a9b47ab7f3a9b64cf1164b852f

Its global proof SHA256:
a8b4a65ad97a06f3c854a9d133e67dca240d6212749f42ed6c4a92b30318483b

The underlying qualitative periodic-background turmite universality and two-visit principle are credited to Maldonado, Gajardo, Hellouin de Menibus and Moreira, arXiv:1702.05547v1, Theorems 2.1/3.1 and section 5:
https://arxiv.org/html/1702.05547

No full article is bundled. The literal interface is a separately reviewed realization of that qualitative literature, not a new attribution of its universality theorem. No public repository write was made. No arithmetic cost for raw input, the periodic initial word, dilution/dilation, rectangle placement, acceptance disjunction, or single-polynomial combination is hidden in the endpoint ledger.
