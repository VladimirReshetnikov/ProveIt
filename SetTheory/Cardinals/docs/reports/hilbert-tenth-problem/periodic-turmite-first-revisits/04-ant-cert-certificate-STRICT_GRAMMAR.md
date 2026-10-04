# Exact literal 1/3 prefix, recovered specification

This is a finite topological source grammar, deliberately unoptimized and not expanded. Only literal 1 and literal 3 are initial constants. Let u=481238074400, v=576000, x0=481225262775. These are fixed source-loop endpoints, not run-time inputs. Let lambda(e) be the number of gates in a left-to-right binary power chain: zero for e=0,1; otherwise floor(log2(e))+popcount(e)-1.

1. Compute 0=1-1, minusOne=0-1 and 2=1+1
2. Independently build Cu=3^u, Cbase=3^(u-219), C198=3^198 by those binary chains, then Cx=Cu-1
3. For each j=0,...,v-1 use the fixed bits b(i,j)=c(288650-j,i+75), 0<=i<u. Compute tile:j from b(u-1,j),...,b(0,j) by full ternary Horner evaluation, retaining every multiplication and addition even on zero symbols. Each costs u-1 M and u-1 A
4. first:j aliases the fixed bit b(0,j), hence aliases 0 or 1
5. For each j=0,...,583, delta(i,j), 0<=i<=220, is the frozen anchor's new-old at (289200-j,i-144), or zero where no anchor cell occurs. Compute anchor:j by all 220 M and 220 A of its 221-symbol signed ternary Horner chain. Symbols alias minusOne,0,1
6. Compute 4=2+2, 6=3+3, 8=4+4 and 9=3*3
7. Independently build EndpointK=3^x0 and EndpointD=Cx-1

The total color recipe c and its exact read closure are the authenticated frozen data under dependencies/recipe_assets. They specify fixed source bits; they are never imported or executed by replay. The anchor is data/anchor_patch.json. This is not an input-dependent oracle.

The base prefix from steps 1--5 costs

    M0=v(u-1)+584*220+lambda(u)+lambda(u-219)+lambda(198)
      =277193130853952587
    A0=v(u-1)+584*220+4=277193130853952484.

The chain lengths are 47,50,10,55 for u,u-219,198,x0 respectively. Steps 6--7 add 56M+4A. The complete merged prefix is therefore

    M=277193130853952643
    A=277193130853952488
    total=554386261707905131.

Zero in the final assertion, history numeral 6, and both endpoint numerals are explicitly paid. Cx is shared. Every multiplication by a fixed coefficient in the main source remains charged there. There are 1,152,598 coefficient labels: 576000 tile rows, 576000 first-column bits, 584 anchor rows, six named coefficients and eight ordinary literals {0,1,2,3,4,6,8,9}. Equal-valued labels need not be distinct integers.

Full strict source totals are 554386261710212588 operations for two raw inputs and 554386261710212598 for one. The prefix adds no witnesses or equations and leaves exact variable degree 2304000 unchanged. These counts describe this exact grammar, not an optimized bound.
