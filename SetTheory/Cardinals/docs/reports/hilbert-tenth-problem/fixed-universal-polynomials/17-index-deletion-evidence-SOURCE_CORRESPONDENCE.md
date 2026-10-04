# Literal candidate correspondence

The complete candidate arrays are preserved verbatim as inert JSON in
scout.json. They were fetched at commit
3f4a974a5ddf12c46302fc5d2edafc3730277923. Their authenticated immediate
parents are included too. check_reduction.py checks only their literal
rows, interfaces, deletion sets and ledgers; it never evaluates them.

Both candidates have exactly these supplied positive witnesses, in order:

    Jrep,F,alpha,transport_quotient,f,i,auxiliary_quotient,s,w,
    tau_root,eta,zeta,y_aux,Z,delta,rho,sigma

The ordinary positive input is x. The fixed numeral ports are exactly

    Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF

with meanings B-1,K,2d,b,MC,MF0+B-1. In particular MF is shifted.
FULL_COUNTERFAMILY.md defines every witness in this exact interface.

## Shared computed registers

| Literal register | Mathematical quantity in FULL_COUNTERFAMILY.md |
| --- | --- |
| repunit | q-1=(B-1)J |
| q,Lbig,n2 | q,q^2,q^3 |
| wn2,sn2,UM | X=wq,Y=sq^3,E=XY |
| R10b,R10a | k=eta+zeta,c=kY+eta |
| R12,a4m5,A | a0=Y(X+1),H=4a0+3,Delta=A_math^2-1 |
| gamma_sum,R14 | rho+sigma,D=X+a0*c+(rho+sigma)H |
| marked_rhs,W | C=W_math+Z,W_math=2^I |
| odd_index,index_rhs | I=2dx+b,kappa=I+delta*Delta |
| exponent_rhs | mu=W_math+a0*kappa+rho*H |
| gap,r_lhs | q^2-Z-qF,R=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J |
| kinner,local_rhs | K+w,transport_quotient*(q-1) |
| L16,aux_u_rhs | f^2,V=c(Tf-1)-Rf^2 |

The mathematical Pell parameter A_math=a0+2 must never be confused
with literal register A=Delta.

## Six actual factors and paid finalizer

| Source factor | Literal mathematical value | Proof section setting it to1 |
| --- | --- | --- |
| norm_first | tau^2-XY^2(XY^2+1)k^2 | Section4 |
| norm_main | D^2-Delta*c^2 | Section4/5 |
| norm_input | mu^2-Delta*kappa^2 | Section5 |
| norm_aux | R16*(V^2-y_aux^2)+y_aux^2 | Section7 |
| norm_transport | (K+w)C+q-F-transport_quotient*(q-1) | Section6 |
| norm_strong, normalized | f^2-Delta*(ic^2)^2 | Section7, i=iN |
| norm_strong, ordinary | 1+(ic^2)^2-Delta*(f^2-1) | Section7, i=Delta*iN |

In the normalized source R16=Delta^2*(ic^2)^2. In the ordinary source
R16=Delta*(f^2-1). Each becomes S^2 on the constructed witness.

The literal first norm's product is first_root_base*first_next, where
first_root_base=UM*ksn2=XY*(kY)=XY^2*k and
first_next=first_root_base+k. Thus its value is exactly the displayed
XY^2(XY^2+1)k^2, with no missing normalization or halved coefficient.

The complete product cone is

    norm_pair=norm_first*norm_main,
    norm_triple=norm_pair*norm_input,
    norm_four=norm_triple*norm_aux,
    all_units=norm_four*norm_transport,
    seven_units=all_units*norm_strong,
    polynomial=seven_units-1.

The historical register name seven_units contains six surviving factors.
The final subtraction is still paid and its result is exactly zero.

## Modes and exact inert source authentication

Normalized candidate:81=46M+35A,17 witnesses, degree168, parent
complete85_auxiliary_bezout_projection.json with SHA256
e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc.

Ordinary candidate:82=45M+37A,17 witnesses, degree124, parent
complete86_ordinary_auxiliary_projection.json with SHA256
f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6.

The scout JSON SHA256 is
0004189e84fdc34e1ae7cbffa30a0e904ec6a0f15be18bcabebe242a303163f8.

Only hpm1,index_difference,norm_index,norm_product are removed, and
all_units changes its left input from norm_product to norm_four.
Both authenticated arrays agree with this literal deletion. No new
compiler, altered fixed port, rescaled ordinary input or signed supplied
witness is substituted in the mathematical counterfamily.

## Fixed compiler recipe provenance

All primary recipe files are saved in provenance/ with original Git blob
IDs, commit IDs and URLs in FETCHED.json; the final manifest adds SHA256.
The pinned complete75_coupled_index_linear88.md Section1 explicitly
states MC=2 modulo4, MF0=4 modulo8, B=2^d,d>=4, and the whole inherited
compiler contract. The pinned complete75_half_binomial_compiler.md
defines the modified MC and native MF0, explicitly exports MF0+B-1,
and retains b,L,d powers of5. FIXED_RAW_UNIVERSAL_76_PROOF.md explains
b,L odd powers of5 and d=bL. Hence b is positive odd and ell=2d.
The construction uses authentic constants symbolically, rather than
asserting that the mock arithmetic fixtures implement a valid compiler.
