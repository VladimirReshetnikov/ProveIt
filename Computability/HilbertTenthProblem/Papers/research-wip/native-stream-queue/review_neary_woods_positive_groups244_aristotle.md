# Independent review of the two-positive-group U9 compiler244

PASS for the frozen author trio below. The full new carry proof, positive-domain maps and both complete static source changes check. The construction has244=129M+115A operations,43 positive witnesses and inherited degree bound936 on the same valid four/five-program-parameter U9 slices. No correction is requested.

| Frozen author file in /tmp | SHA256 |
|---|---|
| `neary_woods_positive_groups244_tesla.md` |`8f4bcdb21a1202c618de0e2b6cd9cb3f5d83372cf9ab83f59ee8f32d3701ff07`|
| `neary_woods_positive_groups244_tesla.py` |`21bfe676106749fefe71bd0f5b32e3cd8689f3e68c24f4798782fb717750d203`|
| `neary_woods_positive_groups244_tesla.json` |`59fb18b0cda52249afab70bf7e2952e80378ab41961e299d809dfa20e322003b`|

## 1. Complete affine identity and static accounting

The map into245 is Shat3_old=G03−S0+1 and g_old=g+S0, with every other supplied coordinate and every fixed numeral unchanged. It transforms old linear_group164=S0+Shat3 to G03+1 and old selector_sum6 to G12+G03+1. Consequently the old subtraction1 becomes the direct paid addition J=G12+G03. The two intermediate group/sum rows can be deleted.

The old private size row has value g_old+Shat1=g+S0+Shat1. The child retains the literal row group_global_slack=g+Shat1 and adds groups_size_slack=group_global_slack+S0; P now consumes the latter. The retained row's intermediate value is not asserted identical under the map. Its only former consumer was P, and that consumer is redirected to the matching new exit. Thus the whole size cone preserves P. The upper transport already consumes J in245, so no other compensation is required.

I independently checked the actual parent consumer lists: Shat3 occurs only in linear_group164, that row only in selector_sum6, that row only in J, and group_global_slack only in P. The child has the exact new private size chain. These cuts exhaust the changed cones. Every other instruction and fixed numeral is literal retained data, establishing the full all-ring identity F244(new)=F245(mapped old), including the actual final polynomial. It is not merely a same-zero or accepting-history identity.

Fresh original inline metadata checking compared all rows of both source variants, without interpreting their arithmetic. Each has241 literal retained records, two edited records, two deleted additions and one new addition, totaling244=129M+115A. Both saved orders are topological, every destination is unique, every row and supplied port is live, and all ten unchanged fixed numeral roles are used. There are43 auxiliaries and49/48 total free ports in the separate/merged program variants. The sole auxiliary rename is Shat3→G03; ordinary input, fixed program parameters and positive-domain metadata are unchanged.

The actual output remains lower_history_product−geo__A, and the certificate comparison remains lower_history_product=geo__A. All other final-product records are retained. Hence the certificate costs243=129M+114A with one comparison, while the complete polynomial costs244. The affine map transfers the accepted936 bound without evaluating the source or propagating degrees.

## 2. Signed bounds without either selector-order assumption

The child's P is a sum of eight positive supplied quantities and includes both S0 and Shat1=S1+1. Hence P≥8, S0<P and S1<P before equations. J=G12+G03≥2, since both groups are positive. The signed repunit relation P=(b−1)J+epsilon, b=c_h D, c_h≥32, D≥1, gives J≤P/6 and b−1≤P+1. Neither S0≤J nor S1≤J is used.

The coefficients of Ctree=G12+P S0+P²S1 are below P. The signed Mtree expansion has coefficients J, G03+(1−epsilon)G12, G12, each at most3J≤P/2≤P−2. Therefore

    Ctree<P³, Mtree≤P³−P²−P−2,
    Mb=(b−1)Ctree<(P+1)P³,
    Mb+P³Mtree<P³(Mtree+P+1)<P⁶.

The other history/selected coefficients are below P by the same positive sum; Hb,Zb<P³ and Hr,Mr<P². Thus H0,M0,Z<P⁸ despite possible physical-mask carries. Adding the top fields gives H−Z≥P⁸+1, M−Z≥1 and bP⁸−H−M+Z≥(b−5)P⁸+2. Together with unchanged low padding these prove the positive truth-field hypotheses before any selector typing.

The accepted local norm/rank/index interface consequently recovers the joint dyadic scale and its positive factors b,P. This is a local native application, not an invocation of full245 with a possibly nonpositive virtual selector. The geometry/low-mask signs remain inherited. The independent Mersenne argument then gives epsilon=1 and P=b^t: for b=2^d, d≥5, the possible powers of two modulo2^d−1 are1,2,...,2^(d−1), so none is−1 and only exponents divisible by d give1. No Boolean selector premise enters this step.

## 3. Both controller lanes survive the nested carry

Put m=b−1. After that recovery, mG12≤mJ=P−1, while the two other physical coefficients may overflow. The exact successive carries are

    c1=floor(mS0/P), c2=floor((mS1+c1)/P).

Since S0,S1≤P−1, both carries lie between0 and m−1=b−2. In particular mS1+c1≤m(P−1)+(m−1)=mP−1. The full physical mask is

    Mb=mG12+P r1+P² r2+P³ c2,
    0≤mG12,r1,r2<P.

Thus only c2 enters the controller mask, whose digits become J+c2,G03,G12. There is no further controller carry because

    J+c2≤J+b−2<P,
    P−(J+b−2)=(b−2)(J−1)+1>0.

The earlier P⁶ bound also protects the range region. H and Z have the same unchanged controller digits G12,S0,S1. As P is a power of two, extracting their P⁴ and P⁵ digit blocks from the recovered exact AND gives respectively S0 AND G03=S0 and S1 AND G12=S1. These two equalities hold before either selector-order condition is assumed.

They imply S0≤G03≤J and S1≤G12≤J. First c1=0 follows from mS0≤P−1, and then c2=0 follows from mS1≤P−1. In particular Shat3_old=G03−S0+1≥1. The other changed old coordinate g+S0 was positive from the start. Only now is the all-ring identity used as a genuine positive245 zero and its complete compiler theorem invoked. This avoids a circular parent call and justifies both lane extractions even when the raw physical mask overflowed.

## 4. Converse, retained failures and scope

For every positive245 zero, its typed S0 is positive and S3=Shat3−1 is nonnegative, so G03_new=S0+S3>0. The quantitative bound g245≥30J−1 applies to every such zero: under the already proved245→247 bijection, g247≥31J and Shat1≤J+1, while g245=g247−Shat1. Since the typed S0≤J, the inverse slack satisfies g244=g245−S0≥29J−1≥28>0. This is stronger than merely knowing that the parent slack is positive. The two affine maps are inverse on full positive tuples, with all native witnesses, ordinary input and program parameters retained.

The actual-U9 prefix and prior word-language theorem retain their established valid-slice scope. There is no assertion of a matching history on a rejecting input or on arbitrary malformed program parameters. The unbounded existential duration and complete paid endpoint obligations remain unchanged.

Author Remark1 correctly records that supplying G03 alone does not bound S0 by J. Remark2 correctly retains the omitted-middle-carry failure: for b=32,P=1024,J=33,S0=34,S1=33, one has c1=1 and c2=1, whereas floor(31S1/P)=0. The listed positive coordinates sum to1024. Both displayed controller tests reject that untyped tuple. It is explicitly not a compiler zero, and the proof uses the corrected nested formula throughout.

I read the complete final244 proof and helper inertly and inspected both complete244/245 source arrays as static records. The complete245 proof/source review is independently frozen as review_neary_woods_positive_group245_aristotle.md; its accepted247 and250 local interfaces are inherited here. This does not re-prove the old machine simulation or every native Pell lemma. Author finite diagnostic descriptions were read without replay; their sample counts are not independently recertified by this review.

No archived, supplied, predecessor, committed or frozen code was executed or imported. No saved source array was evaluated numerically, expanded symbolically or used for degree propagation. Only fresh original inline byte/row/topology/liveness/count metadata code ran. No repository edit or build occurred. The reviewer artifacts are this Markdown and its binding JSON; the draft static scratch receipt is not a separate frozen artifact.
