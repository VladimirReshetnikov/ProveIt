# Independent review of the relator-normal gcd obstruction

The counterexample passes independent hand review, with no correction requested. It refutes the proposed permutation-only justification for setting g=1 in the integral-plane reconstruction. It does not exclude coefficient absorption, a different integer basis, a paid output transformation or another cheaper schedule.

I read the full65-line frozen proof and its complete metadata, and used the previously reviewed217-line plane proof and75-line independent plane review. Every calculation below is handwritten. Only file-byte and metadata authentication ran; no scientific helper, saved source/coefficient evaluation, degree propagation or numerical sampling was used.

For P=[[1651,1575],[630,601]], the determinant is992251-992250=1. Its normal numerator is(630,1050,-1575)=105(6,10,-15). The primitive normal n=(6,10,-15) has coordinate sum1, giving an explicit Bezout witness for primitivity. Its pairwise gcds are2,3,5, so every output permutation has gcd(n1,n2)>1. A global sign change does not alter these gcds.

The optional construction also checks: B0=[[5,15],[6,-5]] has B0²=115I;1126²-115*105²=1267876-1267875=1;1126I+105B0 gives exactly P. Squaring yields P²=2535751I+118230(2B0). Its norm identity follows by squaring the preceding norm-one identity. Thus no Pell existence theorem, search or numerical program is needed for the witness.

For any determinant-one matrix, the stated top-left minor of S(P)-I is -2qs. Here it is nonzero. The invariant n bounds the rank by2, and this minor bounds it below by2, so the rational left kernel is exactly the line through n. If cn is an integer vector for rational c, the sum of its three entries equals c, hence c is an integer. A primitive integer vector on this line is therefore n or -n. Choosing a different primitive invariant cannot produce a coprime coordinate pair.

The first three columns of C are triangular with diagonal(1,1,1), so they form a unimodular matrix and C maps Z^4 onto Z^3. Thus (S(P)-I)C has rank2 and the same left kernel as S(P)-I. The common invariant annihilates both blocks of W, giving the same rank2 and left-kernel conclusion for W. This proves the statement about the rational image plane. It does not identify W's integer column lattice with every integer point of that plane.

Every row of W is nonzero. Otherwise its rank2 image would equal a coordinate plane, whose normal has two zero coordinates, contrary to n. Therefore in every output permutation the third row of W' is nonzero. The established integer-plane recipe makes beta_j=W'_(3,j)/g integral, with at least one beta_j nonzero. The compiled form B is consequently a nonzero polynomial in the independent raw inputs. Since g>1, replacing gB by B while leaving all forms unchanged changes an output polynomial. Choosing the corresponding unit input already witnesses the difference.

For a concrete unrestricted-cut instance in the identity chart, take positive-slot Z4=1 and all seven other raw words zero. Here g=2 and the third component of Wz is s²-2st+2t²-2=(s-t)²+t²-2=362040. Its beta form is181020. Omitting the final multiplication by2 therefore changes that increment from362040 to181020. This is a hand-derived local-cut example, not a native witness, an accepted compiler slice or a claim about membership in the unknown universal relator list.

**Review remark 1 (retained false shortcut).** The proposed claim was that every SL2(Z) relator permits an output permutation of its primitive normal with gcd(n1,n2)=1, allowing gB to be replaced by B. The actual matrix above, uniqueness of its primitive invariant and nonzero form prove this claim false. The accepted21M19A append and complete compiler remain valid and unchanged.

**Open question 1 (other reconstruction strategies).** A different fixed factorization, coefficient absorption or charged coordinate transformation may remove or share an operation. This counterexample does not prove a20M19A impossibility or an arithmetic lower bound. Its scope is exactly the permutation-only shortcut and the unchanged-form alias deletion.

The reviewed author proof is positive7_relator_normal_gcd_obstruction_aristotle.md, SHA256f6bd2a146befd4275cba4ea631fb601b3160002255d82bfa7b4ad20b934a6e9e. The companion review receipt binds that proof, its final metadata and all four immediate plane dependency artifacts. No repository, Git, previous proof or frozen helper was changed.
