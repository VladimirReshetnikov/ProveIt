% Finite class/closure kernel. Genuine equality; no finite-domain assumption.
% A research proposal, not a TM state-count certificate.
cnf(k01,axiom,(v(upd(S,J,Z),J) = Z)).
cnf(k02,axiom,(K = J | v(upd(S,J,Z),K) = v(S,K))).
cnf(k03,axiom,(~eps(S,n(A,B)) | ~eps(S,A) | ~eps(S,B))).
cnf(k04,axiom,(eps(S,n(A,B)) | eps(S,A))).
cnf(k05,axiom,(eps(S,n(A,B)) | eps(S,B))).
cnf(k06,axiom,(~eps(S,a(J,K)) | e(v(S,J),v(S,K)))).
cnf(k07,axiom,(eps(S,a(J,K)) | ~e(v(S,J),v(S,K)))).
cnf(k08,axiom,(~eps(S,q(J,A)) | eps(upd(S,J,w(J,A,S)),A))).
cnf(k09,axiom,(~eps(upd(S,J,Z),A) | eps(S,q(J,A)))).
cnf(k10,axiom,(eps(upd(upd(B,c0,target(B)),n(c0,c0),next(B,Q)),v(B,c0)) | e(w(c0,a(c0,n(c0,c0)),upd(c0,n(c0,c0),X)),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k11,axiom,(e(mem(B,Q),next(B,Q)) | e(w(c0,a(c0,n(c0,c0)),upd(c0,n(c0,c0),X)),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k12,axiom,(~e(mem(B,Q),Q) | e(w(c0,a(c0,n(c0,c0)),upd(c0,n(c0,c0),X)),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k13,axiom,(eps(upd(upd(B,c0,target(B)),n(c0,c0),next(B,Q)),v(B,c0)) | ~e(X,target(B)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k14,axiom,(e(mem(B,Q),next(B,Q)) | ~e(X,target(B)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k15,axiom,(~e(mem(B,Q),Q) | ~e(X,target(B)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,target(B)))).
cnf(k16,axiom,(eps(upd(upd(B,c0,target(B)),n(c0,c0),next(B,Q)),v(B,c0)) | ~e(Y,target(B)) | eps(upd(upd(B,c0,next(B,Y)),n(c0,c0),Y),v(B,c0)))).
cnf(k17,axiom,(e(mem(B,Q),next(B,Q)) | ~e(Y,target(B)) | eps(upd(upd(B,c0,next(B,Y)),n(c0,c0),Y),v(B,c0)))).
cnf(k18,axiom,(~e(mem(B,Q),Q) | ~e(Y,target(B)) | eps(upd(upd(B,c0,next(B,Y)),n(c0,c0),Y),v(B,c0)))).
