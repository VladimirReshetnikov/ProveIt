#define main prior_main
#include "polynomials.cpp"
#undef main
int deg(Code code){int s=0;while(code){s+=code&7;code>>=3;}return s;}
int main(int argc,char**argv){string folder=argc>1?argv[1]:".";ifstream in(folder+"/gamma.tsv");ofstream out(folder+"/core_corrections.jsonl");int id,d,n;while(in>>id>>d>>n){array<Poly,5>g;for(int j=0;j<n;j++){Code code;in>>code;for(int k=0;k<5;k++){ll c;in>>c;if(c)g[k][code]=c;}}Poly F3,C2,B1,E;for(auto[e,c]:g[3]){if(deg(e)==3)F3[e]=c;else{assert(deg(e)==2);C2[e]=c;}}for(auto[e,c]:g[2])if(deg(e)<2)B1[e]=c;binproduct(F3,C2,E,6,d);binproduct(C2,C2,E,3,d);binproduct(B1,g[4],E,-8,d);int neg=0;for(auto[e,c]:E)neg+=c<0;out<<"{\"id\":"<<id<<",\"variables\":"<<d<<",\"E\":";print_poly(out,E);out<<"}\n";cout<<"id="<<id<<" variables="<<d<<" negative_coefficients="<<neg<<endl;}}
