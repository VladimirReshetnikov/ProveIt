// Modular width certificate using a p-adic outlier and four clustered roots.
// Invoke via cm_outlier_width.py to certify the input and the local data.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Scalar = uint32_t;
using Row = std::array<Scalar, 4>;
constexpr Scalar first = 2147483647, second = 1000000007;
template<Scalar p> Scalar add(Scalar a, Scalar b) {
  uint32_t z = a + b;
  return z < p ? z : z - p;
}
template<Scalar p> Scalar sub(Scalar a, Scalar b) { return a >= b ? a-b : (a+p)-b; }
template<Scalar p> Scalar mul(Scalar a, Scalar b) { return uint64_t(a)*b % p; }
template<Scalar p> Scalar inv(Scalar a) {
  Scalar exponent = p-2, result = 1;
  while(exponent) {
    if(exponent & 1) result = mul<p>(result,a);
    a = mul<p>(a,a);
    exponent >>= 1;
  }
  return result;
}

template<Scalar p> std::vector<Row> powers(unsigned width, const std::vector<std::string>& coefficients) {
  const unsigned degree=coefficients.size();
  std::vector<Scalar> polynomial(degree), v(degree);
  for(unsigned i=0;i<degree;++i) {
    for(char c : coefficients[i]) if(c!='-')
      polynomial[i] = add<p>(mul<p>(10,polynomial[i]),c-'0');
    if(coefficients[i][0]=='-') polynomial[i] = sub<p>(0,polynomial[i]);
  }
  v[0]=1;
  std::vector<Row> answer(width+1);
  for(unsigned e=1;e<=width;++e) {
    Scalar high=v.back();
    for(int i=int(degree)-1;i>=0;--i) v[i]=sub<p>(i==0 ? 0 : v[i-1],mul<p>(high,polynomial[i]));
    // Project A/<1> to four coordinates; full rank of the image implies
    // full rank before projection.  All inputs have degree five or six.
    for(unsigned i=0;i<4;++i) answer[e][i]=degree==5 ? v[i+1] : add<p>(v[i+1],v[5]);
  }
  return answer;
}

template<Scalar p> Scalar det2(Scalar a, Scalar b, Scalar c, Scalar d) {
  return sub<p>(mul<p>(a,d),mul<p>(b,c));
}
template<Scalar p> Scalar minor(const Row& a, const Row& b, unsigned i, unsigned j) {
  return det2<p>(a[i],a[j],b[i],b[j]);
}
template<Scalar p> bool independent(Row a, Row b, Row c, Row d) {
  std::array<Row,4> matrix={a,b,c,d};
  for(unsigned j=0;j<4;++j) {
    unsigned k=j;
    while(k<4 && matrix[k][j]==0) ++k;
    if(k==4) return false;
    std::swap(matrix[k],matrix[j]);
    for(unsigned i=j+1;i<4;++i) {
      Scalar factor=matrix[i][j], pivot=matrix[j][j];
      for(unsigned column=j+1;column<4;++column)
        matrix[i][column]=det2<p>(pivot,matrix[j][column],factor,matrix[i][column]);
    }
  }
  return true;
}

// A point represented by (u,v) has projective coordinate u/v.  Batch
// inversion uses one exponentiation for all nonzero denominators in a list.
void normalize(std::vector<Scalar>& numerators, const std::vector<Scalar>& denominators,
               std::vector<Scalar>& products, unsigned begin, unsigned end) {
  Scalar product=1;
  for(unsigned k=begin;k<=end;++k) {
    products[k]=product;
    if(denominators[k]) product=mul<first>(product,denominators[k]);
  }
  Scalar inverse=inv<first>(product);
  for(unsigned k=end;k>=begin;--k) {
    if(denominators[k]) {
      numerators[k]=mul<first>(numerators[k],mul<first>(inverse,products[k]));
      inverse=mul<first>(inverse,denominators[k]);
    } else {
      if(!numerators[k]) throw std::runtime_error("dependent triple at first prime");
      numerators[k]=first;  // projective point at infinity
    }
  }
}

int main(int argc,char** argv) {
  if(argc!=2) throw std::runtime_error("pass exponent width");
  unsigned n=std::stoul(argv[1]);
  if(n<4 || n>1000000) throw std::runtime_error("unsupported width");
  unsigned degree, local_prime, slope_numerator, slope_denominator;
  if(!(std::cin>>degree>>local_prime>>slope_numerator>>slope_denominator))
    throw std::runtime_error("missing input");
  if(degree<5 || degree>6 || local_prime<3 || !slope_numerator || !slope_denominator)
    throw std::runtime_error("invalid input");
  std::vector<std::string> polynomial(degree);
  for(auto& coefficient:polynomial) std::cin>>coefficient;
  auto v=powers<first>(n,polynomial), w=powers<second>(n,polynomial);
  std::vector<Scalar> numerator(n+1),denominator(n+1),products(n+1);
  unsigned size=1;
  while(size<4*n) size*=2;
  std::vector<Scalar> keys(size);
  std::vector<unsigned> heads(size),seen(size),next(n+1);
  unsigned stamp=0;
  uint64_t rechecked=0,anchors=0;
  for(unsigned i=1;i<n;++i) {
    unsigned exponent=(slope_numerator*i+3*slope_denominator-1)/(3*slope_denominator);
    uint64_t step=1;
    for(unsigned z=0;z<exponent && step<=n;++z) step*=local_prime;
    if(step>n-i) break;
    // Every candidate has one such pair of positive exponents i<j.
    for(unsigned j=i+step;j<=n;j+=step) {
    ++anchors;
    std::array<unsigned,4> coords={0,1,2,3};
    while(!minor<first>(v[i],v[j],coords[0],coords[1])) {
      if(!std::next_permutation(coords.begin(),coords.end()))
        throw std::runtime_error("dependent pair at first prime");
    }
    auto [a,b,c,d]=coords;
    Scalar ab=minor<first>(v[i],v[j],a,b), ac=minor<first>(v[i],v[j],a,c);
    Scalar ad=minor<first>(v[i],v[j],a,d), bc=minor<first>(v[i],v[j],b,c);
    Scalar bd=minor<first>(v[i],v[j],b,d);
    // Two three-row minors give coordinates modulo span(v[i],v[j]).
    for(unsigned k=1;k<=n;++k) {
      if(k==i || k==j) { numerator[k]=denominator[k]=1; continue; }
      numerator[k]=add<first>(sub<first>(mul<first>(ab,v[k][c]),mul<first>(ac,v[k][b])),
                              mul<first>(bc,v[k][a]));
      denominator[k]=add<first>(sub<first>(mul<first>(ab,v[k][d]),mul<first>(ad,v[k][b])),
                                mul<first>(bd,v[k][a]));
    }
    normalize(numerator,denominator,products,1,n);
    ++stamp;
    for(unsigned k=1;k<=n;++k) {
      if(k==i || k==j) continue;
      uint32_t hash=numerator[k];
      hash ^= hash>>16; hash *= 0x7feb352dU; hash ^= hash>>15;
      unsigned slot=hash & (size-1);
      while(seen[slot]==stamp && keys[slot]!=numerator[k]) slot=(slot+1) & (size-1);
      if(seen[slot]!=stamp) {
        heads[slot]=0; keys[slot]=numerator[k]; seen[slot]=stamp;
      }
      for(unsigned l=heads[slot];l;l=next[l]) {
        ++rechecked;
        if(!independent<second>(w[i],w[j],w[l],w[k]))
          throw std::runtime_error("both primes singular at "+std::to_string(i)+","+
                     std::to_string(j)+","+std::to_string(l)+","+std::to_string(k));
      }
      next[k]=heads[slot];
      heads[slot]=k;
    }
  }
  }
  std::cout<<"width "<<n<<"\nexponent pairs checked "<<anchors
           <<"\nsecond-prime rechecks "<<rechecked<<"\nall patterns independent\n";
}
