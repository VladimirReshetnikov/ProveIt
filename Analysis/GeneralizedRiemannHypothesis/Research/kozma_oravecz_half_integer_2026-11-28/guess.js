"use strict";
module.exports=function guess(e, sign){
 const h=s=>e===0?s:Math.sin(e*s)/e, c=s=>Math.cos((1+e)*s)+sign*Math.sin((1+e)*s), t=s=>Math.cos((2+e)*s);
 const hp=s=>Math.cos(e*s),cp=s=>(1+e)*(sign*Math.cos((1+e)*s)-Math.sin((1+e)*s)),tp=s=>-(2+e)*Math.sin((2+e)*s);
 function coeff(u,v){const d=c(u)*t(v)-c(v)*t(u);return [(h(v)*t(u)-h(u)*t(v))/d,(c(v)*h(u)-c(u)*h(v))/d];}
 function fd(u,v){const [a,b]=coeff(u,v);return [hp(u)+a*cp(u)+b*tp(u),hp(v)+a*cp(v)+b*tp(v)];}
 let [u,v,x]=sign<0?[.09+.18*e,2.78-1.4*e,-1.905+e]:[1.614-.42*e,4.529-2.25*e,-.699+.39*e];
 for(let i=0;i<15;i++){
  const [r,s]=fd(u,v),d=1e-5,[a,c]=fd(u+d,v).map((y,i)=>(y-[r,s][i])/d),[b,f]=fd(u,v+d).map((y,i)=>(y-[r,s][i])/d),det=a*f-b*c;
  u-=(r*f-b*s)/det;v-=(a*s-c*r)/det;
 }
 const [a,b]=coeff(u,v);
 for(let i=0;i<15;i++)x-=(h(x)+a*c(x)+b*t(x))/(hp(x)+a*cp(x)+b*tp(x));
 return [u,v,x,a,b];
}
