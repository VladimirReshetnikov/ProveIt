
function setup(e){
 const h=s=> e===0?s:Math.sin(e*s)/e, c=s=>Math.cos((1+e)*s), t=s=>Math.sin((2+e)*s), hp=s=>Math.cos(e*s), cp=s=>-(1+e)*Math.sin((1+e)*s), tp=s=>(2+e)*Math.cos((2+e)*s);
 function coeff(u,v){const d=c(u)*t(v)-c(v)*t(u);return [(h(v)*t(u)-h(u)*t(v))/d,(c(v)*h(u)-c(u)*h(v))/d];}
 function fd(u,v){const [a,b]=coeff(u,v);return [hp(u)+a*cp(u)+b*tp(u),hp(v)+a*cp(v)+b*tp(v)];}
 return {h,c,t,hp,cp,tp,coeff,fd};
}
function guess(e,z){
 const {h,c,t,hp,cp,tp,coeff,fd}=setup(e); let [u,v,x]=z;
 for(let i=0;i<9;i++){const [r,s]=fd(u,v),d=1e-5,[a,c]=fd(u+d,v).map((y,i)=>(y-[r,s][i])/d),[b,f]=fd(u,v+d).map((y,i)=>(y-[r,s][i])/d),det=a*f-b*c;u-=(r*f-b*s)/det; v-=(a*s-c*r)/det;}
 const [a,b]=coeff(u,v);
 for(let i=0;i<9;i++) x-=(h(x)+a*c(x)+b*t(x))/(hp(x)+a*cp(x)+b*tp(x));
 return [u,v,x,a,b];
}

module.exports=guess;
