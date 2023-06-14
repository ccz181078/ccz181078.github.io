;
(()=>{
let cmp=(m1,m2)=>{
	if(m1===Infinity){
		if(m2===Infinity)return 0
		return 1
	}else if(m2===Infinity){
		return -1
	}
	if((typeof m1)=='number'){
		if((typeof m2)=='number'){
			return m1<m2?-1:m2<m1?1:0
		}
		return -1
	}else if((typeof m2)=='number'){
		return 1
	}
	for(let i=0;i<Math.min(m1.length,m2.length);++i){
		let x=cmp(m1[i],m2[i])
		if(x!=0)return x
	}
	if(m1.length<m2.length)return -1
	if(m1.length>m2.length)return +1
	return 0
}
let makeFS=(dom_,fs_)=>{
	return {
		dom:dom_,
		fs:(n)=>{
			if(cmp(n,dom_)<0)return fs_(n)
			console.log(to_str(n)+' < '+to_str(dom_)+' : '+cmp(n,dom_))
			throw Exception()
		}
	}
}
let iter=(f,n,x)=>{
	for(let i=0;i<n;++i){x=f(x)}
	return x
}
let is_nat=(x)=>{
	return ((typeof x)=='number') && x>=0 && Number.isInteger(x)
}
let expr=(b,a,c)=>{
	if(c===0)return b
	if(b===0 && a===0 && is_nat(c))return c
	return [b,a,c]
}
let inc=(x,y)=>{
	if(is_nat(x)){
		if(y===0)return x+1
		if(x===0)return expr(0,y,1)
		throw Exception()
	}
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let sgn=cmp(a,y)
		if(sgn<0){
			console.log('inc: '+to_str(x)+' '+to_str(y)+'  sgn='+sgn)
			throw Exception()
		}
		if(sgn===0){
			return expr(b,a,inc(c,0))
		}
		return expr(expr(b,a,c),y,1)
	}
	throw Exception()
}
let w=expr(0,0,expr(0,1,1))
/*
cf(a)=1
	p(b(a,d+1),c) = b(a,d)(a[0],c)
cf(a)>1, c<cf(a)
	p(b(a,d+1),c) = b(a,d)(a[c],1)
*/
let p=(x,n)=>{
	if(is_nat(x)){
		x=[0,0,x]
	}
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let c_=expr_FS(c)
		if(c_.dom===1){
			let a_=expr_FS(a)
			if(a_.dom===0)throw Exception()
			if(a_.dom===1){
				return expr(expr(b,a,c_.fs(0)),a_.fs(0),n)
			}
			return expr(expr(b,a,c_.fs(0)),a_.fs(c),1)
		}
		throw Exception()
	}
	throw Exception()
}
/*
in A expr
设 x = b(a,c)

cf(c)=1
	cf(a)=0
		x[0] = b(a,c[0]), cf(x)=1
	cf(a)=1
		x[n] = b(a,c[0])(a[0],n), cf(x)=A
	cf(a)>1
		x[n] = b(a,c[0])(a[n],1), cf(x)=cf(a)
cf(c)>1
	x[n] = b(a,c[n]), cf(x)=cf(c)
*/
let nat_FS=(x)=>{
	if(is_nat(x)){
		if(x===0){
			return makeFS(0,(n)=>{throw Exception()})
		}
		return makeFS(1,(n)=>x-1)
	}
	console.log(to_str(x)+' is not nat')
	throw Exception()
}
let Aexpr_FS=(x)=>{
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let c_=expr_FS(c)
		if(c_.dom===0)throw Exception()
		if(c_.dom===1){
			let a_=Aexpr_FS(a)
			if(a_.dom===0){
				return makeFS(1,(n)=>expr(b,a,c_.fs(0)))
			}
			if(a_.dom===1){
				return makeFS(Infinity,(n)=>expr(expr(b,a,c_.fs(0)),a_.fs(0),n))
			}
			return makeFS(a_.dom,(n)=>expr(expr(b,a,c_.fs(0)),a_.fs(n),1))
		}
		return makeFS(c_.dom,(n)=>expr(b,a,c_.fs(n)))
	}
	return nat_FS(x)
}
let expr_FS=(x)=>{
	if(x===Infinity){
		return makeFS(w,(n)=>expr(0,0,iter((t)=>expr(0,t,1),n,0)))
	}
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let c_=expr_FS(c)
		if(c_.dom===0)throw Exception()
		if(c_.dom===1){
			let a_=Aexpr_FS(a)
			if(a_.dom===0){
				return makeFS(1,(n)=>expr(b,a,c_.fs(0)))
			}
			if(a_.dom===1||a_.dom===Infinity){
				return makeFS(x,(n)=>n)
			}
			if(cmp(a_.dom,x)<0){
				return makeFS(a_.dom,(n)=>p(x,n))
			}
			return makeFS(w,(n)=>iter((t)=>p(x,p(a_.dom,t)),n,0))
		}
		let y=inc(b,inc(a,0))
		if(cmp(c_.dom,y)<0){
			return makeFS(c_.dom,(n)=>expr(b,a,c_.fs(n)))
		}
		return makeFS(w,(n)=>p(y,iter((t)=>c_.fs(p(c_.dom,t)),n,0)))
	}
	return nat_FS(x)
}
/*
设 x = b(a+1,d)(a,c)
cf(c)=1
	cf(a)=0
		x[0] = b(a+1,d)(a,c[0]), cf(x)=1
	cf(a)∈{1,A}
		x[n] = n, cf(x)=x
	1<cf(a)<x
		x[n] = p(x,n), cf(x)=cf(a)
	x≤cf(a)<A
		x[n] = t(n), cf(x)=ω
		t(0)=0, t(n+1)=p(x,p(cf(a),t(n)))
1<cf(c)<b(a+1,d+1)
	x[n] = b(a+1,d)(a,c[n]), cf(x)=cf(c)
cf(c)≥b(a+1,d+1)
	x[n] = p(b(a+1,d+1), t(n)), cf(x)=ω
	t(0)=0, t(n+1)=c[p(cf(c),t(n))]
*/
let to_str=(x)=>{
	if(x instanceof Array && x.length==3){
		let y=x.map(to_str)
		return (x[0]===0?'':y[0])+'('+y[1]+','+y[2]+')'
	}
	return ''+x
}
let refl_is_lim=(x,n)=>{
	return cmp(w,expr_FS(x).dom)===0
}
let refl_FS=(x,n)=>{
	return expr_FS(x).fs(n)
}
register.push({
   id:'refl_Tree'
   ,name:'refl Tree'
   ,display:to_str
   ,able:refl_is_lim
   ,compare:cmp
   ,FS:refl_FS
   ,init:()=>([
      {expr:Infinity,low:[0],subitems:[]}
      ,{expr:0,low:[0],subitems:[]}
   ])
})
})()