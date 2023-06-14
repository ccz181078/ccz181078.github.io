;
(()=>{
let dbg=(x)=>{
	//console.log(x)
}
let flat=(x)=>{
	if(x===0)return []
	if(x instanceof Array && x.length==3){
		let y=flat(x[0])
		y.push(x[1])
		y.push(x[2])
		return y
	}
	throw Exception()
}
let cmp=(m1,m2)=>{
	if(m1===Infinity){
		if(m2===Infinity)return 0
		return 1
	}else if(m2===Infinity){
		return -1
	}
	if(m1===0){
		if(m2===0){
			return 0
		}
		return -1
	}else if(m2===0){
		return 1
	}
	m1=flat(m1)
	m2=flat(m2)
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
			dbg(to_str(n)+' < '+to_str(dom_)+' : '+cmp(n,dom_))
			throw Exception()
		}
	}
}
let to_nat=(x)=>{
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		if(b===0 && a===0){
			return to_nat(c)+1
		}
		throw Exception()
	}
	if(x===0)return 0
	throw Exception()
}
let iter=(f,n,x)=>{
	for(let i=0;i<n;++i){x=f(x)}
	return x
}
let expr=(b,a,c)=>{
	return [b,a,c]
}
let inc=(x,y)=>{
	if(x===0){
		return expr(0,y,0)
	}
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let sgn=cmp(a,y)
		if(sgn<0){
			dbg('inc: '+to_str(x)+' '+to_str(y)+'  sgn='+sgn)
			throw Exception()
		}
		if(sgn===0){
			return expr(b,a,inc(c,0))
		}
		return expr(expr(b,a,c),y,0)
	}
	throw Exception()
}
let one=expr(0,0,0)
let w=expr(0,0,expr(0,one,0))
/*
b(a,0-1)=b
b(a,c+1-1)=b(a,c)
*/
let dec=(b,a,c,f1,f2)=>{
	dbg('dec '+to_str(b)+' '+to_str(a)+' '+to_str(c))
	let c_=expr_FS(c)
	if(c_.dom===0){
		return f1(b)
	}
	if(cmp(c_.dom,one)===0){
		return f1(expr(b,a,c_.fs(0)))
	}
	return f2(c_)
}
/*
cf(a)=1
	p(b(a,c),n) = b(a,c-1)(a[0],n)
cf(a)>1, n<cf(a)
	p(b(a,c),n) = b(a,c-1)(a[n],0)
*/
let p=(x,n)=>{
	dbg('p '+to_str(x)+' '+to_str(n))
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let ret=dec(b,a,c,(y)=>{
			let a_=Aexpr_FS(a)
			if(cmp(a_.dom,one)===0){
				return expr(y,a_.fs(0),n)
			}
			dbg('fs '+to_str(a)+' '+to_str(n)+' = '+to_str(a_.fs(n)))
			return expr(y,a_.fs(n),0)
		},(c_)=>{
			throw Exception()
		})
		dbg('p '+to_str(x)+' '+to_str(n)+' = '+to_str(ret))
		return ret
	}
	throw Exception()
}
/*
in A expr
设 x = b(a,c)

cf(c)≤1
	cf(a)=0
		x[0] = b(a,c-1), cf(x)=1
	cf(a)=1
		x[n] = b(a,c-1)(a[0],n), cf(x)=A
	cf(a)>1
		x[n] = b(a,c-1)(a[n],0), cf(x)=cf(a)
cf(c)>1
	x[n] = b(a,c[n]), cf(x)=cf(c)
*/
let Aexpr_FS=(x)=>{
	dbg('Aexpr_FS '+to_str(x))
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		let ret=dec(b,a,c,(y)=>{
			let a_=Aexpr_FS(a)
			if(a_.dom===0){
				return makeFS(one,(n)=>y)
			}
			if(cmp(a_.dom,one)===0){
				return makeFS(Infinity,(n)=>expr(y,a_.fs(0),n))
			}
			return makeFS(a_.dom,(n)=>expr(y,a_.fs(n),0))
		},(c_)=>{
			return makeFS(c_.dom,(n)=>expr(b,a,c_.fs(n)))
		})
		dbg('Acf '+to_str(x)+' = '+to_str(ret.dom))
		return ret
	}
	if(x===0){
		return makeFS(0,(n)=>{throw Exception()})
	}
	throw Exception()
}
/*
设 x = b(a+1,d)(a,c)
cf(c)≤1
	cf(a)=0
		x[0] = b(a+1,d)(a,c-1), cf(x)=1
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
let expr_FS=(x)=>{
	dbg('expr_FS '+to_str(x))
	if(x===Infinity){
		return makeFS(w,(n)=>expr(0,0,iter((t)=>expr(0,t,0),to_nat(n),0)))
	}
	if(x instanceof Array && x.length==3){
		let b=x[0]
		let a=x[1]
		let c=x[2]
		return dec(b,a,c,(y)=>{
			let a_=Aexpr_FS(a)
			if(a_.dom===0){
				return makeFS(one,(n)=>y)
			}
			if(cmp(a_.dom,one)===0||a_.dom===Infinity){
				return makeFS(x,(n)=>n)
			}
			if(cmp(a_.dom,x)<0){
				return makeFS(a_.dom,(n)=>p(x,n))
			}
			return makeFS(w,(n)=>iter((t)=>p(x,p(a_.dom,t)),to_nat(n),0))
		},(c_)=>{
			let y=inc(b,inc(a,0))
			if(cmp(c_.dom,y)<0){
				return makeFS(c_.dom,(n)=>expr(b,a,c_.fs(n)))
			}
			return makeFS(w,(n)=>p(y,iter((t)=>c_.fs(p(c_.dom,t)),to_nat(n),0)))
		})
	}
	if(x===0){
		return makeFS(0,(n)=>{throw Exception()})
	}
	throw Exception()
}
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
	return expr_FS(x).fs(iter((t)=>expr(0,0,t),n,0))
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