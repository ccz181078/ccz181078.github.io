(()=>{
let iter=(f,n,x)=>{
	for(let i=0;i<n;++i){x=f(x)}
	return x
}
let flat=(x)=>{
	if(x===0)return []
	if(x instanceof Array && x.length==3){
		let y=flat(x[0])
		y.push(x[1])
		y.push(x[2])
		return y
	}
	console.log(''+x)
	throw Exception()
}
let cmp=(m1,m2)=>{
	if(m1===Infinity){
		if(m2===Infinity)return 0
		return 1
	}else if(m2===Infinity){
		return -1
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
let expr=(s,a,b)=>[s,a,b]
let one=expr(0,0,0)
let w=expr(0,0,one)
let makeFS=(dom_,fs_)=>{
	return {dom:dom_,fs:fs_}
}
let to_nat=(y)=>{
	if(y===0)return 0
	if(y instanceof Array && y.length==3){
		if(y[1]==0 && y[2]==0){
			return to_nat(y[0])+1
		}
	}
	throw Exception()
}
let add=(x,y)=>{
	if(y===0)return x
	if(y instanceof Array && y.length==3){
		return expr(add(x,y[0]),y[1],y[2])
	}
	throw Exception()
}
let dec1=(y)=>{
	if(y instanceof Array && y.length==3){
		if(y[1]===0 && y[2]===0)return y[0]
	}
	throw Exception()
}
let expr_FS=(x)=>{
	if(x===Infinity){
		return makeFS(w,(n)=>expr(0,0,iter((t)=>expr(0,t,0),to_nat(n),0)))
	}
	if(x===0){
		return makeFS(0,(n)=>{throw Exception()})
	}
	if(x instanceof Array && x.length==3){
		let s=x[0]
		let a=x[1]
		let b=x[2]
		let b_=expr_FS(b)
		if(b_.dom===0){
			let a_=expr_FS(a)
			if(a_.dom===0){
				return makeFS(one,(n)=>s)
			}
			if(cmp(a_.dom,one)===0){
				return makeFS(expr(0,a,0),(n)=>add(s,n))
			}
			return makeFS(a_.dom,(n)=>expr(s,a_.fs(n),0))
		}
		if(cmp(b_.dom,one)===0){
			return makeFS(w,(n)=>iter((t)=>expr(t,a,b_.fs(0)),to_nat(n),s))
		}
		if(cmp(b_.dom,expr(0,add(a,one),0))<0){
			return makeFS(b_.dom,(n)=>expr(s,a,b_.fs(n)))
		}
		let y=dec1(b_.dom[1])
		return makeFS(w,(n)=>expr(s,a,iter((t)=>b_.fs(expr(0,y,t)),to_nat(n),0)))
	}
	throw Exception()
}
let EBO_able=(x)=>expr_FS(x).dom!==0
let EBO_FS=(x,n)=>{
	let x_=expr_FS(x)
	if(cmp(x_.dom,one)===0){
		if(n===0)return x_.fs(0)
		return undefined
	}
	return x_.fs(iter((t)=>add(t,one),n,0))
}
let to_str=(x)=>{
	if(x instanceof Array && x.length==3){
		let s=x[0]
		let a=x[1]
		let b=x[2]
		let n=1
		while(s instanceof Array && s.length==3 && cmp(s[1],a)===0 && cmp(s[2],b)===0){
			s=s[0]
			n+=1
		}
		let s1=to_str(s)
		let a1=to_str(a)
		let b1=to_str(b)
		return (s instanceof Array ? (s1+'+') : '')+
		(a===0 && b===0 ? (''+n):
		b==0?
		('Ω'+
		'<sub>'+
		a1+
		'</sub>'+
		(n===1?'':''+n))
		:
		('p'+
		'<sub>'+
		a1+
		'</sub>'+
		'('+
		b1+
		')')+
		(n===1?'':''+n))
		
	}
	return ''+x
}
register.push({
   id:'ExBOCF'
   ,name:'ExBOCF'
   ,display:(n)=>{return ''+to_str(n)}
   ,able:EBO_able
   ,compare:cmp
   ,FS:EBO_FS
   ,init:()=>([
      {expr:Infinity,low:[0],subitems:[]}
      ,{expr:0,low:[0],subitems:[]}
   ])
})
})()