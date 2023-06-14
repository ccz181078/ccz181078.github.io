(()=>{
let iter=(f,n,x)=>{
	for(let i=0;i<n;++i){x=f(x)}
	return x
}
let flat=(x)=>{
	if(x===0)return []
	let y=flat(x[0])
	y.push(x[1])
	return y
}
let cmp=(m1,m2)=>{
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
let expr=(a,b)=>[a,b]
let one=expr(0,0)
let w=expr(0,one)
let makeFS=(dom_,fs_)=>{
	return {dom:dom_,fs:fs_}
}
let expr_FS=(x)=>{
	if(x===Infinity){
		return makeFS(2,(n)=>iter((t)=>expr(0,t),n,0))
	}
	if(x===0)return makeFS(0,(n)=>{throw Exception()})
	if(x instanceof Array && x.length==2){
		let a=x[0]
		let b=x[1]
		let b_=expr_FS(b)
		if(b_.dom===0)return makeFS(1,(n)=>a)
		if(b_.dom===1)return makeFS(2,(n)=>iter((t)=>expr(t,b_.fs(0)),n,a))
		if(b_.dom===2)return makeFS(b_.dom,(n)=>expr(a,b_.fs(n)))
	}
	throw Exception()
}
let e0_able=(x)=>expr_FS(x).dom!==0
let e0_FS=(x,n)=>{
	let x_=expr_FS(x)
	if(x_.dom===1){
		if(n===0)return x_.fs(0)
		return undefined
	}
	return x_.fs(n)
}
let to_str=(x)=>{
	if(x instanceof Array && x.length==2){
		let a=x[0]
		let b=x[1]
		let n=1
		while(a instanceof Array && a.length==2 && cmp(a[1],b)===0){
			a=a[0]
			n+=1
		}
		let a1=to_str(a)
		let b1=to_str(b)
		return (a instanceof Array ? (a1+'+') : '')+
		(b===0?''+n:'ω'+(b1==='1'?'':'<sup>'+b1+'</sup>')+(n===1?'':''+n))
	}
	return ''+x
}
register.push({
   id:'e0'
   ,name:'ε0'
   ,display:(n)=>{return ''+to_str(n)}
   ,able:e0_able
   ,compare:cmp
   ,FS:e0_FS
   ,init:()=>([
      {expr:Infinity,low:[0],subitems:[]}
      ,{expr:0,low:[0],subitems:[]}
   ])
})
})()