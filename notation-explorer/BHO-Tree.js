;
var is_zero=(a)=>{
	if(!(a instanceof Array))return 0
	return a.length==0
}
var is_lim = (a)=>{
	if(a===Infinity)return 1
	if(!(a instanceof Array))return 0
    if(is_zero(a))return 0
	let xy = a[a.length-1]
	let x = xy[0]
	let y = xy[1]
	return is_lim(y) || !is_zero(x)
}
let BHO_tree_display=(a)=>{
	if(!(a instanceof Array))return ''+a
	if(is_zero(a))return ''
	return a.map(xy=>{
		return '('+xy.map(BHO_tree_display).join(',')+')'
	}).join('')
}
let BHO_tree_simpl=(a)=>{
	if(!(a instanceof Array))return a
    if(is_zero(a))return 0
    let a1 = []
    for(let i=0;i<a.length;++i)a1.push([BHO_tree_simpl(a[i][0]),BHO_tree_simpl(a[i][1])])
    if(a1.length==1){
		let x=a1[0][0]
		let y=a1[0][1]
		if(x==0 && y==y+0)return y+1
	}
    return a1
}
var tree_compare=(m1,m2)=>{
	if(m1===Infinity){
		if(m2===Infinity)return 0
		return 1
	}else if(m2===Infinity){
		return -1
	}
	if(m1[0]==-1){
		if(m2[0]==-1)return tree_compare(m1[1],m2[1])
		let s=tree_compare(m1,m2[0])
		return s==0?-1:s
	}else if(m2[0]==-1){
		let s=tree_compare(m1[0],m2)
		return s==0?1:s
	}
	for(let i=0;i<Math.min(m1.length,m2.length);++i){
		let x=tree_compare(m1[i],m2[i])
		if(x!=0)return x
	}
	if(m1.length<m2.length)return -1
	if(m1.length>m2.length)return +1
	return 0
}
let BHO_FS=(()=>{
  let at = (a,n,a0)=>{
	if(a===Infinity)return n==0 ? [] : [[at(a,n-1),[]]]
	if(is_zero(a))return a
	let xy = a[a.length-1]
	//if(xy.length!=2)throw Exception()
	let x = xy[0]
	let y = xy[1]
	let x0 = ()=>at(x,n,a0)
	let y0 = ()=>at(y,n,y)
	let rec= ()=>(n==0 ? [] : at(a0,n-1,a0))
	let a1 = []
	for(let i=0;i<a.length-1;++i)a1.push(a[i])
	 //console.log('at1: '+BHO_tree_display(a)+'; '+n+';'+BHO_tree_display(a0)+' = '+BHO_tree_display(a1)+' x='+BHO_tree_display(x)+' y='+BHO_tree_display(y))
	if(is_lim(y))a1.push([x,y0()]) //#[...(x ,y_)] => [...(x,y[n])] (a is Lim)
	else if(!is_zero(y)){
		if(is_zero(x))a1.push([x,y0()]) //[...(0 ,y+)] => [...(0,y)] (a is Suc)
		else if(is_lim(x)){
			a1.push([x,y0()])
			a1.push([x0(),[]]) //[...(x_,y+)] => [...(x_,y)(x[n],0)] (a is Lim)
		}else{
			a1.push([x,y0()])
			a1.push([x0(),rec()]) //[...(x+,y+)] => [...(x+,y)(x,_REC_)] (a is Lim)
		}
	}else{
		if(is_lim(x))a1.push([x0(),[]]) //[...(x_,0 )] => [...(x[n],0)] (a is Lim)
		else if(!is_zero(x))a1.push([x0(),rec()])  //[...(x+,0 )] => [...(x,_REC_)] (a is Lim)
	}
	 //console.log('at2: '+BHO_tree_display(a)+'; '+n+';'+BHO_tree_display(a0)+' = '+BHO_tree_display(a1)+' x='+BHO_tree_display(x)+' y='+BHO_tree_display(y))
	return a1
  }
  return (m,FSterm)=>{
	 //if(FSterm>10)throw Exception()
	 //console.log('FS: '+BHO_tree_display(m)+'; '+FSterm)
	 if(is_lim(m))return at(m,FSterm,m)
	 return []
  }
})()
let BHO_tree_display_expr=(a)=>{
	if(!(a instanceof Array))return ''+a
	let rec=(a)=>{
		if(is_zero(a))return '()'
		return '('+a.map(xy=>{
			let xy_=xy.map(rec)
			return 'Ω^'+xy_[0]+'×ψ'+xy_[1]+''
		}).join('+')+')'
	}
	return 'ψ'+rec(a)
}
register.push({
   id:'BHO_Tree'
   ,name:'BHO Tree'
   ,display:a=>BHO_tree_display(BHO_tree_simpl(a))
   ,able:is_lim
   ,compare:tree_compare
   ,FS:BHO_FS
   ,init:()=>([
      {expr:Infinity,low:[[]],subitems:[]}
      ,{expr:[],low:[[]],subitems:[]}
   ])
})
register.push({
   id:'BHO_Tree_Raw'
   ,name:'BHO Tree (Raw)'
   ,display:BHO_tree_display
   ,able:is_lim
   ,compare:tree_compare
   ,FS:BHO_FS
   ,init:()=>([
      {expr:Infinity,low:[[]],subitems:[]}
      ,{expr:[],low:[[]],subitems:[]}
   ])
})
register.push({
   id:'BHO_Tree_Expr'
   ,name:'BHO Tree (Ω^a×ψ(b)+c)'
   ,display:BHO_tree_display_expr
   ,able:is_lim
   ,compare:tree_compare
   ,FS:BHO_FS
   ,init:()=>([
      {expr:Infinity,low:[[]],subitems:[]}
      ,{expr:[],low:[[]],subitems:[]}
   ])
})

let e0_is_lim=(a)=>{
	if(a===Infinity)return 1
	return a.length>0 && a[a.length-1].length>0
}
let e0_FS=(a,n)=>{
	if(a==Infinity)return n==0?[]:[e0_FS(a,n-1)]
	let a1 = []
	for(let i=0;i<a.length-1;++i)a1.push(a[i])
	let x = a[a.length-1]
	let x0 = ()=>e0_FS(x,n)
	if(e0_is_lim(x))a1.push(x0())
	else if(x.length>0){
		for(let i=0;i<n;++i)a1.push(x0())
	}
	return a1
}
let e0_tree_display=(a)=>{
	if(!(a instanceof Array))return ''+a
	return '('+a.map(e0_tree_display).join('')+')'
}
register.push({
   id:'e0_Tree'
   ,name:'ε0 Tree'
   ,display:e0_tree_display
   ,able:e0_is_lim
   ,compare:tree_compare
   ,FS:e0_FS
   ,init:()=>([
      {expr:Infinity,low:[[]],subitems:[]}
      ,{expr:[],low:[[]],subitems:[]}
   ])
})
let e0_wapb_display=(a)=>{
	if(!(a instanceof Array))return ''+a
	if(a.length==0)return '0'
	let s=a.map(x=>'ω^'+e0_wapb_display(x)).join('+')
	if(a.length>1)s='('+s+')'
	return s
}
register.push({
   id:'e0_Tree_expr'
   ,name:'ε0 Tree (ω^a+b)'
   ,display:e0_wapb_display
   ,able:e0_is_lim
   ,compare:tree_compare
   ,FS:e0_FS
   ,init:()=>([
      {expr:Infinity,low:[[]],subitems:[]}
      ,{expr:[],low:[[]],subitems:[]}
   ])
})