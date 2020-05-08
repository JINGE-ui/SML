(*实现任意精度的大整数的加、减、乘的运算*)
(*允许使用lietsequence和arraysequence结构*)
val list1 = getIntTable(getInt());
val list2 = getIntTable(getInt());

list1 :[1,2,3,4];
list2 :[1,2];

fun myzip(a:int list,b:int list):(int*int) list=
rev(ListPair.zip(a,List.tabulate(length(a)-length(b),fn x=> 0)@b));


fun plus(x::xs : (int*int) list,c:int) =
((# 1 x + # 2 x + c) mod 10)::plus(xs,(# 1 x + # 2 x + c) div 10)
|plus([],c) = if(c=0) then [] else 1::[];
(*需要反转一次*)
(*plus结果输出为rev plus(myzip(a,b),0)*)

(*下面的减法假定a>b,也即length a >length b*)
fun mirus(x::xs : (int*int) list,c:int) =
if(# 1 x - # 2 x - c >= 0) then (# 1 x - # 2 x - c)::mirus(xs,0)
else (# 1 x + 10 - # 2 x - c)::mirus(xs,1)
|mirus([],_)=[];
(*need a rev*)

(*rev list1:4 3 2 1   rev list2:2 1*)
fun multi(a:int array,b:int array,i:int,j:int,c:int,arr:int array) = 
if j=Array.length(b) then 
    if c=0 then multi(a,b,i+1,0,0,arr)
    else let val tmp2 = Array.update(arr,i+Array.length(b)-1,c)
    in multi(a,b,i+1,0,0,arr)  end
else if i=Array.length(a) then ()
else let
    val tmp = Array.update(arr,i+j,(Array.sub(arr,i+j) + Array.sub(a,i) * Array.sub(b,j) + c) mod 10)
    val c = Array.sub(arr,i+j) div 10
in
    multi(a,b,i,j+1,c,arr)
end;

fun arraytolist (arr:int array,i:int,list:int list,maxn:int) =
if i >=  maxn andalso Array.sub(arr,i)=0 then list
else arraytolist(arr,i+1,Array.sub(arr,i)::list,maxn);

(**)
(*有一个测试集总是WA，问题似乎出在pri函数上*)
fun clear0 []  = []
|clear0 l = if hd l = 0 then clear0 (tl l) else l;
val n1 = getInt();
val a = Array.fromList(clear0 (getIntTable(n1)));
val N1 = Array.length a;
val n2 = getInt();
val list = clear0 (getIntTable(n2));
val N2 = List.length list;
val b = Array.fromList(List.tabulate(N1-N2,fn x=> 0)@list);
val arrp = Array.array(N1+1,0);
fun plus(~1,0) = ()
|plus (~1,1) =
let 
    val tmp = Array.update(arrp,0,1)
in
    plus(~1,0)
end 
|plus (i:int,c:int) =
let 
    val tmp = Array.update(arrp,i+1,(Array.sub(a,i)+Array.sub(b,i)+c) mod 10)
in
    plus (i-1,(Array.sub(a,i)+Array.sub(b,i)+c) div 10)
end; 
plus(N1-1,0);
val arrmi = Array.array(N1,0);
fun mirus(~1,c) = ()
|mirus(i,c) = 
let
    val x = Array.sub(a,i)-Array.sub(b,i)-c
in  if(x >= 0) then let val tmp1 = Array.update(arrmi,i,x) in mirus(i-1,0) end
else let val tmp2 = Array.update(arrmi,i,10 + x) in mirus(i-1,1) end 
end;
mirus(N1-1,0);

val arrmu = Array.array(2 * N1,0);
fun cacumulti(maxn:int) = 
let
fun multi(i,~1,0) = multi(i-1,maxn,0)
|multi(i,~1,c) = 
let val tmp2 = Array.update(arrmu,i,c)
in multi(i-1,maxn,0)  end
|multi(~1,j,c) = ()
|multi(i:int,j:int,c:int) = 
let val x = Array.sub(arrmu,i+j+1) + Array.sub(a,i) * Array.sub(b,j) + c  
    val tmp = Array.update(arrmu,i+j+1,x mod 10) 
in multi(i,j-1,x div 10)  end
in
multi(maxn,maxn,0)
end;
cacumulti(N1-1);

fun pri(a:int array,i:int,vis:int) = 
if i = Array.length(a) then ()
else if Array.sub(a,i)=0 andalso i<>Array.length(a)-1 andalso vis = 1 then pri(a,i+1,1)
else let val tmp = printInt(Array.sub(a,i))
in pri(a,i+1,0) end;

pri(arrp,0,1);
print("\n");
pri(arrmi,0,1);
print("\n");
pri(arrmu,0,1);


(*********************************************************以下是正式的程序**)
fun clear0 []  = []
|clear0 l = if hd l = 0 then clear0 (tl l) else l;
val n1 = getInt();
val a = Array.fromList(clear0(getIntTable(n1)));
val N1 = Array.length a;
val n2 = getInt();
val list = clear0(getIntTable(n2));
val b = Array.fromList(List.tabulate(N1 - List.length(list),fn x=>0)@list);
val arr = Array.tabulate(N1,fn x=>x);

val arr1 = Array.array(N1+1,0);
val c = Array.foldr (fn (i,c)=> let val tmp = Array.update(arr1,i+1,(Array.sub(a,i)+Array.sub(b,i)+c) mod 10) in 
    (Array.sub(a,i)+Array.sub(b,i)+c)div 10 end) 0 arr;  
Array.update(arr1,0,c);
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr1 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1 then 1 else let val tmp = printInt(x) in 0 end) 
1 arr1;
print("\n");

val arr2 = Array.array(N1,0);
Array.foldr (fn (i,c)=> if Array.sub(a,i)-Array.sub(b,i)-c >= 0 then 
let val t1 = Array.update(arr2,i,Array.sub(a,i)-Array.sub(b,i)-c) in 0 end
else let val t2 = Array.update(arr2,i,Array.sub(a,i)-Array.sub(b,i)-c+10) in 1 end )
0 arr;
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr2 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1
then 1 else let val tmp = printInt(x) in 0 end) 
1 arr2;
print("\n");

val arr3 = Array.array(2*N1,0);
fun mul1 (j,_) = let
val c = Array.foldri (fn(i,x,c)=> let val d = Array.sub(arr3,i+j+1) + x * Array.sub(b,j) + c 
val tmp = Array.update(arr3,i+j+1,d mod 10) in d div 10 end) 0 a;
val tmp1 = Array.update(arr3,j,c);
in 0 end;
(*对b内的从低到高位，用a的所有位数做运算*)
Array.foldr (mul1) 0 arr;
if Array.foldl (fn (x,max)=>Int.max(x,max)) 0 arr3 = 0 
then let val t1 = printInt(0) in 0 end else
Array.foldli (fn (i,x,vis)=>if x = 0 andalso vis = 1 andalso i <> Array.length(arr3) - 1 
then 1 else let val tmp = printInt(x) in 0 end) 
1 arr3;