(*天际线问题，描述建筑物的轮廓，类扫描线法解决*)
val N = getInt();
fun readin _ = 
let val l = getInt() and h = getInt() and r = getInt()
in (l,h,r) end;
val data = List.tabulate(N,readin);

(*sort是根据f要求的排序函数*)
fun sort f [] = []
|sort f (x::xs:(int*int*int) list) = let
val (x1,x2) = List.partition (fn a=>f(a,x)) xs;
in (sort f x1)@[x]@(sort f x2) end;

val sorta = sort (fn(x,y)=> # 2 x < # 2 y) data;(*sorta将原数据根据高度从小到大排序*)
val sorhei = Array.fromList(map (fn(a,b,c)=>b) sorta);(*sorhei是排序好的高度序列*)
val (_,aa) = List.foldr (fn((a,b,c),(i,ans))=> (i-1,(a,i,c)::ans)) (N-1,[]) sorta;
(*aa:将sorta高度换成序号，从0开始，即0对应最低的楼*)
val aa1 = List.foldr (fn((a,i,c),ans) => (a,i,1)::(c,i,0)::ans) [] aa;
(*aa1:将aa拆分，左边界为1，右边界为0*)
val aa2 = rev aa;
(*aa2:逆转aa*)
val borda = sort (fn(x,y)=> # 1 x < # 1 y) aa1;
(*对所有边界/aa1的从小到大的排序*)
val m = Array.array(1,~1);
(*m相当于自由变量，m是当前扫描的高度序号*)

fun cacu(a,b,c) = 
(*左边界的判断*)
if c = 1 then if Array.sub(m,0) < b andalso if b > 0 then Array.sub(sorhei,b) <> Array.sub(sorhei,b - 1) else true
(*后面的andalso一串也是为了考虑高度相等的情况*) 
then let val t1 = printInt(a) and t2 = printInt(Array.sub(sorhei,b)) and t3 = print("\n");
val t4 = Array.update(m,0,b); in () end else ()
(*右边界的判断，如果m=b，就要找到与右边界相交的最高的那一个点*)
else if Array.sub(m,0) = b then
let val t1 = List.find (fn(a1,b1,c1)=> b1 < b andalso a1 <= a andalso c1 > a) aa2;
(*t1就是寻找和右边界相交的点*)
val t11 = List.find (fn(a1,b1,c1)=> Array.sub(sorhei,b1) = Array.sub(sorhei,b) andalso a1 <= a andalso c1 > a) aa2;
(*t11用于判断高度是否有平行的情况*)
in if t11 <> NONE then let val (_,b3,_) = Option.valOf t11
val tmp = Array.update(m,0,b3) in () end else(*如果出现高度平行，则不做处理*) 
if t1 = NONE then let val t2 = printInt(a) and t3 = printInt(0) and t4 = print("\n")
val t5 = Array.update(m,0,~1) in () end
else let val (_,b2,_) = Option.valOf t1(*否则输出t1中找到的值*) 
val t6 = printInt(a) and t7 = printInt(Array.sub(sorhei,b2)) and t8 = print("\n")
val t9 = Array.update(m,0,b2) in () end end else ();

List.app cacu borda;