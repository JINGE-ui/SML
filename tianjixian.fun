val N = getInt();
fun readin _ = 
let val l = getInt() and h = getInt() and r = getInt()
in (l,h,r) end;
val data = List.tabulate(N,readin);
fun sort f [] = []
|sort f (x::xs:(int*int*int) list) = let
val (x1,x2) = List.partition (fn a=>f(a,x)) xs;
in (sort f x1)@[x]@(sort f x2) end;
val sorta = sort (fn(x,y)=> # 2 x < # 2 y) data;
val sorhei = Array.fromList(map (fn(a,b,c)=>b) sorta);
val (_,aa) = List.foldr (fn((a,b,c),(i,ans))=> (i-1,(a,i,c)::ans)) (N-1,[]) sorta;
val aa1 = List.foldr (fn((a,i,c),ans) => (a,i,1)::(c,i,0)::ans) [] aa;
val aa2 = rev aa;
val borda = sort (fn(x,y)=> # 1 x < # 1 y) aa1;
val m = Array.array(1,~1);

fun cacu(a,b,c) = 
if c = 1 then if Array.sub(m,0) < b andalso if b > 0 then Array.sub(sorhei,b) <> Array.sub(sorhei,b - 1) else true then 
let val t1 = printInt(a) and t2 = printInt(Array.sub(sorhei,b)) and t3 = print("\n");
val t4 = Array.update(m,0,b); in () end else ()
else if Array.sub(m,0) = b then
let val t1 = List.find (fn(a1,b1,c1)=> b1 < b andalso a1 <= a andalso c1 > a) aa2;
val t11 = List.find (fn(a1,b1,c1)=> Array.sub(sorhei,b1) = Array.sub(sorhei,b) andalso a1 <= a andalso c1 > a) aa2;
in if t11 <> NONE then let val (_,b3,_) = Option.valOf t11
val tmp = Array.update(m,0,b3) in () end else 
if t1 = NONE then let val t2 = printInt(a) and t3 = printInt(0) and t4 = print("\n")
val t5 = Array.update(m,0,~1) in () end
else let val (_,b2,_) = Option.valOf t1
val t6 = printInt(a) and t7 = printInt(Array.sub(sorhei,b2)) and t8 = print("\n")
val t9 = Array.update(m,0,b2) in () end end else ();

List.app cacu borda;