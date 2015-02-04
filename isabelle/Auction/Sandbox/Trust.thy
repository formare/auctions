theory Trust

imports
(* "/apps/afp/thys/Lazy-Lists-II/LList2" *)
(* "~/afp/Coinductive/Coinductive_List" *)
Predicate
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Target_Numeral"
(* "~~/src/HOL/Library/Code_Binary_Nat" *)
"~~/src/HOL/Library/Code_Numeral"
"~~/src/HOL/Library/Code_Char"
String

begin

inductive rtrancl' :: "'a => 'a => ('a => 'a => bool) => bool" 
where
  "rtrancl' x x r"
| "r x y ==> rtrancl' y z r ==> rtrancl' x z r"
(*
inductive prova :: "(nat => bool) => nat => bool" 
where
  "prova f 0" | 
  "f n ==> prova f (Suc n)"

term "prova ((P::((nat => nat) => bool)) \<circ> f)"
*)
lemma "Predicate.eval (Predicate.Seq f) = Predicate.member (f ())" 
by (metis eval_code)

fun g where
"g f [] = []"|
"g f (x#xs) = (f x) # xs"

term"removeAll"
term "integer_of_char"
term "a::(String.literal)"
find_consts "string => String.literal"
(*
definition trusted where "trusted (output::(String.literal => _)) (input::(integer  => _)) = 
(output (String.implode ''zio''), input 0)"
*)

fun toListWithCondition where 
"toListWithCondition P f 0 = [f 0]"|
"toListWithCondition P f (Suc n) = (if (P ((f (Suc n))#toListWithCondition P f n))
then
(f (Suc n))#toListWithCondition P f n else [])"
value "toListWithCondition (%l. listsum l < 13) id 4"

fun test where 
"test f 0 = ((f 0) \<noteq> f 1)"|
"test f (Suc n)=(if n > 3 then (f n=f n) else False)"


(* definition "prova f={f n| n. n<2}" *)
term "Predicate.eval P \<le> Predicate.eval Q"
definition trusted where "trusted (output::(String.literal => _)) (input::(integer => String.literal)) = 
range input"

definition "prova (input::(integer => String.literal)) = (inf_llist (input \<circ> integer_of_nat))"

export_code prova trusted in Scala module_name a file "/dev/shm/a.scala"

end

