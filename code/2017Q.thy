theory "2017Q"
imports Main
begin

(*exercice 1*)

(*Q1*)
type_synonym email= "char list* char list* char list"
datatype test = dest "char list"  | exp "char list" | sujet "char list"
datatype requete =  Test test | Neg requete |Et requete requete | Ou requete requete


(*Q2*)

lemma a :"length l = (let (la,lb) = filtrer r l in length la + length lb)"
  oops
lemma b :"length l = (let (la,lb) = filtrer r l in length la + length lb)" (*même lemme car on compare la taille*)
  oops

lemma c: "\<forall>e el.
      ((List.member (hd (filtrer r el)) e) \<longrightarrow> (\<not>List.member (hd (tl (filtrer r el))) e)
    \<and> (\<not>List.member (hd (filtrer r el)) e) \<longrightarrow> (List.member (hd (tl (filtrer r el))) e))"
  oops 

lemma d:"\<forall>r. (let(l1,l2) = filtrer r el in filtrer (Neg r) el = (l2,l1)) " 
  oops

(*On vérifie si l1 et l2 sont bien des sous séquences de el*)
lemma e:"\<forall>r el. let(l1,l2) = filtrer r el in (subsequence l1 el \<and> subsequence l2 el)"
  oops

(*Question 3*)
fun evaluate::"requete \<Rightarrow> email \<Rightarrow>bool"
  where
"evaluate (Test (dest d)) (x,_,_) = (d=x)"|
"evaluate (Test (exp e)) (_,x,_) = (e=x)"|
"evaluate (Test (sujet s)) (_,_,x) = (s=x)"|
"evaluate (Neg x) y = ( \<not>(evaluate x y))"|
"evaluate (Et x1 x2) y = ((evaluate x1 y)\<and> (evaluate x2 y))"|
"evaluate (Ou x1 x2) y = ((evaluate x1 y) \<or> (evaluate x2 y))"

fun filtrer::"requete \<Rightarrow> email list \<Rightarrow> (email list * email list)"
  where
"filtrer _ [] = ([],[])"|
"filtrer r (x#xs) = 
    (let (la,lb) = filtrer r xs in
      (if(evaluate r x) then (x#la,lb) else (la,x#lb))
)"

(*exercice 2*)

fun f :: "'a list \<Rightarrow> bool"
where
"f [] = True" |
"f (x#y#z) = f (y#z)"

value "f [a,b]" 


(*Exercice 3*)

datatype expression = Const int | Add expression expression

datatype color = Red | Blue | Green


(*Exercice 4*)

lemma "g (l1 @ l2) = g (l2 @ l1)"
  nitpick
  oops

end
