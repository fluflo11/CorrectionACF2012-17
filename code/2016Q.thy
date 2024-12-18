theory "2016Q"
imports Main
begin 


(* Exercice 1*)

lemma q1:"( ∃ x. P(x)) ⟶ (∀ x. P(x))"
  nitpick [card=1]

  nitpick [card=2]

  sorry

(*Exercice 2 *)

type_synonym ('a,'b) map= "('a * 'b) list"

datatype 'a option  = Some 'a | None (*utile pour la fonction get *)

fun get ::" 'a ⇒ ('a,'b) map ⇒ 'b option "
  where
"get a [] = None"| (*Pas d'indication donc on ne renvoit rien *)
"get a ((a2,b)#xs) = (if a = a2 then (Some b) else (get a xs))" 

fun remove:: " 'a ⇒  ('a,'b) map ⇒ ('a,'b) map"
  where
"remove a [] = []" |
"remove a ((a2,b)#xs) = (if a =  a2 then xs else (a2,b)#(remove a xs))"

fun modify :: "'a ⇒ 'b ⇒ ('a,'b) map ⇒ ('a,'b) map"
  where
"modify a b [] = [(a, b)]" |    
"modify a b ((a2,c)#xs) = (if a = a2 then (a,b)#xs  else (a2,c)#(modify a b xs))"

(*2.a*)
lemma carons: "∀ k t. ¬ List.member  (map fst (remove k t)) k"
  oops

(*2.b*)
lemma rtinique: "∀ k t a b. List.member (remove k t)  (a, b) ⟷ (List.member t  (a, b)  ∧ a ≠ k)"
  oops


(*2.c*)
lemma racas0 :"∀ k t. ∃v. List.member (map fst(modify k v t)) k"
  oops

(*2.d*)
lemma tome: "∀k t v a b. List.member (modify k v t) (a, b) ⟷ (List.member t (a, b) ∧ a ≠ k)"
  oops

end