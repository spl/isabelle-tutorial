(* Sections 2.1 through 2.3 *)
theory AToyList
imports Datatype
begin

datatype 'a list = Nil ("[]") | Cons 'a "'a list" (infixr "#" 65)

(* append one list to another *)
primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65) where
"([] @ ys)     = ys" |
"(x # xs) @ ys = x # xs @ ys"

(* reverse a list *)
primrec rev :: "'a list \<Rightarrow> 'a list" where
"rev []       = []" |
"rev (x # xs) = rev xs @ x # []"

lemma app_Nil2 [simp]: "xs @ [] = xs"
apply (induct_tac xs)
apply auto
done

lemma app_assoc [simp]: "(xs @ yz) @ zs = xs @ (yz @ zs)"
apply (induct_tac xs)
apply auto
done

lemma rev_app [simp]: "rev (xs @ ys) = rev ys @ rev xs"
apply (induct_tac xs)
apply auto
done

theorem rev_rev [simp]: "rev (rev xs) = xs"
apply (induct_tac xs)
apply auto
done

end
