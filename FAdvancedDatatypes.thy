(* Section 3.4 Advanced Datatypes *)

theory FAdvancedDatatypes
imports Main
begin

(* Section 3.4.1 Mutual Recursion *)

(* Mutually recursive data types *)
datatype 'a aexp = IF "'a bexp" "'a aexp" "'a aexp"
                 | Sum "'a aexp" "'a aexp"
                 | Diff "'a aexp" "'a aexp"
                 | Var 'a
                 | Num nat
and      'a bexp = Less "'a aexp" "'a aexp"
                 | And "'a bexp" "'a bexp"
                 | Neg "'a bexp"

(* Mutually recursive data types have mutually recursive primitive recursion functions. *)

(* Evaluation *)
primrec evala :: "'a aexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat" and
        evalb :: "'a bexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
"evala (IF b a1 a2) env = (if evalb b env then evala a1 env else evala a2 env)" |
"evala (Sum a1 a2)  env = (evala a1 env + evala a2 env)" |
"evala (Diff a1 a2) env = (evala a1 env - evala a2 env)" |
"evala (Var v)      env = env v" |
"evala (Num n)      env = n" |

"evalb (Less a1 a2) env = (evala a1 env < evala a2 env)" |
"evalb (And b1 b2)  env = (evalb b1 env \<and> evalb b2 env)" |
"evalb (Neg b)      env = (\<not> evalb b env)"

(* Substitution *)
primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp" and
        substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp" where
"substa s (IF b a1 a2) =  IF (substb s b) (substa s a1) (substa s a2)" |
"substa s (Sum a1 a2)  = Sum (substa s a1) (substa s a2)" |
"substa s (Diff a1 a2) = Diff (substa s a1) (substa s a2)" |
"substa s (Var v)      = s v" |
"substa s (Num n)      = Num n" |

"substb s (Less a1 a2) = Less (substa s a1) (substa s a2)" |
"substb s (And b1 b2)  = And (substb s b1) (substb s b2)" |
"substb s (Neg b)      = Neg (substb s b)"

lemma "evala (substa s a) env = evala a (\<lambda>x. evala (s x) env) \<and>
       evalb (substb s b) env = evalb b (\<lambda>x. evala (s x) env)"
apply (induct_tac a and b)
apply simp_all
done

(* Exercise 3.4.1 *)

(*
Normalize IF with Less and without And and Neg.
Note the primitive recursion requirements for norma and normif.
*)
primrec norma  :: "'a aexp \<Rightarrow> 'a aexp" and
        normif :: "'a bexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp" where
"norma (IF b a1 a2) = normif b (norma a1) (norma a2)" |
"norma (Sum a1 a2)  = Sum (norma a1) (norma a2)" |
"norma (Diff a1 a2) = Diff (norma a1) (norma a2)" |
"norma (Var v)      = Var v" |
"norma (Num n)      = Num n" |

"normif (Less a1 a2) a1' a2' = IF (Less (norma a1) (norma a2)) a1' a2'" |
"normif (And b1 b2)  a1' a2' = normif b1 (normif b2 a1' a2') a2'" |
"normif (Neg b)      a1' a2' = normif b a2' a1'"

(*
The value of a normalized IF is the same as that of a non-normalized IF.
Note that the quantification cannot be lifted.
*)
theorem "evala (norma a) env = evala a env \<and>
         (\<forall>a1 a2. evala (normif b a1 a2) env = evala (IF b a1 a2) env)"
apply (induct_tac a and b)
apply auto
done

primrec normala :: "'a aexp \<Rightarrow> bool" and
        normalb :: "'a bexp \<Rightarrow> bool" where
"normala (IF b a1 a2) = (normalb b \<and> normala a1 \<and> normala a2)" |
"normala (Sum a1 a2)  = (normala a1 \<and> normala a2)" |
"normala (Diff a1 a2) = (normala a1 \<and> normala a2)" |
"normala (Var _)      = True" |
"normala (Num _)      = True" |

"normalb (Less a1 a2) = (normala a1 \<and> normala a2)" |
"normalb (And _ _)    = False" |
"normalb (Neg _)      = False"

(* normif normalizes the condition but not the branches. *)
theorem "normala (norma (a :: 'a aexp)) \<and>
         (\<forall>a1 a2. normala (normif (b :: 'a bexp) a1 a2) = (normala a1 \<and> normala a2))"
apply (induct_tac a and b)
apply auto
done
