theory Temp_Theory
  imports "RG_Translate"
begin

text \<open> A temporary theory to show the basic steps for translation \<close>

ML_file \<open>utils.ML\<close>

section \<open> The structure of a basic term \<close>
ML \<open>
val x = Free("x", dummyT)
val _ = RG_Debug.print_term @{context} x
\<close>

section \<open> How to bind terms into lambda functions \<close>
ML \<open>
val x = Bound(0)
val lambda = Abs("x", dummyT, x)
val _ = RG_Debug.print_term @{context} x
val _ = RG_Debug.print_term @{context} lambda
\<close>

section \<open> The structure of a tuple \<close>
ML \<open>
val tup = @{term "(x, y)"}
\<close>

section \<open> The structure of a pair of tuples \<close>
ML \<open>
val tup_pair = @{term "((x, y), (x', y'))"}
\<close>

section \<open> The structure of a set comprehension of pairs of tuples \<close>
ML \<open>
val set_comp = @{term "{((x, y), (x', y')). x}"}
\<close>

section \<open> Example usage of the translation framework \<close>

text \<open> Set up the variables present in the program state \<close>
setup \<open>
  RG_Var_List.add (@{term "x"}) #>
  RG_Var_List.add (@{term "y"})
\<close>

lemma "\<lrel> x > x' \<rrel> = {((x,y), (x',y')). x > x'}"
  by (rule refl)

text \<open> Clear the variables afterward to avoid affecting other theories \<close>
setup \<open>
  RG_Var_List.reset
\<close>

end

