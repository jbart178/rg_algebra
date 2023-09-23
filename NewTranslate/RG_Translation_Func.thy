theory RG_Translation_Func
  imports Main "HOL-Statespace.StateSpaceLocale" "HOL-Statespace.StateSpaceSyntax"
begin
ML_file utils.ML

ML \<open>
signature RG_VAR_LIST =
sig
  val get: theory -> term list
  val add: term -> theory -> theory
  val reset: theory -> theory
end;

structure RG_Var_List: RG_VAR_LIST =
struct

structure Data = Theory_Data
(
  type T = term list;
  val empty = [];
  val extend = I;
  val merge = Library.merge (op aconv);
);

val get = Data.get;

fun add t thy = Data.map (cons (Sign.cert_term thy t)) thy

val reset = Data.put [];

end;
\<close>

ML \<open>
fun list_free_vars trm =
  let
    fun list_free_vars_helper trm names = 
      case trm of 
          x $ Free("<markup>", _) => list_free_vars_helper x names 
        | (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ u $ _) => list_free_vars_helper u names
        | (Const (\<^syntax_const>\<open>_constrainAbs\<close>, _) $ u $ _) =>  list_free_vars_helper u names
        | u $ u' =>
          let 
            val (lhs, names') = list_free_vars_helper u names 
            val (rhs, names'') = list_free_vars_helper u' names
            (*val _ = @{print} {lhs=lhs, rhs=rhs}*)
          in (lhs $ rhs, List.concat [names', names'']) end
        | Free(s, t) =>
          let
            (*val _ = @{print} trm*)
            val ignore_pattern = "_ig"
            val should_ignore = if String.isSuffix ignore_pattern s then true else false
            val trimmed_name = 
              if String.isSuffix ignore_pattern s then 
                String.substring(s, 0, (String.size s) - (String.size ignore_pattern)) 
              else s;
            val is_prime = if String.isSuffix "'" trimmed_name then true else false
          in
            if should_ignore then (Free(trimmed_name,t), names)
            else if s = "<markup>" then (Free(trimmed_name,t), names)
            else if is_prime then
              let
                (* Remove the ' from the name and wrap it *)
                val updated_name = String.substring(trimmed_name, 0, (String.size trimmed_name) - 1);
              in 
                (Free(updated_name, t), updated_name :: names)
              end
            else 
              (Free(trimmed_name, t), trimmed_name :: names)
          end
      | Abs(s, t, u) => 
          let
            val (res, names') = list_free_vars_helper u names
          in (Abs(s, t, res), names') end
      | _ => (trm, names)
  in list_free_vars_helper trm [] end
\<close>

ML \<open>
fun make_record ts names = let
  
  val result = nil
in result end
\<close>

ML \<open>  
fun rgrelation_tr ctxt ts = let
  val trm = hd ts
  val var_list = list_free_vars trm
  
  val record = make_record var_list
in trm
end
\<close>

statespace vars = x :: nat
ML \<open>
val _ = @{print} X
\<close>

lemma(in vars) "s<x:=2>\<cdot>x == 2"
  by simp

syntax  "_rgrelation" :: "args => 'a set"
        "_surr" :: "args \<Rightarrow> 'a set"  ("\<lrel>_\<rrel>")

translations "\<lrel>b\<rrel>" \<rightharpoonup> "CONST Collect (s,s') where "

record generic = _ :: bool

function make_states :: "'a list \<Rightarrow> generic set" where
  make_states ts = 
| make_states [t] = generic + \<lparr> t :: 

parse_translation \<open>[(@{syntax_const "_rgrelation"}, rgrelation_tr)]\<close>

lemma "\<lrel> x < x' \<rrel> = {(x, x'). x < x'}"
  by (rule refl)

end